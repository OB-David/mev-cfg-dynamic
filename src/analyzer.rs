use crate::blockchain::{BlockchainService, BytecodeCache};
use crate::cfg_gen::{
    cfg_graph::{CFGRunner, Edges},
    dasm::{self, InstructionBlock},
    trace::{self, CallEdge, TraceStep},
};
use eyre::{eyre, Result};
use ethers::types::{H160, Bytes};
use fnv::FnvBuildHasher;
use petgraph::{
    graph::DiGraph,
    visit::{EdgeRef}
};
use revm::{
    primitives::{Bytecode as RevmBytecode},
    interpreter::analysis::to_analysed,
};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt::Write;
use std::path::Path;

/// Represents a contract's control flow graph and execution information
pub struct ContractCFG {
    pub address: H160,
    pub cfg_runner: CFGRunner<'static>,
    pub executed_pcs: HashSet<u16>,
    // 新增：用于存储边的编号
    pub edge_numbering: HashMap<((u16, u16), (u16, u16), Edges), u32>,
}

/// Node in the global transaction graph
#[derive(Clone, Debug)]
pub struct TransactionNode {
    pub contract_address: H160,
    pub pc: u16,
    pub instruction: String,
    pub contains_sstore: bool,  // Marks whether it contains SSTORE opcode
    pub contains_add_or_sub: bool, // Marks whether it contains ADD or SUB opcodes
}

impl Default for TransactionNode {
    fn default() -> Self {
        Self {
            contract_address: H160::zero(),
            pc: 0,
            instruction: String::new(),
            contains_sstore: false,
            contains_add_or_sub: false,
        }
    }
}

/// Edge in the global transaction graph
#[derive(Clone, Debug)]
pub enum TransactionEdge {
    Internal(String),    // Internal contract flow, string represents edge type
    External(String),    // Cross-contract call, string represents call type (CALL, DELEGATECALL, etc.)
}

pub struct TransactionAnalyzer {
    pub trace_steps: Vec<TraceStep>,
    pub contract_addresses: HashSet<H160>,
    pub bytecode_cache: BytecodeCache,
    pub contract_cfgs: HashMap<H160, ContractCFG>,
    pub call_edges: Vec<CallEdge>,
    pub global_graph: DiGraph<TransactionNode, TransactionEdge>,
    pub node_mapping: HashMap<(H160, u16), petgraph::graph::NodeIndex>,
}

impl TransactionAnalyzer {
    pub fn new(trace_steps: Vec<TraceStep>) -> Self {
        let contract_addresses = trace::extract_contract_addresses(&trace_steps);
        let call_edges = trace::extract_call_edges(&trace_steps);
        
        Self {
            trace_steps,
            contract_addresses,
            bytecode_cache: BytecodeCache::new(),
            contract_cfgs: HashMap::new(),
            call_edges,
            global_graph: DiGraph::new(),
            node_mapping: HashMap::new(),
        }
    }
    
    pub fn from_trace_file(trace_path: &str) -> Result<Self> {
        let trace_steps = trace::parse_trace_file(trace_path)?;
        Ok(Self::new(trace_steps))
    }
    
    pub async fn fetch_bytecodes(&mut self, blockchain_service: &impl BlockchainService) -> Result<()> {
        let addresses: Vec<H160> = self.contract_addresses.iter().cloned().collect();
        self.bytecode_cache = crate::blockchain::fetch_all_bytecodes(&addresses, blockchain_service).await?;
        Ok(())
    }
    
    /// Generate CFG for each contract
    pub fn generate_contract_cfgs(&mut self) -> Result<()> {
        // Create empty objects to prevent ownership issues
        let mut contract_cfgs = HashMap::new();
        
        for (address, bytecode) in &self.bytecode_cache.cache {
            let contract_cfg = self.generate_single_contract_cfg(address, bytecode)?;
            contract_cfgs.insert(*address, contract_cfg);
        }
        
        self.contract_cfgs = contract_cfgs;
        Ok(())
    }
    
    /// Generate CFG for a single contract
    fn generate_single_contract_cfg(&self, address: &H160, bytecode: &Bytes) -> Result<ContractCFG> {
        // Convert to the format required by revm
        let contract_data = bytecode.to_vec().into();
        let bytecode_analysed = to_analysed(RevmBytecode::new_raw(contract_data));
        
        // Get valid jump targets
        let revm_jumptable = bytecode_analysed.legacy_jump_table()
            .ok_or_else(|| eyre!("revm bytecode analysis failed"))?;
            
        let mut set_all_valid_jumpdests: HashSet<u16, FnvBuildHasher> = HashSet::default();
        let slice = revm_jumptable.as_slice();
        for (byte_index, &byte) in slice.iter().enumerate() {
            for bit_index in 0..8 {
                if byte & (1 << bit_index) != 0 {
                    let pc = (byte_index * 8 + bit_index) as u16;
                    set_all_valid_jumpdests.insert(pc);
                }
            }
        }
        
        // Parse instruction blocks
        let mut instruction_blocks = dasm::disassemble(bytecode_analysed.original_byte_slice().into());
        for block in &mut instruction_blocks {
            block.analyze_stack_info();
        }
        
        // Create instruction block mapping
        let map_to_instructionblocks: BTreeMap<(u16, u16), InstructionBlock> = instruction_blocks
            .iter()
            .map(|block| ((block.start_pc, block.end_pc), block.clone()))
            .collect();
            
        // Get execution steps for this contract
        let filtered_steps = trace::filter_steps_by_address(&self.trace_steps, address);
        let executed_pcs = trace::get_executed_pcs(&filtered_steps);
        
        // Create CFG
        let mut cfg_runner = CFGRunner::new(
            bytecode_analysed.original_byte_slice().into(),
            Box::leak(Box::new(map_to_instructionblocks)),
        );
        
        // Set executed PCs
        cfg_runner.set_executed_pcs(executed_pcs.clone());
        
        // Establish basic connections
        cfg_runner.form_basic_connections();
        
        // Remove unreachable instruction blocks
        cfg_runner.remove_unreachable_instruction_blocks();
        
        // Resolve indirect jumps
        crate::cfg_gen::stack_solve::symbolic_cycle(
            &mut cfg_runner,
            &set_all_valid_jumpdests,
            false,
        );
        
        // 假设这里调用 process_trace_and_number_edges
        let edge_numbering = self.process_trace_and_number_edges(&mut cfg_runner, &filtered_steps);

        Ok(ContractCFG {
            address: *address,
            cfg_runner: cfg_runner,
            executed_pcs,
            edge_numbering,
        })
    }
    // 新增：处理trace并编号边的函数
    pub fn process_trace_and_number_edges(&self, cfg_runner: &mut CFGRunner, trace_steps: &[TraceStep]) -> HashMap<((u16, u16), (u16, u16), Edges), u32> {
        let mut edge_numbering: HashMap<((u16, u16), (u16, u16), Edges), u32> = HashMap::new();
        let mut edge_counter = 0;
        // 存储已出现过的行号（trace_steps的索引，单增且唯一）
        let mut seen_line_numbers = HashSet::new();

        let mut i = 0;
        while i < trace_steps.len() {
            // 检查当前行号是否已出现过，若已出现则终止处理
            if seen_line_numbers.contains(&i) {
                println!("检测到重复行号 {}，终止当前合约的遍历", i);
                break;
            }
            seen_line_numbers.insert(i);

            let current_step = &trace_steps[i];
            let current_pc = current_step.pc.unwrap_or(0);
            let current_index = i; // 当前行号（索引）

            if let Some(op) = &current_step.op {
                if op == "JUMP" || op == "JUMPI" {
                    let default_stack = vec![];
                    let stack = current_step.stack.as_ref().unwrap_or(&default_stack);
                    let mut destination_pc = 0;

                    if op == "JUMP" {
                        destination_pc = stack.last().and_then(|val| u16::from_str_radix(&val[2..], 16).ok()).unwrap_or(0);
                        // 以16进制打印JUMP信息，带0x前缀
                        println!("检测到JUMP指令: 从PC 0x{:x} (行号 {}) 跳转到 PC 0x{:x}", current_pc, current_index, destination_pc);
                    } else if op == "JUMPI" {
                        let condition = stack.get(stack.len() - 2).and_then(|val| u16::from_str_radix(&val[2..], 16).ok()).unwrap_or(0);
                        if condition == 0 {
                            // 查找当前pc之后最近的下一个pc，且行号大于当前行号
                            destination_pc = trace_steps[i+1..]
                                .iter()
                                .enumerate() // 同时获取相对索引
                                .filter_map(|(relative_idx, step)| {
                                    step.pc.map(|pc| (relative_idx, pc))
                                })
                                // 确保pc大于当前pc，且绝对行号（当前行号+1+相对索引）大于当前行号
                                .filter(|&(_, pc)| pc > current_pc)
                                // 按pc值排序找到最小的有效pc
                                .min_by_key(|&(_, pc)| pc)
                                // 提取pc值，如果没找到则使用current_pc + 1
                                .map(|(_, pc)| pc)
                                .unwrap_or(current_pc + 1);
                            
                            // 以16进制打印JUMPI条件为0的信息
                            println!("检测到JUMPI指令: 条件为0，从PC 0x{:x} (行号 {}) 跳转到最近的下一个PC 0x{:x}", current_pc, current_index, destination_pc);
                        } else {
                            destination_pc = stack.last().and_then(|val| u16::from_str_radix(&val[2..], 16).ok()).unwrap_or(0);
                            // 以16进制打印JUMPI条件为非0的信息
                            println!("检测到JUMPI指令: 条件为非0，从PC 0x{:x} (行号 {}) 跳转到 PC 0x{:x}", current_pc, current_index, destination_pc);
                        }
                    }

                    let from_node = cfg_runner.get_node_from_pc(current_pc);
                    let to_node = cfg_runner.get_node_from_pc(destination_pc);

                    let edge_type = if op == "JUMP" {
                        Edges::Jump
                    } else if op == "JUMPI" && destination_pc == current_pc + 1 {
                        Edges::ConditionFalse
                    } else {
                        Edges::ConditionTrue
                    };

                    if!cfg_runner.cfg_dag.contains_edge(from_node, to_node) {
                        cfg_runner.cfg_dag.add_edge(from_node, to_node, edge_type);
                    }

                    let edge_key = (from_node, to_node, edge_type);
                    if!edge_numbering.contains_key(&edge_key) {
                        edge_numbering.insert(edge_key, edge_counter);
                        edge_counter += 1;
                    }

                    // 从新的pc开始继续遍历，确保下一个索引大于当前索引
                    let next_index = trace_steps[i+1..]
                        .iter()
                        .position(|step| step.pc.unwrap_or(0) == destination_pc)
                        .map(|pos| i + 1 + pos) // 计算绝对索引
                        .unwrap_or(i + 1); // 如果没找到，至少向前移动一步
                    
                    // 确保索引递增，防止循环
                    if next_index <= current_index {
                        println!("警告：可能的循环检测，强制索引递增");
                        i = current_index + 1;
                    } else {
                        i = next_index;
                    }
                } else {
                    i += 1;
                }
            } else {
                i += 1;
            }
        }

        edge_numbering
    }
    
    /// Create global transaction graph
    pub fn build_global_transaction_graph(&mut self) -> Result<()> {
        // Create global graph nodes for each node in contract CFGs
        for (address, contract_cfg) in &self.contract_cfgs {
            for node in contract_cfg.cfg_runner.cfg_dag.nodes() {
                // Only add executed nodes
                if contract_cfg.executed_pcs.contains(&node.0) {
                    let instruction_block = contract_cfg.cfg_runner.map_to_instructionblock.get(&node).unwrap();
                    let pc = instruction_block.start_pc;
                    
                    // Check if it contains SSTORE opcode
                    let contains_sstore = instruction_block.ops.iter().any(|(_, op, _)| *op == 0x55); // SSTORE opcode is 0x55
                    
                    // Check if it contains ADD or SUB opcodes
                    let contains_add_or_sub = instruction_block.ops.iter().any(|(_, op, _)| 
                        *op == 0x01 || // ADD opcode
                        *op == 0x03    // SUB opcode
                    );
                    
                    // Create transaction node
                    let tx_node = TransactionNode {
                        contract_address: *address,
                        pc,
                        instruction: instruction_block.to_string(),
                        contains_sstore, // Set SSTORE flag
                        contains_add_or_sub, // Set ADD/SUB flag
                    };
                    
                    // Add to global graph
                    let node_idx = self.global_graph.add_node(tx_node);
                    self.node_mapping.insert((*address, pc), node_idx);
                }
            }
        }
        
        // Add internal edges
        for (address, contract_cfg) in &self.contract_cfgs {
            for edge in contract_cfg.cfg_runner.cfg_dag.all_edges() {
                let (from_node, to_node, edge_type) = edge;
                let from_pc = from_node.0;
                let to_pc = to_node.0;
                
                // Only add edges where both endpoints were executed
                if contract_cfg.executed_pcs.contains(&from_pc) && contract_cfg.executed_pcs.contains(&to_pc) {
                    if let (Some(from_idx), Some(to_idx)) = (
                        self.node_mapping.get(&(*address, from_pc)),
                        self.node_mapping.get(&(*address, to_pc))
                    ) {
                        // Add internal edge
                        let edge_label = format!("{:?}", edge_type);
                        self.global_graph.add_edge(
                            *from_idx,
                            *to_idx,
                            TransactionEdge::Internal(edge_label),
                        );
                    }
                }
            }
        }
        
        // Add cross-contract call edges
        for edge in &self.call_edges {
            if let (Some(from_idx), Some(to_idx)) = (
                self.node_mapping.get(&(edge.from_addr, edge.from_pc)),
                // Assume target contract's entry PC is 0
                self.node_mapping.get(&(edge.to_addr, 0))
            ) {
                // Add external call edge
                self.global_graph.add_edge(
                    *from_idx,
                    *to_idx,
                    TransactionEdge::External(edge.call_type.clone()),
                );
            }
        }
        
        Ok(())
    }
    
    /// Export global transaction graph in DOT format
    pub fn export_global_graph_dot(&self) -> String {
        let mut dot_str = String::new();

        writeln!(&mut dot_str, "digraph G {{").unwrap();
        writeln!(&mut dot_str, "    rankdir=TB;").unwrap();
        writeln!(&mut dot_str, "    node [shape=box, style=\"filled, rounded\", color=\"#565f89\", fontcolor=\"#c0caf5\", fontname=\"Helvetica\", fillcolor=\"#24283b\"];").unwrap();
        writeln!(&mut dot_str, "    edge [color=\"#414868\", fontcolor=\"#c0caf5\", fontname=\"Helvetica\"];").unwrap();
        writeln!(&mut dot_str, "    bgcolor=\"#1a1b26\";").unwrap();

        // Add nodes
        for (idx, node) in self.global_graph.node_indices().zip(self.global_graph.node_weights()) {
            let addr_str = format!("{:?}", node.contract_address);
            let label = format!("{}\\nPC: {}\\n{}", addr_str, node.pc, node.instruction.replace('"', "\\\""));

            // Apply the same highlighting logic as in cfg_dot_str_highlighted_only
            // Color priority: SSTORE > ADD/SUB > others
            let fillcolor = if node.contains_sstore {
                "#f7768e" // Pink for SSTORE
            } else if node.contains_add_or_sub {
                "#ff9e64" // Orange for ADD/SUB
            } else {
                "#9ece6a" // Green for others
            };

            writeln!(
                &mut dot_str,
                "    {} [label=\"{}\", fillcolor=\"{}\", fontcolor=\"#1a1b26\"];",
                idx.index(),
                label,
                fillcolor
            ).unwrap();
        }

        // Add edges
        for edge in self.global_graph.edge_references() {
            let (from, to) = (edge.source().index(), edge.target().index());

            match &edge.weight() {
                TransactionEdge::Internal(edge_type) => {
                    let from_node = self.global_graph.node_weight(edge.source()).unwrap();
                    let to_node = self.global_graph.node_weight(edge.target()).unwrap();
                    let contract_cfg = self.contract_cfgs.get(&from_node.contract_address).unwrap();
                    let from_pc = from_node.pc;
                    let to_pc = to_node.pc;
                    let from_block = contract_cfg.cfg_runner.get_node_from_pc(from_pc);
                    let to_block = contract_cfg.cfg_runner.get_node_from_pc(to_pc);
                    let edge_type_enum = match edge_type.as_str() {
                        "ConditionTrue" => Edges::ConditionTrue,
                        "ConditionFalse" => Edges::ConditionFalse,
                        "SymbolicJump" => Edges::SymbolicJump,
                        _ => Edges::Jump,
                    };
                    let edge_key = (from_block, to_block, edge_type_enum);
                    let edge_number = contract_cfg.edge_numbering.get(&edge_key).cloned().unwrap_or(0);

                    // 为编号设置颜色（与边颜色一致，或使用对比色）
                    let style = match edge_type.as_str() {
                        "ConditionTrue" => {
                            // 边颜色为#9ece6a（绿色），编号使用白色对比
                            format!("color=\"#9ece6a\", label=<True - <font color=\"white\">#{}</font>>", edge_number)
                        }
                        "ConditionFalse" => {
                            // 边颜色为#f7768e（红色），编号使用白色对比
                            format!("color=\"#f7768e\", label=<False - <font color=\"white\">#{}</font>>", edge_number)
                        }
                        "SymbolicJump" => {
                            // 边颜色为#e0af68（金色），编号使用深色对比
                            format!("color=\"#e0af68\", style=\"dotted\", label=<Symbolic - <font color=\"#333333\">#{}</font>>", edge_number)
                        }
                        _ => {
                            // 边颜色为#414868（深蓝色），编号使用白色对比
                            format!("color=\"#414868\", label=<#<font color=\"white\">{}</font>>", edge_number)
                        }
                    };
                    writeln!(&mut dot_str, "    {} -> {} [{}];", from, to, style).unwrap();
                },
                TransactionEdge::External(call_type) => {
                    // 外部调用边，为编号（此处是call_type）设置颜色
                    let style = format!(
                        "color=\"#7aa2f7\", style=\"bold\", penwidth=2, label=<{}>",
                        // 用蓝色突出显示外部调用类型
                        format!("<font color=\"#0000ff\">{}</font>", call_type)
                    );
                    writeln!(&mut dot_str, "    {} -> {} [{}];", from, to, style).unwrap();
                }
            }
        }

        writeln!(&mut dot_str, "}}").unwrap();

        dot_str
    }
    
    /// Save global transaction graph to DOT file
    pub fn save_global_graph_dot(&self, output_path: &str) -> Result<()> {
        let dot_str = self.export_global_graph_dot();
        std::fs::write(output_path, dot_str)?;
        Ok(())
    }
    
    /// Convert to other formats (PNG, SVG, etc.)
    pub fn convert_to_image(&self, dot_path: &str, output_path: &str) -> Result<()> {
        let ext = Path::new(output_path).extension().and_then(|s| s.to_str()).unwrap_or("png");
        
        let output = std::process::Command::new("dot")
            .arg(format!("-T{}", ext))
            .arg("-o")
            .arg(output_path)
            .arg(dot_path)
            .output()?;
            
        if!output.status.success() {
            return Err(eyre!("Conversion failed: {}", String::from_utf8_lossy(&output.stderr)));
        }
        
        Ok(())
    }

    /// Export individual contract CFGs with only highlighted nodes and edges
    // 在TransactionAnalyzer的export_contract_highlighted_cfgs方法中
    pub fn export_contract_highlighted_cfgs(&self) -> HashMap<H160, String> {
        let mut results = HashMap::new();

        for (address, contract_cfg) in &self.contract_cfgs {
            // 传入预定义的边编号
            let dot_str = contract_cfg.cfg_runner.cfg_dot_str_highlighted_only(&contract_cfg.edge_numbering);
            results.insert(*address, dot_str);
        }

        results
    }
    
    /// Save individual contract CFGs with only highlighted nodes and edges
    pub fn save_contract_highlighted_cfgs(&self, output_dir: &str) -> Result<Vec<String>> {
        let mut saved_files = Vec::new();
        
        // Create output directory if it doesn't exist
        std::fs::create_dir_all(output_dir)?;
        
        for (address, dot_str) in self.export_contract_highlighted_cfgs() {
            let address_str = format!("{:x}", address);
            let output_path = format!("{}/{}.dot", output_dir, address_str);
            std::fs::write(&output_path, dot_str)?;
            saved_files.push(output_path);
        }
        
        Ok(saved_files)
    }
}