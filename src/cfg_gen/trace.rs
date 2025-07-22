use ethers::types::H160;
use serde::{Deserialize, Deserializer};
use std::collections::{HashMap, HashSet};
use std::str::FromStr;


// 自定义反序列化函数，用于将十六进制字符串转换为 u16
fn parse_hex_pc<'de, D>(deserializer: D) -> Result<Option<u16>, D::Error>
where
    D: Deserializer<'de>,
{
    let s: Option<String> = Option::deserialize(deserializer)?;
    match s {
        Some(s) => {
            if s.starts_with("0x") {
                u16::from_str_radix(&s[2..], 16).map(Some).map_err(serde::de::Error::custom)
            } else {
                u16::from_str_radix(&s, 10).map(Some).map_err(serde::de::Error::custom)
            }
        }
        None => Ok(None),
    }
}


#[derive(Debug, Deserialize, Clone)]
pub struct TraceStep {
    #[serde(deserialize_with = "parse_hex_pc")]
    pub pc: Option<u16>,
    pub op: Option<String>,
    pub gas: Option<u64>,
    #[serde(rename = "gasCost")]
    pub gas_cost: Option<u64>,
    pub depth: Option<u64>,
    pub error: Option<String>,
    pub stack: Option<Vec<String>>,
    pub memory: Option<Vec<String>>,
    pub storage: Option<HashMap<String, String>>,
    pub address: Option<HashMap<String, u8>>,
}

#[derive(Debug, Deserialize)]
pub struct TraceTransaction {
    pub gas: u64,
    pub failed: bool,
    #[serde(rename = "returnValue")]
    pub return_value: String,
    #[serde(rename = "structLogs")]
    pub struct_logs: Vec<TraceStep>,
}

impl TraceStep {
    /// Convert address field (HashMap) to a hex string starting with 0x
    pub fn address_hex(&self) -> Option<String> {
        self.address.as_ref().map(|map| {
            let mut bytes: Vec<u8> = vec![];
            for i in 0..map.len() {
                if let Some(b) = map.get(&i.to_string()) {
                    bytes.push(*b);
                }
            }
            format!("0x{}", hex::encode(bytes))
        })
    }

    /// Get address in H160 format
    pub fn get_h160_address(&self) -> Option<H160> {
        self.address_hex().and_then(|addr_hex| {
            H160::from_str(&addr_hex).ok()
        })
    }
    
    /// Determine if this step is a contract call
    pub fn is_contract_call(&self) -> bool {
        match &self.op {
            Some(op) => {
                op == "CALL" || op == "DELEGATECALL" || op == "STATICCALL" || op == "CALLCODE"
            },
            None => false,
        }
    }
    
    /// Get target address for contract call (from stack)
    pub fn get_call_target(&self) -> Option<H160> {
        if !self.is_contract_call() {
            return None;
        }
        
        // Different call instructions have target addresses at different positions in the stack
        // CALL: [gas, address, value, argsOffset, argsLength, retOffset, retLength]
        // DELEGATECALL/STATICCALL: [gas, address, argsOffset, argsLength, retOffset, retLength]
        let stack_pos = match self.op.as_deref() {
            Some("CALL") => 1, // Address is at the 2nd position (index 1)
            Some("DELEGATECALL") | Some("STATICCALL") | Some("CALLCODE") => 1, // Address is at the 2nd position
            _ => return None,
        };
        
        self.stack.as_ref().and_then(|stack| {
            if stack.len() > stack_pos {
                let addr_hex = &stack[stack.len() - 1 - stack_pos]; // Stack is read from right to left
                if addr_hex.starts_with("0x") {
                    H160::from_str(addr_hex).ok()
                } else {
                    H160::from_str(&format!("0x{}", addr_hex)).ok()
                }
            } else {
                None
            }
        })
    }
    
    /// Get call type
    pub fn get_call_type(&self) -> Option<String> {
        self.op.clone()
    }
}

/// Parse transaction trace file
pub fn parse_trace_file(path: &str) -> eyre::Result<Vec<TraceStep>> {
    let data = std::fs::read_to_string(path)?;
    
    // Try to parse directly as an array of steps
    let steps_result: Result<Vec<TraceStep>, _> = serde_json::from_str(&data);
    
    match steps_result {
        Ok(steps) => Ok(steps),
        Err(_) => {
            // Try to parse as TraceTransaction format
            let trace: TraceTransaction = serde_json::from_str(&data)?;
            Ok(trace.struct_logs)
        }
    }
}

/// Extract all contract addresses involved in the trace
pub fn extract_contract_addresses(steps: &[TraceStep]) -> HashSet<H160> {
    let mut addresses = HashSet::new();
    
    for step in steps {
        if let Some(addr) = step.get_h160_address() {
            addresses.insert(addr);
        }
    }
    
    addresses
}

/// Extract call relationships from the trace
pub struct CallEdge {
    pub from_addr: H160,
    pub from_pc: u16,
    pub to_addr: H160,
    pub call_type: String,
}

pub fn extract_call_edges(steps: &[TraceStep]) -> Vec<CallEdge> {
    let mut edges = Vec::new();
    let mut i = 0;
    
    while i < steps.len() - 1 {
        let current_step = &steps[i];
        let next_step = &steps[i + 1];
        
        if current_step.is_contract_call() {
            if let (Some(from_addr), Some(from_pc), Some(call_type)) = (
                current_step.get_h160_address(),
                current_step.pc,
                current_step.get_call_type()
            ) {
                if let Some(to_addr) = next_step.get_h160_address() {
                    edges.push(CallEdge {
                        from_addr,
                        from_pc,
                        to_addr,
                        call_type,
                    });
                }
            }
        }
        
        i += 1;
    }
    
    edges
}

/// Filter trace steps by address
pub fn filter_steps_by_address(steps: &[TraceStep], address: &H160) -> Vec<TraceStep> {
    steps
        .iter()
        .filter(|step| {
            if let Some(addr) = step.get_h160_address() {
                &addr == address
            } else {
                false
            }
        })
        .cloned()
        .collect()
}

/// Get the set of PC values executed by the contract
pub fn get_executed_pcs(steps: &[TraceStep]) -> HashSet<u16> {
    steps
        .iter()
        .filter_map(|step| step.pc)
        .collect()
}