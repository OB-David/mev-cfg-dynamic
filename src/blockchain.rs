use async_trait::async_trait;
use ethers::{
    providers::{Http, Middleware, Provider},
    types::{H160, BlockId, BlockNumber, Bytes, H256},
};
use eyre::{Result, eyre};
use std::collections::HashMap;
use std::sync::Arc;

#[async_trait]
pub trait BlockchainService {
    async fn get_code(&self, address: H160) -> Result<Bytes>;
    async fn get_transaction_trace(&self, tx_hash: H256) -> Result<String>;
}

pub struct EthersBlockchainService {
    provider: Arc<Provider<Http>>,
}

impl EthersBlockchainService {
    pub fn new(rpc_url: &str) -> Result<Self> {
        let provider = Provider::<Http>::try_from(rpc_url)?;
        Ok(Self {
            provider: Arc::new(provider),
        })
    }
}

#[async_trait]
impl BlockchainService for EthersBlockchainService {
    async fn get_code(&self, address: H160) -> Result<Bytes> {
        let code = self
            .provider
            .get_code(address, Some(BlockId::Number(BlockNumber::Latest)))
            .await?;
        Ok(code)
    }
    
    async fn get_transaction_trace(&self, tx_hash: H256) -> Result<String> {
        // Custom JS tracer to get address information for execution steps
        let address_tracer = r#"
        {
          data: [],
          step: function(log) {
            this.data.push({
              depth: log.getDepth(),
              address: log.contract ? (log.contract.getAddress ? log.contract.getAddress() : log.contract.address) : null
            });
          },
          fault: function(log) {},
          result: function() { return this.data; }
        }
        "#;
        
        // 1. Get standard trace (structured logs)
        let trace_params = serde_json::json!([tx_hash]);
        let trace_result: serde_json::Value = self.provider.request("debug_traceTransaction", trace_params).await?;
        
        // Extract structLogs from result
        let struct_logs = trace_result.get("structLogs")
            .ok_or_else(|| eyre!("Invalid trace result: missing structLogs field"))?
            .as_array()
            .ok_or_else(|| eyre!("structLogs is not an array"))?;
        
        // 2. Get address information (using custom tracer)
        let address_params = serde_json::json!([
            tx_hash,
            { "tracer": address_tracer }
        ]);
        let address_trace: Vec<serde_json::Value> = self.provider.request("debug_traceTransaction", address_params).await?;
        
        // 3. Merge data from both traces
        let mut merged_steps = Vec::new();
        
        for (i, log) in struct_logs.iter().enumerate() {
           
            let pc = log.get("pc").and_then(|v| v.as_u64()).unwrap_or(0);

            // Get opcode
            let op = log.get("op").and_then(|v| v.as_str()).unwrap_or("").to_string();
            
            // Get stack data, ensure format consistency
            let stack = log.get("stack")
                .and_then(|v| v.as_array())
                .map(|arr| arr.iter().map(|item| item.as_str().unwrap_or("").to_string()).collect::<Vec<String>>())
                .unwrap_or_default();
            
            // Get depth
            let depth = log.get("depth").and_then(|v| v.as_u64()).unwrap_or(0);
            
            // Get gas related information
            let gas = log.get("gas").and_then(|v| v.as_u64());
            let gas_cost = log.get("gasCost").and_then(|v| v.as_u64());
            
            // Get address information from address trace
            let address = if i < address_trace.len() {
                address_trace[i].get("address").cloned()
            } else {
                None
            };
            
            // Create merged step object
            let mut step = serde_json::json!({
                // Get 0x-prefixed hexadecimal pc
                "pc": format!("0x{:x}", pc),
                "op": op,
                "stack": stack,
                "depth": depth
            });
            
            // Add optional fields
            if let Some(g) = gas {
                step["gas"] = serde_json::json!(g);
            }
            
            if let Some(gc) = gas_cost {
                step["gasCost"] = serde_json::json!(gc);
            }
            
            if let Some(addr) = address {
                step["address"] = addr;
            }
            
            merged_steps.push(step);
        }
        
        // Convert merged steps to JSON string
        Ok(serde_json::to_string_pretty(&merged_steps)?)
    }
}

pub struct BytecodeCache {
    pub cache: HashMap<H160, Bytes>,
}

impl BytecodeCache {
    pub fn new() -> Self {
        Self {
            cache: HashMap::new(),
        }
    }

    pub fn get(&self, address: &H160) -> Option<&Bytes> {
        self.cache.get(address)
    }

    pub fn insert(&mut self, address: H160, bytecode: Bytes) {
        self.cache.insert(address, bytecode);
    }
}

pub async fn fetch_all_bytecodes(
    addresses: &[H160],
    blockchain_service: &impl BlockchainService,
) -> Result<BytecodeCache> {
    let mut cache = BytecodeCache::new();

    for address in addresses {
        let bytecode = blockchain_service.get_code(*address).await?;
        
        // Only save non-empty contracts
        if !bytecode.0.is_empty() {
            cache.insert(*address, bytecode);
        }
    }

    Ok(cache)
}

// Save transaction trace to file (returns trace json string only)
pub async fn save_transaction_trace(
    tx_hash: H256,
    blockchain_service: &impl BlockchainService,
) -> Result<String> {
    // Get transaction trace
    let trace_json = blockchain_service.get_transaction_trace(tx_hash).await?;
    
    // Return the trace JSON without saving to file
    // The main.rs will handle saving to the correct location
    Ok(trace_json)
}
