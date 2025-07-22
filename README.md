# EVM Transaction Flow Visualizer

This tool analyzes Ethereum transaction trace files to automatically generate control flow graphs (CFGs) for the entire transaction execution process, including cross-contract call paths.

This tool is forked from the original [evm-cfg](https://github.com/plotchy/evm-cfg) and [evm-cfg-execpath](https://github.com/Avery76/evm-cfg-execpath).

## Features

- Automatically parses transaction traces and identifies all contract addresses involved
- Fetches contract bytecode through configured RPC nodes
- Generates internal control flow graphs for each contract with highlighted execution paths
- Combines all local path graphs into a complete global execution graph based on call relationships
- Supports identification of CALL, DELEGATECALL, STATICCALL and other cross-contract calls
- Highlights nodes with different colors based on operations:
  - Nodes with SSTORE operations: Pink (#f7768e)
  - Nodes with ADD/SUB operations: Orange (#ff9e64)
  - Other executed nodes: Green (#9ece6a)
- Provides aesthetically pleasing graph output, with export to DOT format or direct rendering to images
- Automatically saves the trace file and all contract CFGs in a structured directory

## Installation

1. Ensure you have Rust and Cargo installed
2. Clone the repository and build:

```bash
git clone https://github.com/OB-David/mev-cfg-dynamic.git
cd mev-cfg-dynamic
cargo build --release
```

## Configuration

Create a `.env` file in the project root directory and configure your RPC node URL:

```
GETH_API=https://eth-mainnet.g.alchemy.com/v2/YOUR_API_KEY
```

You can use Infura, Alchemy, or other Ethereum RPC providers.

## Usage

### Standard Method

Basic usage:

```bash
# Method 1: Directly provide a transaction hash (automatic trace retrieval)
./target/release/evm-cfg --tx-hash <TRANSACTION_HASH>

# Method 2: Provide an existing trace file
./target/release/evm-cfg --trace <PATH_TO_TRACE_FILE>

```

### Simplified Method (Recommended)

A simplified wrapper script `mev-cfg` is provided for convenience:

```bash
# First, make the script executable (only needed once)
chmod +x mev-cfg

# Method 1: Directly provide a transaction hash (automatic trace retrieval)
./mev-cfg --tx-hash <TRANSACTION_HASH>

# Method 2: Provide an existing trace file
./mev-cfg --trace <PATH_TO_TRACE_FILE>
```

The `mev-cfg` script automatically checks if a release build exists and creates one if needed, then forwards all arguments to the executable.

### Parameters

- `--trace`: Path to transaction trace file containing JSON output from debug_traceTransaction
- `--tx-hash`: Transaction hash value; the program will automatically retrieve the trace and generate the graph
- `--output`: (Optional) Path for the output DOT file; if not provided, named after the transaction hash
- `--render`: (Optional) Whether to automatically render to an image format, default is false
- `--format`: (Optional) Output image format, only valid when render=true, default is svg

Examples:

```bash
# Directly using a transaction hash (automatic processing)
./target/release/evm-cfg --tx-hash 0xef39c19ceb07373914204e76019943d57e5c4e99760ec2a337a6e9d38a315fbc
```

## Output Structure

When you run the tool, it will create the following output structure:

```
Results/
└── 0xTRANSACTION_HASH/
    ├── 0xCONTRACT_ADDRESS1.dot  # Highlighted CFG for contract 1
    ├── 0xCONTRACT_ADDRESS2.dot  # Highlighted CFG for contract 2
    ├── ...
    ├── Trace_TRANSACTION_HASH.txt  # Copy of the transaction trace
    └── 0xTRANSACTION_HASH.dot  # Global transaction graph
```

If you use the `--render` option, it will also create image files (SVG by default) for each DOT file.

## Obtaining Transaction Traces


## Viewing Results

The generated DOT files can be viewed using Graphviz tools:

```bash
dot -Tsvg Results/0xTRANSACTION_HASH/0xCONTRACT_ADDRESS.dot -o output.svg
```

Or directly use the tool's `--render` option to automatically generate images.

## Graph Styles and Color Codes

The generated control flow graphs use the following color conventions:

- **Pink nodes (#f7768e)**: Represent nodes containing SSTORE opcodes (state modifications)
- **Orange nodes (#ff9e64)**: Represent nodes containing ADD or SUB opcodes (value calculations)
- **Green nodes (#9ece6a)**: Represent other executed nodes
- **Blue bold edges**: Represent cross-contract calls
- **Green edges**: Represent execution paths in the highlighted CFGs

The SSTORE opcode is responsible for modifying contract storage state in the Ethereum EVM. By highlighting these nodes in pink, you can quickly identify all operations that change on-chain state during a transaction.

## Technical Details

This tool combines static analysis with execution traces to produce comprehensive transaction flow visualizations:

1. **Transaction Parsing**: Extracts all contract addresses and execution steps from transaction traces
2. **Bytecode Analysis**: Performs static analysis on each contract's bytecode to create basic CFGs
3. **Execution Path Highlighting**: Marks paths actually executed during the transaction
4. **Operation-Based Coloring**: Differentiates nodes based on their operations (SSTORE, ADD/SUB, etc.)
5. **Cross-Contract Flow**: Links individual contract CFGs to show the complete transaction flow


## License

[MIT License](LICENSE)
