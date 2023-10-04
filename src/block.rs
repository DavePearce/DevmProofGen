use evmil::bytecode::Instruction;
use evmil::util::w256;
use crate::analysis::BytecodeAnalysis;

pub enum Bytecode {
    Unit(bool,&'static str),
    Push(Vec<u8>),
    Dup(usize),
    Swap(usize),
    JumpI(Vec<usize>),
    Jump(Vec<usize>)
}

pub struct StackFrame {
    // Height of the stack in this frame
    height: usize,
    // Items on the stack in this frame (where first is top).  If an
    // item is None, this indicates nothing is known in this frame
    // about that item.
    items: Option<w256>
}

/// Represents a basic block within a given sequence of instructions.
/// All relevant information for generating the proof object is
/// included.
pub struct Block {
    // The starting PC for this block
    pc: usize,
    // Set of free memory pointers on entry.  If this is empty, then
    // the contents of the free memory pointer is unknown.
    freemem_ptr: Vec<usize>,
    // Set of stack frames on entry
    stack_frames: Vec<StackFrame>,
    // The set of bytecodes
    bytecodes: Vec<Bytecode>
}

/// Represents a sequence of basic blocks which are ordered in some
/// particular way.
pub struct BlockSequence {
    blocks: Vec<Block>
}

impl BlockSequence {
    /// Construct a block sequence from a given instruction sequence.
    pub fn from_insns(insns: &[Instruction]) -> Self {
        let blocks = insns_to_blocks(insns);
        Self{blocks}
    }
}

// =============================================================================
// Helpers
// =============================================================================

/// Decompose a given instruction sequence into a block sequence.
/// This employs an abstract interpretation to determine various key
/// pieces of information (e.g. jump targets, stack values, etc) at
/// each point.
fn insns_to_blocks(insns: &[Instruction]) -> Vec<Block> {
    // Compute suplementary information needed for remainder.
    let analysis = BytecodeAnalysis::from_insns(insns);
    // Initially empty set of blocks.
    let mut blocks = Vec::new();
    // Index of current instruction.
    let mut index = 0;    
    // Byte offset of current instruction.
    let mut pc = 0;
    // Process blocks one by one until all sequence is exhausted.
    loop {
        let block : Block;
        // Process next block
        (pc,index,block) = insns_to_block(pc,index,insns,&analysis);
        // Store processed block
        blocks.push(block);
    }
}

/// Extract the next block starting at a given byte offset (and
/// instruction offset) within the original sequence.
fn insns_to_block(mut pc: usize, mut index: usize, insns: &[Instruction], analysis: &BytecodeAnalysis) -> (usize,usize,Block) {
    // Extract stack frames at this position.
    let stack_frames = analysis.get_stack_frames(index);
    // Extract free memory ptr at this position.
    let freemem_ptr = analysis.get_freemem_ptr(index);
    // Construct (initially) empty block
    let mut block = Block{pc,freemem_ptr,stack_frames,bytecodes: Vec::new()};
    //
    todo!()
}
