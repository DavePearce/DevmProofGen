use evmil::bytecode::Instruction;
use evmil::bytecode::Instruction::*;
use evmil::util::w256;
use crate::analysis::{BytecodeAnalysis,AbstractState};
use crate::opcodes::OPCODES;

pub enum Bytecode {
    Comment(String),
    Unit(bool,&'static str),
    Push(Vec<u8>),
    Dup(u8),
    Log(u8),    
    Swap(u8),
    JumpI(Vec<usize>),
    Jump(Vec<usize>)
}

/// Represents a basic block within a given sequence of instructions.
/// All relevant information for generating the proof object is
/// included.
pub struct Block {
    // The starting PC for this block
    pc: usize,
    // Set of state frames on entry
    states: Vec<AbstractState>,
    // The set of bytecodes
    bytecodes: Vec<Bytecode>,
    // Fall-thru (if applicable)
    next: Option<usize>
}

impl Block {
    pub fn pc(&self) -> usize {
        self.pc
    }
    pub fn states(&self) -> &[AbstractState] {
        &self.states
    }
    pub fn bytecodes(&self) -> &[Bytecode] {
        &self.bytecodes
    }
    pub fn next(&self) -> Option<usize> { self.next }
    pub fn iter(&self) -> std::slice::Iter<Bytecode> {
        self.bytecodes.iter()
    }
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

    pub fn iter(&self) -> std::slice::Iter<Block> {
        self.blocks.iter()
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
    while index < insns.len() {
        let block : Block;
        // Process next block
        (pc,index,block) = insns_to_block(pc,index,insns,&analysis);
        // Store processed block
        blocks.push(block);
    }
    // Done
    blocks
}

/// Extract the next block starting at a given byte offset (and
/// instruction offset) within the original sequence.
fn insns_to_block(mut pc: usize, index: usize, insns: &[Instruction], analysis: &BytecodeAnalysis) -> (usize,usize,Block) {
    let mut i = index;    
    // Extract abstract states at this position.
    let states = analysis.get_states(i).to_vec();
    // Construct (initially) empty block
    let mut block = Block{pc,states,bytecodes: Vec::new(),next: None};
    // Flag to signal early exit
    let mut done = false;
    // Travese block to its end
    while !done && i < insns.len() {
        let insn = &insns[i];
        // Convert bytecode
        let bc = match insn {
            DUP(n) => Bytecode::Dup(*n),
            HAVOC(n) => {
                // Virtual instructions
                Bytecode::Comment(format!("Havoc {n}"))
            }
            JUMPDEST => {
                if i == index {
                    // A jumddest is only allowed as the first
                    // instruction of a block.  This is because we
                    // cannot jump into the middle of a Dafny
                    // method!
                    let name = &OPCODES[insn.opcode() as usize];
                    Bytecode::Unit(false,name)
                } else {
                    // Indicates split is necessary.
                    block.next = Some(pc);
                    break;
                }
            }
            JUMPI => {
                // Extract branch targets
                let targets = jump_targets(analysis.get_states(i));
                // 
                Bytecode::JumpI(targets)
            }
            JUMP => {
                // Extract branch targets
                let targets = jump_targets(analysis.get_states(i));
                // Terminating instruction
                done = true;
                // 
                Bytecode::Jump(targets)                    
            }
            LOG(n) =>  Bytecode::Log(*n),            
            PUSH(bytes) => { Bytecode::Push(bytes.clone()) }
            RJUMPI(_)|RJUMP(_) => { todo!() }
            SWAP(n) =>  Bytecode::Swap(*n),      
            _ => {
                let name = &OPCODES[insn.opcode() as usize];
                done = !insn.fallthru();
                Bytecode::Unit(!insn.fallthru(),name)
            }
        };
        block.bytecodes.push(bc);
        pc += insn.length();
        i += 1;
    }
    // Done
    (pc,i,block)
}

/// Extract the set of possible jump targets from a given abstract
/// state.  That is, the set of possible values on top of the stack in
/// the given state.
fn jump_targets(states: &[AbstractState]) -> Vec<usize> {
    let mut targets = Vec::new();
    for s in states {
        // NOTE: this will fail if the branch target is unknown.  For
        // now, I just assume this can never happen.  However, in
        // practice, it could happen in some unusual cases (e.g. the
        // jump target is loaded out of memory or storage).
        targets.push(s.stack()[0].unwrap().to());
    }
    targets
}
