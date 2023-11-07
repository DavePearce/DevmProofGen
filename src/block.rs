use evmil::bytecode::Instruction;
use evmil::bytecode::Instruction::*;
use evmil::util::w256;
use crate::analysis::{BytecodeAnalysis,AbstractState};
use crate::opcodes::OPCODES;

#[derive(Clone,Debug)]
pub enum Bytecode {
    Call,
    Comment(String),
    Raw(String),
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
#[derive(Clone,Debug)]
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
    pub fn stack_bounds(&self) -> (usize,usize) {
        let mut min = usize::MAX;
        let mut max = 0;
        // 
        for s in &self.states {    
            min = min.min(s.stack().len());
            max = max.max(s.stack().len());        
        }
        //
        (min,max)        
    }
    pub fn stack_heights(&self) -> Vec<usize> {
        let mut hs = Vec::new();
        for s in &self.states {
            hs.push(s.stack().len());
        }
        hs.sort();
        hs.dedup();
        hs
    }
    pub fn freemem_ptrs(&self) -> Option<(usize,usize)> {
        let mut min = usize::MAX;
        let mut max = 0;
        // 
        for s in &self.states {
            match s.freemem_ptr() {
                Some(p) => {
                    min = min.min(p);
                    max = max.max(p);
                }
                None => { return None; }
            }
        }
        //
        Some((min,max))
    }
    pub fn next(&self) -> Option<usize> { self.next }
    pub fn iter(&self) -> std::slice::Iter<Bytecode> {
        self.bytecodes.iter()
    }
}

/// Represents a sequence of basic blocks which are ordered in some
/// particular way.
#[derive(Clone)]
pub struct BlockSequence {
    blocks: Vec<Block>
}

impl BlockSequence {
    /// Construct a block sequence from a given instruction sequence.
    pub fn from_insns(n: usize, insns: &[Instruction], precheck: PreconditionFn) -> Self {
        let blocks = insns_to_blocks(n, insns, precheck);
        Self{blocks}
    }

    pub fn as_ref(&self) -> &[Block] {
        &self.blocks
    }
    
    pub fn iter(&self) -> std::slice::Iter<Block> {
        self.blocks.iter()
    }

    pub fn to_vec(self) -> Vec<Block> {
        self.blocks
    }
}

// =============================================================================
// Helpers
// =============================================================================

pub type PreconditionFn = fn(&Instruction,&mut Vec<Bytecode>);

/// Decompose a given instruction sequence into a block sequence.
/// This employs an abstract interpretation to determine various key
/// pieces of information (e.g. jump targets, stack values, etc) at
/// each point.
fn insns_to_blocks(n: usize, insns: &[Instruction], precheck: PreconditionFn) -> Vec<Block> {
    // Compute suplementary information needed for remainder.
    let analysis = BytecodeAnalysis::from_insns(insns);
    // Initially empty set of blocks.
    let mut blocks = Vec::new();
    // Index of current instruction.
    let mut index = 0;    
    // Byte offset of current instruction.
    let mut pc = 0;
    // Process blocks one by one until all sequence is exhausted.
    while n > 0 && index < insns.len() {
        let block : Block;
        // Process next block
        (pc,index,block) = insns_to_block(n,pc,index,insns,&analysis,precheck);
        // Store processed block
        blocks.push(block);
    }
    // Done
    blocks
}

/// Extract the next block starting at a given byte offset (and
/// instruction offset) within the original sequence.
fn insns_to_block(mut n: usize, mut pc: usize, index: usize, insns: &[Instruction], analysis: &BytecodeAnalysis, precheck: PreconditionFn) -> (usize,usize,Block) {
    let mut i = index;    
    // Extract abstract states at this position.
    let states = analysis.get_states(i).to_vec();
    // Construct (initially) empty block
    let mut block = Block{pc,states,bytecodes: Vec::new(),next: None};
    // Flag to signal early exit
    let mut done = false;
    // Travese block to its end
    while !done && i < insns.len() && n > 0 {
        let insn = &insns[i];
        let mut bc : Bytecode;        
        // Insert debug information
        add_debug_info(&mut block,analysis.get_states(i));
        // Insert any precondition checks
        precheck(insn, &mut block.bytecodes);
        // Convert bytecode                
        match insn {
            JUMPDEST => {
                // Jumpdest handled specially
                if i == index {
                    // A jumddest is only allowed as the first
                    // instruction of a block.  This is because we
                    // cannot jump into the middle of a Dafny
                    // method!
                    let name = &OPCODES[insn.opcode() as usize];
                    bc = Bytecode::Unit(false,name);
                } else {
                    // Indicates split is necessary.
                    block.next = Some(pc);
                    break;
                }
            }            
            _ => {
                // Translate any other kind of instruction
                (bc,done) = translate_insn(insn,done,analysis.get_states(i));
            }
        };
        block.bytecodes.push(bc);
        pc += insn.length();
        i += 1;
        n -= 1;
    }
    // Connect blocks together
    if n == 0 && !done { block.next = Some(pc); }    
    // Done
    (pc,i,block)
}

fn add_debug_info(block: &mut Block, states: &[AbstractState]) {
    for s in states {
        let bc = Bytecode::Comment(format!("{}",s));
        block.bytecodes.push(bc);
    }
}

fn translate_insn(insn: &Instruction, mut done: bool, states: &[AbstractState]) -> (Bytecode,bool) {
    let bc = match insn {
        CALL => Bytecode::Call,
        CALLCODE => todo!(),
        DELEGATECALL => todo!(),        
        DUP(n) => Bytecode::Dup(*n),
        HAVOC(n) => {
            // Virtual instructions
            Bytecode::Comment(format!("Havoc {n}"))
        }
        JUMPI => {
            // Extract branch targets
            let targets = jump_targets(states);
            // 
            Bytecode::JumpI(targets)
        }
        JUMP => {
            // Extract branch targets
            let targets = jump_targets(states);
            // Terminating instruction
            done = true;
            // 
            Bytecode::Jump(targets)                    
        }
        LOG(n) =>  Bytecode::Log(*n),            
        PUSH(bytes) => { Bytecode::Push(bytes.clone()) }
        RJUMPI(_)|RJUMP(_) => { todo!() }
        STATICCALL => todo!(),        
        SWAP(n) =>  Bytecode::Swap(*n),
        DATA(bytes) => {
            done = true;
            Bytecode::Unit(true,"Invalid")            
        }
        _ => {
            let name = &OPCODES[insn.opcode() as usize];
            done = !insn.fallthru();
            Bytecode::Unit(!insn.fallthru(),name)
        }
    };
    (bc,done)
}

/// Extract the set of possible jump targets from a given abstract
/// state.  That is, the set of possible values on top of the stack in
/// the given state.
fn jump_targets(states: &[AbstractState]) -> Vec<usize> {
    let mut targets :Vec<usize> = Vec::new();
    for s in states {
        // NOTE: this will fail if the branch target is unknown.  For
        // now, I just assume this can never happen.  However, in
        // practice, it could happen in some unusual cases (e.g. the
        // jump target is loaded out of memory or storage).
        targets.push(s.stack()[0].unwrap().to());
    }
    targets.sort_unstable();
    targets.dedup();
    targets
}
