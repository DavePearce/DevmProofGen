use std::collections::HashMap;
use evmil::bytecode::Instruction;
use evmil::bytecode::Instruction::*;
use evmil::util::w256;
use crate::analysis::{BytecodeAnalysis,AbstractState};
use crate::opcodes::OPCODES;

#[derive(Clone,Debug)]
pub enum Bytecode {
    Comment(String),
    Assert(Vec<usize>,String),
    Mask(usize),
    Unit(Instruction),
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
    // States before each bytecode.
    states: Vec<BlockState>,
    // The set of bytecodes
    bytecodes: Vec<Bytecode>,
    // Fall-thru (if applicable)
    next: Option<usize>
}

impl Block {
    pub fn pc(&self) -> usize {
        self.pc
    }
    pub fn state(&self, i: usize) -> &BlockState {
        &self.states[i]
    }
    pub fn states(&self) -> &[BlockState] {
        &self.states
    }
    pub fn entry_states(&self) -> &[AbstractState] {
        &self.states[0].states
    }    
    pub fn bytecodes(&self) -> &[Bytecode] {
        &self.bytecodes
    }
    // Determine stack bounds on entry to this block.
    pub fn stack_bounds(&self) -> (usize,usize) {
        self.states[0].stack_bounds()
    }
    // Determine stack heights on entry to this block.
    pub fn stack_heights(&self) -> Vec<usize> {
        self.states[0].stack_heights()
    }
    // Determine freememory pointer bounds on entry to this block.
    pub fn freemem_ptrs(&self) -> Option<(usize,usize)> {
        self.states[0].freemem_ptr_bounds()
    }
    // Check whether this block is reachable. More specifically,
    // whether or not it was reached during the flow analysis.
    pub fn is_unreachable(&self) -> bool {
	// Block is unreachable if it contains no initial states.
	self.states[0].states.len() == 0
    }
    pub fn next(&self) -> Option<usize> { self.next }

    pub fn iter(&self) -> std::slice::Iter<Bytecode> {
        self.bytecodes.iter()
    }
    
    pub fn entry_state(&self) -> AbstractState {
        self.states[0].join_states()
    }
    /// Minimise block information to contain only that which is
    /// deemed "necessary".
    pub fn minimise(&mut self) {
        for s in &mut self.states {
            s.minimise()
        }
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
        let mut blocks = insns_to_blocks(n, insns, precheck);
        determine_necessary_stateinfo(&mut blocks);
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
    
    pub fn minimise(&mut self) {
        // Do it.
        for i in 0..self.blocks.len() {
            self.blocks[i].minimise();
        }
    }
}

/// Contains information relevant to a given block during the
/// minimisation procedure.
#[derive(Clone,Debug)]
pub struct BlockState {
    states: Vec<AbstractState>,    
    necessary: NecessaryState
}

impl BlockState {
    pub fn new(states: Vec<AbstractState>) -> Self {
        Self{states, necessary: NecessaryState::new()}
    }

    pub fn states(&self) -> &[AbstractState] {
        &self.states
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

    pub fn freemem_ptr_bounds(&self) -> Option<(usize,usize)> {
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

    pub fn necessary_stack_item(&self, item: usize) -> bool {
        self.necessary.get(item)
    }
    
    pub fn join_states(&self) -> AbstractState {
        let mut r = self.states[0].clone();
        //
        for i in 1..self.states.len() {
            r.join(&self.states[i]);
        }
        //
        r
    }

    pub fn clear_stack_item(&mut self, item: usize) {
        for s in &mut self.states {
            s.clear_stack_item(item);
        }
    }
    
    pub fn minimise(&mut self) {
        // Determine max stack height
        let (_,height) = self.stack_bounds();
        //
        for i in 0..height {
            // Check whether ith stack item is necessary (or not).
            if !self.necessary.get(i) {
                // Its not necessary, so clear it.
                self.clear_stack_item(i);
            } 
        }
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
    // Construct (initially) empty block
    let mut block = Block{pc,states: Vec::new(), bytecodes: Vec::new(),next: None};
    // Flag to signal early exit
    let mut done = false;
    // Travese block to its end
    while !done && i < insns.len() && n > 0 {
        let insn = &insns[i];
        let mut bc : Bytecode;
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
                    bc = Bytecode::Unit(insn.clone());
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
        // Account for any added bytecodes
        while block.states.len() < block.bytecodes.len() {
            let mut ith_states = analysis.get_states(i).to_vec();                
            block.states.push(BlockState::new(ith_states));        
        }
        //
        pc += insn.length();
        i += 1;
        n -= 1;
    }
    // Connect blocks together
    if n == 0 && !done { block.next = Some(pc); }    
    // Done
    (pc,i,block)
}

fn translate_insn(insn: &Instruction, mut done: bool, states: &[AbstractState]) -> (Bytecode,bool) {
    let bc = match insn {
        AND => {
            match &operand(0,states) {
                Some(b) if as_bit_mask(b) != 0 => {
                    Bytecode::Mask(as_bit_mask(b))
                }
                _ => Bytecode::Unit(insn.clone())                    
            }
        }
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
        RJUMPI(_)|RJUMP(_) => { todo!() }
        DATA(bytes) => {
            done = true;
            Bytecode::Unit(insn.clone())            
        }
        _ => {
            done = !insn.fallthru();
            Bytecode::Unit(insn.clone())
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

/// Extract a single value (where applicable) for a given item on the
/// stack.
fn operand(index: usize, states: &[AbstractState]) -> Option<w256> {
    let state = AbstractState::join_states(states);
    let stack = state.stack();
    if stack.len() <= index {
        None
    } else {
        stack[index]
    }
}


const MASK_U1 : w256 = w256::from_limbs([0b1,0,0,0]);
const MASK_U5 : w256  = w256::from_limbs([0b11111,0,0,0]);
const MASK_U8 : w256 = w256::from_limbs([0b11111111,0,0,0]);
const MASK_U16 : w256 = w256::from_limbs([0b11111111_11111111,0,0,0]);
const MASK_U24 : w256 = w256::from_limbs([0b11111111_11111111_11111111,0,0,0]);
const MASK_U32 : w256 = w256::from_limbs([0b11111111_11111111_11111111_11111111,0,0,0]);
const MASK_U64 : w256 = w256::from_limbs([0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111,0,0,0]);
const MASK_U128 : w256 = w256::from_limbs([0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111,0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111,0,0]);
const MASK_U160 : w256 = w256::from_limbs([0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111,0b11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111,0b11111111_11111111_11111111_11111111,0]);

/// Attempt to convert a given constant as a mask for a given
/// bitwidth.
fn as_bit_mask(w: &w256) -> usize {
    match *w {
	MASK_U1 => 1,
	MASK_U5 => 5,
	MASK_U8 => 8,
	MASK_U16 => 16,
	MASK_U32 => 32,
	MASK_U64 => 64,
	MASK_U128 => 128,	
	MASK_U160 => 160,		
	_ => 0
    }
}

// =============================================================================
// Minimisation
// =============================================================================

/// Contains information relevant to a given block during the
/// minimisation procedure.
#[derive(Clone,Debug)]
struct NecessaryState { stack: Vec<bool> }

impl NecessaryState {
    pub fn new() -> Self {
        Self{stack: Vec::new()}
    }
    
    // Check whether the given stack item was used or not.
    pub fn get(&self, index: usize) -> bool {
	let n = self.stack.len();	
        if index < n {	    
            self.stack[n - 1 - index]
        } else {
            false
        }
    }

    pub fn set(&mut self, index: usize, item: bool) {
	// Ensure stack is large enough
	while self.stack.len() <= index {
	    self.stack.insert(0,false);
	}
	// Make the assignment
	let n = self.stack.len();		
        self.stack[n - 1 - index] = item;
    }

    pub fn push(&mut self, item: bool) {
	self.stack.push(item);
    }

    pub fn pop(&mut self) -> bool {
	match self.stack.pop() {
	    Some(v) => v,
	    None => false
	}
    }
    
    // Merge another stack into this stack
    pub fn join(&mut self, other: &Self) -> bool {
	let n = usize::max(self.stack.len(),other.stack.len());
	// Ensure our stack is big enough
	while self.stack.len() < n { self.stack.insert(0,false); }
	// Now perform the merge
	let m = self.stack.len() - other.stack.len();
	let mut changed = false;
	for i in 0 .. other.stack.len() {
	    let old = self.stack[i+m];
	    self.stack[i+m] |= other.stack[i];
	    changed |= (old != self.stack[i+m]);
	}
	changed
    }    
}

/// Construct the necessary information to perform state minimisation.
fn determine_necessary_stateinfo(blocks: &mut [Block]) {
    let n = blocks.len();
    let mut offsets = HashMap::new();
    // Initialise every block
    for i in 0..n {
        let blk = &blocks[i];
        // Map block address to block index.
        offsets.insert(blk.pc(),i);
    }
    // Iterative dataflow analysis algorithm :)
    let mut changed = true;
    let mut counter = 100;
    while changed && counter > 0 {
        changed = false;        
        // Iterate backwards
        for i in (0..n).into_iter().rev() {
            // Determine incoming state
            let mut state = match blocks[i].next() {
                None => NecessaryState::new(),
                Some(pc) => {
                    blocks[*offsets.get(&pc).unwrap()].states[0].necessary.clone()
                }
            };
            // Iterate bytecodes in reverse
            let m = blocks[i].bytecodes().len();
            for j in (0..m).into_iter().rev() {
                let b = &blocks[i].bytecodes[j];
                // Apply effect of bytecode (in reverse)
                state = transfer_bytecode(b,state,&blocks,&offsets);
                // Now merge it in
                changed |= blocks[i].states[j].necessary.join(&state);                
            }
        }
	counter -= 1;
    }
}

fn transfer_bytecode(bytecode: &Bytecode, mut state: NecessaryState, blocks: &[Block], offsets: &HashMap<usize,usize>) -> NecessaryState {
    match bytecode {
	Bytecode::Comment(_) => { state }
	Bytecode::Assert(deps,_) => {
	    for dep in deps {
		state.set(*dep,true);
	    }
	    state
	}
	Bytecode::Unit(DUP(n)) => {
	    let n = *n as usize;
	    let mut tmp = state.get(0);
	    tmp |= state.get(n);
	    state.set(n,tmp);
	    state.pop();
	    state
	}
	Bytecode::Unit(SWAP(n)) => {
	    let n = *n as usize;
	    let tmp = state.get(0);
	    state.set(0,state.get(n));
	    state.set(n,tmp);
	    state
	}
	Bytecode::Unit(MSTORE|MSTORE8) => {
	    // Put things on the stack
	    state.push(false); // value lost
            state.push(true); // address always "used"
	    state
	}        
	Bytecode::Mask(mask) => {
            // Special AND representation
	    let mut used = state.pop();
	    // Put things on the stack
	    state.push(used);
            state.push(true); // mask always "used"            
            // Done
            state
        }
	Bytecode::Unit(insn) => {
	    let n = insn.operands();
	    let m = insn_produces(insn);
	    let mut used = false;
	    // Take things off the stack
	    for i in 0 .. m {
		used |= state.pop();
	    }
	    // Put things on the stack
	    for i in 0 .. n {
		state.push(used);
	    }
	    // Done
	    state
	}
	Bytecode::JumpI(targets) => {
	    let targets = merge_target_states(targets,blocks,offsets);
	    state.join(&targets);
	    state.push(false); // condition
	    state.push(true); // target pc            
	    state
	}
	Bytecode::Jump(targets) => {
	    let targets = merge_target_states(targets,blocks,offsets);
	    state.join(&targets);	    
	    state.push(true); // target pc
	    state
	}
    }
}

fn merge_target_states(targets: &[usize], blocks: &[Block], offsets: &HashMap<usize,usize>) -> NecessaryState {
    let mut state = NecessaryState::new();
    
    for pc in targets {
	let bid = offsets.get(pc).unwrap();
	state.join(&blocks[*bid].states[0].necessary);
    }
    // done
    state
}

// Determines how many stack items are produced by the given
// instruction.
fn insn_produces(insn: &Instruction) -> usize {
    match insn {
        STOP => 0,
        ADD|MUL|SUB|DIV|SDIV|MOD|SMOD|EXP|SIGNEXTEND => 1,
        ADDMOD|MULMOD => 1,
        LT|GT|SLT|SGT|EQ|AND|OR|XOR => 1,
        ISZERO|NOT => 1,
        BYTE|SHL|SHR|SAR|KECCAK256 => 1,
        // 30s: Environmental Information
        ADDRESS|ORIGIN|CALLER|CALLVALUE|CALLDATASIZE|CODESIZE|RETURNDATASIZE|GASPRICE => 1,
        BALANCE|CALLDATALOAD|EXTCODESIZE|EXTCODEHASH => 1,
        CALLDATACOPY|CODECOPY|RETURNDATACOPY|EXTCODECOPY => 0,
        // 40s: Block Information
        BLOCKHASH => 1,
        COINBASE|TIMESTAMP|NUMBER|DIFFICULTY|GASLIMIT|CHAINID|SELFBALANCE => 1,
        // 50s: Stack, Memory, Storage and Flow Operations
        MSIZE|PC|GAS|MLOAD|SLOAD => 1,
	JUMPDEST|POP|JUMP|JUMPI|SSTORE|MSTORE|MSTORE8 => 0,     
        // 60s & 70s: Push Operations            
        PUSH0|PUSH(_) => 1,
        // 80s: Duplication Operations
        DUP(_) => 1,
        // 90s: Swap Operations
        SWAP(_) => 0,
        // a0s: Log Operations
        LOG(_) => 0,
        // f0s: System Operations
        INVALID => 0,
        SELFDESTRUCT => 0,
        RETURN|REVERT => 0,            
        CREATE => 1,
        CREATE2 => 1,            
        DELEGATECALL|STATICCALL => 1,            
        CALL|CALLCODE => 1,
        // Virtual instructions
        HAVOC(_) => 0,
        DATA(_) => 0,
        _ => { unreachable!("{:?}",insn); }
    }
}
