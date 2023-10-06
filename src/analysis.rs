use evmil::analysis::{EvmState, EvmStack};
use evmil::analysis::{aw256,ConcreteStack,ConcreteState,EvmMemory,trace,ConcreteMemory,UnknownStorage};
use evmil::bytecode::Instruction;
use evmil::bytecode::Instruction::*;
use evmil::util::{Concretizable,w256};

// =============================================================================
// Abstract State
// =============================================================================

/// An abstract representation of the EVM at a given point in time.
/// This includes information known about the stack at this point,
/// along with the free memory pointer.
#[derive(Clone,Debug,PartialEq)]
pub struct AbstractState {
    // Set of free memory pointers on entry.  If this is empty, then
    // the contents of the free memory pointer is unknown.    
    freemem_ptr: Option<usize>,
    // Set of stack frames on entry.  No information is known about
    // entries marked `None`
    stack_frame: Vec<Option<w256>>    
}

impl AbstractState {
    fn new(state: &State) -> Self {
        let freemem_ptr = Self::extract_fmp(state);
        let stack_frame = Self::extract_stack_frame(state);
        Self{freemem_ptr,stack_frame}
    }
    pub fn freemem_ptr(&self) -> Option<usize> {
        self.freemem_ptr
    }
    pub fn stack(&self) -> &[Option<w256>] {
        &self.stack_frame            
    }
    fn extract_fmp(state: &State) -> Option<usize> {
        let fmp = aw256::from(w256::from(0x40));
        // NOTE: this is a hack to work around the lack of an
        // immutable peek option for memory.
        let mut mem = state.memory().clone();        
        // Read free memory pointer        
        Self::from_aw256(&mem.read(fmp)).map(|s| s.to())
    }
    fn extract_stack_frame(state: &State) -> Vec<Option<w256>> {
        let stack = state.stack();
        let mut nstack = Vec::new();
        for i in 0..stack.size() {
            nstack.push(Self::from_aw256(stack.peek(i)));
        }
        nstack
    }
    /// Convert abstract word into required format.  This should be
    /// deprecated in the future, when `Into<Option<w256>>` is
    /// implemented for `aw256`.
    fn from_aw256(v: &aw256) -> Option<w256> {
        if v.is_constant() { Some(v.constant().to())
        } else { None }
    }
}

// =============================================================================
// Bytecode Analysis
// =============================================================================

/// Abstracts the key information generated from an abstract
/// interpretation of an instruction sequence.
pub struct BytecodeAnalysis {
    /// Stores information for each instruction.  Observe that this
    /// maps _byte offsets_ to analysis results (i.e. not _instruction
    /// offsets_).
    states: Vec<Vec<AbstractState>>
}

impl BytecodeAnalysis {
    /// Perform the bytecode analysis on a given sequence of
    /// instructions.
    pub fn from_insns(insns: &[Instruction]) -> Self {
        let mut states = Vec::new();        
        // Compute analysis results
        let init : State = State::new();
        // Run the abstract trace
        let trace : Vec<Vec<State>> = trace(&insns,init);
        // Convert into abstract states
        for t in trace {
            let mut s:Vec<_> = t.iter().map(|s| AbstractState::new(s)).collect();
            s.dedup();
            states.push(s);
        }
        //
        Self{states}        
    }

    /// Get the set of abstract states at a given instruction within
    /// the original sequence (i.e. an _instruction offset_ rather
    /// than a _byte offset_).
    pub fn get_states(&self, index: usize) -> &[AbstractState] {
        &self.states[index]
    }
}


// =============================================================================
// Helpers
// =============================================================================

// Package up a suitable state for the analysis
pub type State = ConcreteState<ConcreteStack<aw256>,ConcreteMemory<aw256>,UnknownStorage<aw256>>;

pub fn determine_stack_size(index: usize, analysis: &[Vec<State>]) -> (usize,usize) {
    let mut min = usize::MAX;
    let mut max = 0;
    // 
    for s in analysis[index].iter() {    
        min = min.min(s.stack().size());
        max = max.max(s.stack().size());        
    }
    //
    (min,max)
}    

pub fn extract_stack_values(i: usize, index: usize, analysis: &[Vec<State>]) -> Option<Vec<w256>> {
    let mut values = Vec::new();
    // 
    for s in analysis[index].iter() {    
        let v = s.stack().peek(i);
        if v.is_constant() {
            // FIXME: unsafe for large w256 values.
            values.push(v.constant());
        } else {
            // In this case, we have any unknown value so we cannot
            // conclude anything useful.
            return None;
        }
            
    }
    // Remove duplicates!
    values.sort_unstable();    
    values.dedup();
    //
    Some(values)
}    

pub fn extract_free_mem_pointer(index: usize, analysis: &[Vec<State>]) -> Vec<usize> {
    let fmp = aw256::from(w256::from(0x40));
    let mut values = Vec::new();
    //
    for s in analysis[index].iter() {
        // NOTE: this is a hack to work around the lack of an
        // immutable peek option for memory.
        let mut mem = s.memory().clone();
        // Read free memory pointer        
        let v = mem.read(fmp);
        // Check if known value
        if v.is_constant() {
            values.push(v.constant().to());
        } else {
            // In this case, we have any unknown value so we cannot
            // conclude anything useful.
            return Vec::new();
        }        
    }
    // Remove duplicates!
    values.sort_unstable();
    values.dedup();    
    //
    values
}

// Determine the target of this branch
pub fn branch_targets(mut pc: usize, insn: &Instruction, analysis: &[Vec<State>]) -> Vec<usize> {    
    match insn {
        RJUMP(offset)|RJUMPI(offset) => {
            // Push pc to past this instruction
            pc += insn.length();
            // Compute absolute target based on pc value of following
            // instruction.
            let target = (pc as isize) + (*offset as isize);
            vec![target as usize]
        }
	JUMP|JUMPI => {
	    let mut targets : Vec<usize> = Vec::new();
	    for s in analysis[pc].iter() {
                let target = s.stack().peek(0).constant();
		targets.push(target.to());
	    }
            targets.sort_unstable();
	    targets.dedup();
            targets
	}
        _ => {
            unreachable!()
        }
    }
}

