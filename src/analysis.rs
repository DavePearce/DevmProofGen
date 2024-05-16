use std::cmp;
use std::fmt;
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
    pub fn clear_stack_item(&mut self, index: usize) {
        if index < self.stack_frame.len() {
            self.stack_frame[index] = None;
        }
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
    /// Join this state with another.  Observe that this produces an
    /// approximate state.
    pub fn join(&mut self, other: &AbstractState) {
        // Join freemem pointer
        Self::join_word(&mut self.freemem_ptr,&other.freemem_ptr);
        //
        self.join_stack(&other.stack_frame);
    }
    /// Remove what is known from one stack.
    pub fn cancel(&mut self, other: &AbstractState) {
        let n = other.stack_frame.len();
        for i in 0..n {
            if self.stack_frame[i] != None && other.stack_frame[i] != None {
                // cancel
                self.stack_frame[i] = None;
            }
        }
    }
    /// Convert abstract word into required format.  This should be
    /// deprecated in the future, when `Into<Option<w256>>` is
    /// implemented for `aw256`.
    fn from_aw256(v: &aw256) -> Option<w256> {
        if v.is_constant() { Some(v.constant().to())
        } else { None }
    }
    fn join_stack(&mut self, stack: &[Option<w256>]) {
        // Determine height of resulting stack
        let n = cmp::min(self.stack_frame.len(),stack.len());
        // Resize to that length
        self.stack_frame.truncate(n);
        // Join individual items
        for i in 0..n {
            Self::join_word(&mut self.stack_frame[i],&stack[i]);
        }
        // Done
    }
    fn join_word<T:PartialEq>(lhs: &mut Option<T>, rhs: &Option<T>) {
        match (&lhs,&rhs) {
            (Some(v),Some(w)) if v == w => {
                // do nothing in this case
            }
            (_,_) => {
                // reset lhs
                *lhs = None;
            }
        };
    }
}

impl fmt::Display for AbstractState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f,"|")?;                
        // Write freemem ptr
        match self.freemem_ptr {
            Some(w) => { write!(f,"fp={w:#06x}"); }
            None => {}
        }       
        write!(f,"|")?;
        // Write stack
        for (i,av) in self.stack_frame.iter().enumerate() {
            if i != 0 { write!(f,",")?; }
            match av {
                Some(w) => { write_w256(f,w)?; }
                None => {write!(f,"_")?;}
            }
        }
        write!(f,"|")?;        
        Ok(())
    }        
}

pub fn write_w256(f: &mut fmt::Formatter, w:&w256) -> fmt::Result {
    let mut first = true;
    write!(f,"0x")?;
    // Following is necessary because ruint::Uint doesn't
    // appear to play nicely with formatting hexadecimal.                
    for l in w.as_limbs().iter().rev() {
        if *l != 0 || !first {
            write!(f,"{l:02x}")?;
            first = false;
        }
    }
    if first {
        write!(f,"00")?;
    }
    Ok(())
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

