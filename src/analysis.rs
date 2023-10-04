use evmil::analysis::{EvmState, EvmStack};
use evmil::analysis::{aw256,ConcreteStack,ConcreteState,EvmMemory,trace,ConcreteMemory,UnknownStorage};
use evmil::bytecode::Instruction;
use evmil::bytecode::Instruction::*;
use evmil::util::{Concretizable,w256};
use crate::block::StackFrame;

/// Abstracts the key information generated from an abstract
/// interpretation of an instruction sequence.
pub struct BytecodeAnalysis {
    /// Stores information for each instruction.  Observe that this
    /// maps _byte offsets_ to analysis results (i.e. not _instruction
    /// offsets_).
    states: Vec<Vec<State>>
}

impl BytecodeAnalysis {
    /// Perform the bytecode analysis on a given sequence of
    /// instructions.
    pub fn from_insns(insns: &[Instruction]) -> Self {
        // Compute analysis results
        let init : State = State::new();
        // Run the abstract trace
        let states : Vec<Vec<State>> = trace(&insns,init);
        //
        todo!()
    }

    /// Get the set of stack frames for a given instruction within the
    /// original sequence (i.e. an _instruction offset_ rather than a
    /// _byte offset_).
    pub fn get_stack_frames(&self, index: usize) -> Vec<StackFrame> {
        todo!()
    }

    /// Get the set of free memory pointer positions for a given
    /// instruction within the original sequence (i.e. an _instruction
    /// offset_ rather than a _byte offset_).  Observe that, if the
    /// result is empty, this indicates nothing is known about the
    /// free memory pointer at this position.
    pub fn get_freemem_ptr(&self, index: usize) -> Vec<usize> {
        todo!()
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
    values.dedup();
    //
    Some(values)
}    

pub fn extract_free_mem_pointer(index: usize, analysis: &[Vec<State>]) -> Option<Vec<usize>> {
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
            return None;
        }        
    }
    // Remove duplicates!
    values.dedup();    
    //
    Some(values)    
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
	    targets.dedup();
            targets
	}
        _ => {
            unreachable!()
        }
    }
}

