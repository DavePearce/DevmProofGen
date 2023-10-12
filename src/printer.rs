use std::io::Write;
use evmil::bytecode::{Assemble,Instruction};
use evmil::bytecode::Instruction::*;
use evmil::util::{ToHexString};

use crate::block::{Bytecode,Block};
use crate::analysis::*;
use crate::opcodes::{OPCODES};
use crate::PreconditionFn;

/// Responsible for printing individual blocks to a given writer.
/// What makes this complicated is that, at block boundaries, we want
/// to extract known information and include that in the `requires`
/// clause of the corresponding Dafny method.
pub struct BlockPrinter<T:Write> {
    id: usize,
    out: T
}

impl<T:Write> BlockPrinter<T> {
    pub fn new(id: usize, out: T) -> Self {
        Self{id,out}
    }
    
    pub fn print_block(&mut self, block: &Block) {
        // Print method signature
        writeln!(self.out,"\tmethod block_{}_{:#06x}(st': EvmState.ExecutingState) returns (st'': EvmState.State)", self.id, block.pc());
        // Print standard requires
        writeln!(self.out,"\trequires st'.evm.code == Code.Create(BYTECODE_{})",self.id);
        writeln!(self.out,"\trequires st'.WritesPermitted() && st'.PC() == {:#06x}",block.pc());
        self.print_fmp_requires(block);
        self.print_stack_requires(block);        
        writeln!(self.out,"\t{{");
        writeln!(self.out,"\t\tvar st := st';");
        for code in block.iter() {
            self.print_code(code);
        }
        match block.next() {
            Some(pc) => {
                writeln!(self.out,"\t\tst := block_{}_{pc:#06x}(st); return st;",self.id);
            }
            None => {
                writeln!(self.out,"\t\treturn st;");
            }
        }
        writeln!(self.out,"\t}}");
        writeln!(self.out,"");        
    }

    fn print_fmp_requires(&mut self, block: &Block) {
        // Constants to help
        let fmps = block.freemem_ptrs();
        // Generic free ptr bounds
        match fmps {
            Some((v,w)) => {
                if v >= 0x60 {
                    writeln!(self.out,"\t// Free memory pointer");                    
                    write!(self.out,"\trequires Memory.Size(st'.evm.memory) >= 0x60 && ");                
                    if v == w {
                        writeln!(self.out,"st'.Read(0x40) == {:#02x}",v);
                    } else {
                        writeln!(self.out,"st'.Read(0x40) >= {:#02x}",v);
                    }
                }
            }
            _ => {}
        }        
    }
    
    fn print_stack_requires(&mut self, block: &Block) {
        // Generic stack bounds
        writeln!(self.out,"\t// Stack height(s)");
        self.print_stack_heights(block);
        // Determine constant items
        let join = join_states(block.states());
        // Print static items
        self.print_static_stack_requires(&join);
        // Print dynamic items
        self.print_dynamic_stack_requires(block,&join);
    }

    fn print_stack_heights(&mut self, block: &Block) {
        // Compute min \& max heights
        let (min,max) = block.stack_bounds();
        let heights = block.stack_heights();
        let mut contig = true;
        for i in 0..heights.len() {
            if heights[i] != (min+i) { contig = false; }
        }
        //
        if min == max {
            writeln!(self.out,"\trequires st'.Operands() == {min}");
        } else if contig {
            writeln!(self.out,"\trequires st'.Operands() >= {min} && st'.Operands() <= {max}");
        } else {
            write!(self.out,"\trequires st'.Operands() in {{");
            for h in heights {
                if h != min { write!(self.out,","); }
                write!(self.out,"{h}");
            }
            writeln!(self.out,"}}");
        }
    }        
    
    fn print_dynamic_stack_requires(&mut self, block: &Block, join: &AbstractState) {
        let (min,max) = block.stack_bounds();                
        // Decompose states        
        let stacked = stacked_states(block.states(),join,max+1);        
        //
        for (sh,sts) in stacked.iter().enumerate() {
            if min <= sh && is_useful(&sts) {
                if min == sh { writeln!(self.out,"\t// Dynamic stack items"); }                
                write!(self.out,"\trequires ");
                if min != max { write!(self.out,"st'.Operands() == {sh} ==> ("); }
                for (i,st) in sts.iter().enumerate() {
                    if i != 0 {
                        write!(self.out," || ");
                    }
                    self.print_state(st);
                }
                if min != max { write!(self.out,")"); }
                writeln!(self.out,"");
            } 
        }
    }

    /// Print all static 
    fn print_static_stack_requires(&mut self, join: &AbstractState) {
        // Check whether at least one static stack item.
        let atleast_one = join.stack().iter().fold(false,|a,e| a || matches!(e,Some(_)));
        //
        if atleast_one {
            writeln!(self.out,"\t// Static stack items");
            write!(self.out,"\trequires ");
            self.print_state(join);
            writeln!(self.out);
        }
    }        

    fn print_state(&mut self, state: &AbstractState) {
        let stack = state.stack();
        write!(self.out,"(");
        // Print out stack
        let mut first = true;
        for i in 0..stack.len() {
            match stack[i] {
                Some(v) => {
                    if !first {
                        write!(self.out," && ");
                    }
                    // NOTE: following is a hack to work around
                    // hex display problems with w256.
                    if v.byte_len() <= 16 {
                        let jth128 : u128 = v.to();
                        write!(self.out,"st'.Peek({i}) == {:#02x}",jth128);
                    } else {
                        write!(self.out,"st'.Peek({i}) == {:#02x}",v);
                    }
                    first = false;                    
                }
                None => {
                    
                }
            }
        }
        write!(self.out,")");        
    }
    
    fn print_code(&mut self, code: &Bytecode) {
        //
        match code {
            Bytecode::Call => {
                self.print_call();
            }
            Bytecode::Comment(s) => {
                writeln!(self.out,"\t\t// {s}");
            }
            Bytecode::Dup(n) => {
                writeln!(self.out,"\t\tst := Dup(st,{n});");                                     
            }
            Bytecode::Log(n) => {
                writeln!(self.out,"\t\tst := LogN(st,{n});");                                     
            }            
            Bytecode::Jump(targets) => {
                self.print_jump(targets);
            }
            Bytecode::JumpI(targets) => {
                self.print_jumpi(targets);
            }
            Bytecode::Push(bytes) => {
                let n = bytes.len();
                let hex = bytes.to_hex_string();
                match n {
                    1 => writeln!(self.out,"\t\tst := Push1(st,{});", hex),
                    2 => writeln!(self.out,"\t\tst := Push2(st,{});", hex),
                    3 => writeln!(self.out,"\t\tst := Push3(st,{});", hex),
                    4 => writeln!(self.out,"\t\tst := Push4(st,{});", hex),                    
                    _ => {
                        writeln!(self.out,"\t\tst := PushN(st,{n},{});", hex)
                    }                    
                };
            }            
            Bytecode::Swap(n) => {
                writeln!(self.out,"\t\tst := Swap(st,{n});");
            }            
            Bytecode::Unit(_,name) => {
                writeln!(self.out,"\t\tst := {name}(st);");                
            }
        };
    }

    fn print_jump(&mut self, targets: &[usize]) {
        // Print out assumptions
        self.print_jump_assumes(targets);
        // Print out instruction
        writeln!(self.out,"\t\tst := Jump(st);");
        // Manage Control Flow
        if targets.len() == 1 {
            writeln!(self.out,"\t\tst := block_{}_{:#06x}(st);", self.id, targets[0]);
        } else {
            writeln!(self.out,"\t\tmatch st.PC() {{");
            for target in targets {
                writeln!(self.out,"\t\t\tcase {target:#x} => {{ st := block_{}_{target:#06x}(st); }}",self.id);
            }
            writeln!(self.out,"\t}}");
        }
    }

    fn print_jumpi(&mut self, targets: &[usize]) {
        // Print out assumptions
        self.print_jump_assumes(targets);
        // Print out instruction
        writeln!(self.out,"\t\tst := JumpI(st);");        
        // Manage Control Flow
        if targets.len() == 1 {
            let target = targets[0];
            writeln!(self.out,"\t\tif st.PC() == {target:#x} {{ st := block_{}_{target:#06x}(st); return st;}}",self.id);
        } else {
            writeln!(self.out,"\tmatch st.PC() {{");
            for target in targets {
                writeln!(self.out,"\t\tcase {target:#x} => {{ st := block_{}_{target:#06x}(st); return st;}}",self.id);
            }
            writeln!(self.out,"\t\tcase _ => {{}}");
            writeln!(self.out,"\t}}");            
        }
    }

    fn print_jump_assumes(&mut self, targets: &[usize]) {
        for target in targets {
            writeln!(self.out,"\t\tassume st.IsJumpDest({target:#x});");
        }
    }

    fn print_call(&mut self) {
        writeln!(self.out,"\t\tvar CONTINUING(cc) := Call(st);");
        writeln!(self.out,"\t\t{{");
        writeln!(self.out,"\t\t\tvar inner := cc.CallEnter(1);");
        writeln!(self.out,"\t\t\tif inner.EXECUTING? {{ inner := external_call(cc.sender,inner); }}");
        writeln!(self.out,"\t\t\tst := cc.CallReturn(inner);");
        writeln!(self.out,"\t\t}}");
    }
    
}

/// Determine items which are constant across all stack states.
fn join_states(states: &[AbstractState]) -> AbstractState {
    let mut r = states[0].clone();
    //
    for i in 1..states.len() {
        r.join(&states[i]);
    }
    //
    r
}

fn stacked_states(states: &[AbstractState], join: &AbstractState, n:usize) -> Vec<Vec<AbstractState>> {
    let mut stack = vec![Vec::new(); n];
    for s in states {
        let sh = s.stack().len();
        let mut ns = s.clone();
        assert!(ns.stack().len() >= join.stack().len());
        ns.cancel(join);
        stack[sh].push(ns);
    }
    stack
}

/// Check no state in a given set of states offers no value.  That is
/// where we no *nothing* about the stack in the case.
fn is_useful(states: &[AbstractState]) -> bool {
    if states.len() == 0 { return false; }
    for st in states {
        if !has_value(st) { return false; }
    }
    true
}

/// Check whether we know something useful about the stack in this
/// state.  A stack is useful if it contains at least one known value.
fn has_value(st: &AbstractState) -> bool {
    let stack = st.stack();
    let mut count = 0;
    for i in 0..stack.len() {
        match stack[i] {
            Some(_) => { count += 1; }
            None => {}
        }
    }
    count > 0
}
