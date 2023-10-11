use std::io::Write;
use evmil::bytecode::{Assemble,Instruction};
use evmil::bytecode::Instruction::*;
use evmil::util::{ToHexString};

use crate::block::{Bytecode,Block};
use crate::analysis::*;
use crate::opcodes::{OPCODES};
use crate::PreconditionFn;

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
        let (min,max) = block.stack_heights();        
        // Generic stack bounds
        if min == max {
            writeln!(self.out,"\trequires st'.Operands() == {min}");
        } else {
            writeln!(self.out,"\trequires st'.Operands() >= {min} && st'.Operands() <= {max}");
        }        
        // Decompose states
        let stacked = stacked_states(block.states(),max+1);
        //
        for (sh,sts) in stacked.iter().enumerate() {
            if min <= sh && is_useful(&sts) {
                write!(self.out,"\trequires ");
                if min != max { write!(self.out,"st'.Operands() == {sh} ==> ("); }
                for (i,st) in sts.iter().enumerate() {
                    if i != 0 {
                        writeln!(self.out,"");
                        write!(self.out,"\t || ");
                    }
                    self.print_state(st);
                }
                if min != max { write!(self.out,")"); }
                writeln!(self.out,"");
            }            
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
}

fn stacked_states(states: &[AbstractState], n:usize) -> Vec<Vec<&AbstractState>> {
    let mut stack = vec![Vec::new(); n];
    for s in states {
        let sh = s.stack().len();
        stack[sh].push(s);
    }
    stack
}

/// Check no state in a given set of states offers no value.  That is
/// where we no *nothing* about the stack in the case.
fn is_useful(states: &[&AbstractState]) -> bool {
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


// fn print_call() {
//     println!("\tvar CONTINUING(cc) := Call(st);");
//     println!("\t{{");
//     println!("\t\tvar inner := cc.CallEnter(1);");
//     println!("\t\tif inner.EXECUTING? {{ inner := external_call(cc.sender,inner); }}");
//     println!("\t\tst := cc.CallReturn(inner);");
//     println!("\t}}");
// }
