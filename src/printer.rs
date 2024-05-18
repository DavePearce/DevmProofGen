use std::io::Write;
use evmil::bytecode::{Assemble,Instruction};
use evmil::bytecode::Instruction::*;
use evmil::util::{ToHexString,w256};

use crate::Config;
use crate::block::{Bytecode,Block,BlockState};
use crate::analysis::*;
use crate::opcodes::{OPCODES};

/// Responsible for printing individual blocks to a given writer.
/// What makes this complicated is that, at block boundaries, we want
/// to extract known information and include that in the `requires`
/// clause of the corresponding Dafny method.
pub struct BlockPrinter<'a,T:Write> {
    id: usize,
    out: T,
    settings: &'a Config
}

impl<'a,T:Write> BlockPrinter<'a,T> {
    pub fn new(id: usize, out: T, settings: &'a Config) -> Self {
        Self{id,out,settings}
    }
    
    pub fn print_block(&mut self, block: &Block) {
        // Print method signature
        writeln!(self.out,"\tmethod block_{}_{:#06x}(st': EvmState.ExecutingState) returns (st'': EvmState.State)", self.id, block.pc());
        // Print standard requires
        writeln!(self.out,"\trequires st'.evm.code == Code.Create(BYTECODE_{})",self.id);
        writeln!(self.out,"\trequires st'.WritesPermitted() && st'.PC() == {:#06x}",block.pc());
        if block.is_unreachable() {
            // Deadcode
            writeln!(self.out,"\t// Deadcode");            
            writeln!(self.out,"\trequires false");
        } else {
            self.print_fmp_requires(block);
            self.print_stack_requires(block);
        }
        writeln!(self.out,"\t{{");
        writeln!(self.out,"\t\tvar st := st';");
        for (i,code) in block.iter().enumerate() {
            let state = block.state(i);
            self.print_debug_info(state);
            self.print_code(code);
        }
        match block.next() {
            Some(pc) => {
                writeln!(self.out,"\t\tst := block_{}_{pc:#06x}(st);",self.id);
                writeln!(self.out,"\t\treturn st;");                
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
                    write!(self.out,"\trequires st'.MemSize() >= 0x60 && ");                
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
	let mut block = block.clone();
	// Minimise block information (if applicable)
	if self.settings.minimise_requires {
	    block.minimise();
	}
        // Generic stack bounds
        writeln!(self.out,"\t// Stack height(s)");
        self.print_stack_heights(&block);
        // Determine constant items
        let join = block.entry_state();
        // Print static items
        self.print_static_stack_requires(&join);
        // Print dynamic items
        self.print_dynamic_stack_requires(&block,&join);
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
        let stacked = block_stacked_states(block,join,max+1);        
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

    fn print_debug_info(&mut self, state: &BlockState) -> std::io::Result<()> {
	let mut state = state.clone();
	// Minimiase this state (if applicable)
	if self.settings.minimise_internal {
	    state.minimise();
	}
        for s in state.states() {
            write!(self.out,"\t\t//");            
            write!(self.out,"|")?;                
            // Write freemem ptr
            match s.freemem_ptr() {
                Some(w) => { write!(self.out,"fp={w:#06x}"); }
                None => {}
            }       
            write!(self.out,"|")?;
            // Write stack
            for (i,av) in s.stack().iter().enumerate() {
                if i != 0 { write!(self.out,",")?; }
                match av {
                    Some(w) => { self.write_w256(w)?; }
                    None => {write!(self.out,"_")?;}
                }
                if self.settings.debug && state.necessary_stack_item(i) {
                    write!(self.out,"*")?;
                }
            }
            writeln!(self.out,"|")?;        
        }
        Ok(())        
    }

    // FIXME: this was cloned from analysis.  I couldn't figure out
    // how to reuse it.
    fn write_w256(&mut self, w:&w256) -> std::io::Result<()> {
        let mut first = true;
        write!(self.out,"0x")?;
        // Following is necessary because ruint::Uint doesn't
        // appear to play nicely with formatting hexadecimal.                
        for l in w.as_limbs().iter().rev() {
            if *l != 0 || !first {
                write!(self.out,"{l:02x}")?;
                first = false;
            }
        }
        if first {
            write!(self.out,"00")?;
        }
        Ok(())
    }
    
    
    fn print_code(&mut self, code: &Bytecode) {
        //
        match code {
            Bytecode::Assert(uses,s) => {
                writeln!(self.out,"\t\tassert {s};");
            }            
            Bytecode::Comment(s) => {
                writeln!(self.out,"\t\t// {s}");
            }
            Bytecode::Jump(targets) => {
                self.print_jump(targets);
            }
            Bytecode::JumpI(targets) => {
                self.print_jumpi(targets);
            }
            Bytecode::Unit(CALL) => {
                self.print_call();
            }            
            Bytecode::Unit(DUP(n)) => {
                writeln!(self.out,"\t\tst := Dup(st,{n});");                                     
            }            
            Bytecode::Unit(LOG(n)) => {
                writeln!(self.out,"\t\tst := LogN(st,{n});");                                     
            }
            Bytecode::Unit(PUSH(bytes)) => {
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
            Bytecode::Unit(SWAP(n)) => {
                writeln!(self.out,"\t\tst := Swap(st,{n});");
            }            
            Bytecode::Unit(insn) => {
                let name = &OPCODES[insn.opcode() as usize];                
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

fn block_stacked_states(block: &Block, join: &AbstractState, n:usize) -> Vec<Vec<AbstractState>> {
    let mut stack = vec![Vec::new(); n];
    // Stack states
    for s in block.entry_states() {
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
