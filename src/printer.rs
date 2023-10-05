use evmil::bytecode::{Assemble,Instruction};
use evmil::bytecode::Instruction::*;
use evmil::util::{ToHexString};

use crate::block::{Bytecode,Block};
use crate::analysis::*;
use crate::opcodes::{OPCODES};
use crate::PreconditionFn;

pub struct DafnyPrinter {
    id: usize,
    out: String
}

impl DafnyPrinter {
    pub fn new(id: usize) -> Self {
        Self{id,out:String::new()}
    }
    pub fn to_string(self) -> String {
        self.out
    }
    pub fn print(&mut self, s: &str) {
        self.out.push_str(s);
    }
    pub fn println(&mut self, s: &str) {
        self.out.push_str(s);
        self.out.push_str("\n");
    }

    /// Print the raw bytecode associated with this instruction
    /// sequence.
    pub fn print_bytecode(&mut self, insns: &[Instruction]) {
        // Convert instructions into bytes
        let mut bytes = insns.assemble();
        //
        self.print(&format!("const BYTECODE_{} : seq<u8> := [",self.id));
        //
        for i in 0..bytes.len() {
            let ith = format!("{:#02x}", bytes[i]);
            self.print(&ith);
            if (i + 1) != bytes.len() {
                self.print(", ");
            }
        }
        self.println("];");
        self.println("");
    }    
    
    pub fn print_block(&mut self, block: &Block) {
        let sig = format!("method block_{}_{:#06x}(st': EvmState.ExecutingState) returns (st'': EvmState.State)", self.id, block.pc());        
        self.println(&sig);
        self.print_requires(block);
        self.println("{");
        self.println("\tvar st := st';");
        for code in block.iter() {
            self.print_code(code);
        }
        match block.next() {
            Some(pc) => {
                self.println(&format!("\treturn block_{}_{pc:#06x}(st);",self.id));
            }
            None => {
                self.println("\treturn st;");
            }
        }
        self.println("}");
        self.println("");        
    }

    fn print_requires(&mut self, block: &Block) {
        let req1 = format!("requires st'.evm.code == Code.Create(BYTECODE_{});",self.id);
        let req2 = format!("requires st'.WritesPermitted() && st'.PC() == {:#06x}",block.pc());
        // Standard requires
        self.println(&req1);
        self.println(&req2);
        // Frames
        self.print("requires ");
        //
        for (i,st) in block.states().iter().enumerate() {
            if i != 0 {
                self.println("");
                self.print("\t\t || ");
            }
            self.print_state(st);
        }
        self.println("");
    }

    fn print_state(&mut self, state: &AbstractState) {
        let stack = state.stack();
        self.print("(");
        // Print out stack height
        self.print(&format!("st'.Operands() == {}",stack.len()));
        // Print out free memory pointer (if applicable)
        match state.freemem_ptr() {
            Some(v) => {
                self.print(" && Memory.Size(st'.evm.memory) >= 0x60");
                self.print(&format!(" && st'.Read(0x40) == {v:#x}"));
            }
            None => {}
        }
        // Print out stack
        for i in 0..stack.len() {
            match stack[i] {
                Some(v) => {
                    self.print(" && ");                    
                    // NOTE: following is a hack to work around
                    // hex display problems with w256.
                    if v.byte_len() <= 16 {
                        let jth128 : u128 = v.to();
                        self.print(&format!("st'.Peek({i}) == {:#02x}",jth128));
                    } else {
                        self.print(&format!("st'.Peek({i}) == {:#02x}",v));
                    }
                }
                None => {
                    
                }
            }
        }
        self.print(")");        
    }
    
    fn print_code(&mut self, code: &Bytecode) {
        //
        match code {
            Bytecode::Comment(s) => {
                self.print("\t// ");
                self.println(s);
            }
            Bytecode::Dup(n) => {
                self.println(&format!("\tst := Dup(st,{n});"));                                     
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
                    1 => self.println(&format!("\tst := Push1(st,{});", hex)),
                    2 => self.println(&format!("\tst := Push2(st,{});", hex)),
                    3 => self.println(&format!("\tst := Push3(st,{});", hex)),
                    4 => self.println(&format!("\tst := Push4(st,{});", hex)),
                    _ => {
                        self.println(&format!("\tst := PushN(st,{n},{});", hex))
                    }                    
                }
            }            
            Bytecode::Swap(n) => {
                self.println(&format!("\tst := Swap(st,{n});"));
            }            
            Bytecode::Unit(_,name) => {
                self.println(&format!("\tst := {name}(st);"));                
            }
            _ => {
                self.println("\t???");
            }
        }
    }

    fn print_jump(&mut self, targets: &[usize]) {
        // Print out assumptions
        self.print_jump_assumes(targets);
        // Print out instruction
        self.println("\tst := Jump(st);");
        // Manage Control Flow
        if targets.len() == 1 {
            self.println(&format!("\tst := block_{}_{:#06x}(st);", self.id, targets[0]));
        } else {
            self.println("\tmatch st.PC() {{");
            for target in targets {
                self.println(&format!("\t\tcase {target:#x} => {{ st := block_{}_{target:#06x}(st); }}",self.id));
            }
            self.println("\t}}");
        }
    }

    fn print_jumpi(&mut self, targets: &[usize]) {
        // Print out assumptions
        self.print_jump_assumes(targets);
        // Print out instruction
        self.println("\tst := JumpI(st);");
        // Manage Control Flow
        if targets.len() == 1 {
            let target = targets[0];
            let line = format!("\tif st.PC() == {target:#x} {{ return block_{}_{target:#06x}(st); }}",self.id);
            self.println(&line);
        } else {
            self.println("\tmatch st.PC() {{");
            for target in targets {
                self.println(&format!("\t\tcase {target:#x} => {{ return block_{}_{target:#06x}(st); }}",self.id));
            }
            self.println("\t\tcase _ => {{}}");
            self.println("\t}}");
        }
    }

    fn print_jump_assumes(&mut self, targets: &[usize]) {
        for target in targets {
            self.println(&format!("\tassume st.IsJumpDest({target:#x});"));
        }
    }                
}

fn print_block_header(id: usize, index: usize, pc: usize, analysis: &[Vec<State>]) {
    // First compute upper and lower bounds on the stack height.
    let (min,max) = determine_stack_size(index,analysis);
    //    
    println!("method block_{id}_{:#06x}(st': EvmState.ExecutingState) returns (st'': EvmState.State)", pc);
    println!("requires st'.evm.code == Code.Create(BYTECODE_{id});");
    println!("requires st'.WritesPermitted() && st'.PC() == {pc:#06x}");
    // Limit stack height
    if min == max {
        println!("requires st'.Operands() == {max}");
    } else if min < max {
        println!("requires {min} <= st'.Operands() <= {max}");
    }
    if min <= max {
        // Figure out concrete stack values        
        for i in 0..min {
            match extract_stack_values(i,index,analysis) {
                Some(items) => {
                    print!("requires ");
                    for j in 0..items.len() {
                        if j != 0 { print!(" || "); }
                        let jth = items[j];
                        // NOTE: following is a hack to work around
                        // hex display problems with w256.
                        if jth.byte_len() <= 16 {
                            let jth128 : u128 = items[j].to();
                            print!("(st'.Peek({i}) == {:#02x})",jth128);
                        } else {
                            print!("(st'.Peek({i}) == {:#02x})",items[j]);
                        }
                    }
                    println!();
                }
                None => { }
            }
        }
        // Support free_memory pointer
        let fmp = extract_free_mem_pointer(index,analysis);
        if fmp.len() > 0 {
            print!("requires Memory.Size(st'.evm.memory) >= 0x60 && (");
            for j in 0..fmp.len() {
                if j != 0 { print!(" || "); }
                print!("st'.Read(0x40) == {:#x}",fmp[j]);
            }
            println!(")");
        }
    } else {
        // NOTE: min > max suggests unreachable code.  Therefore, put
        // in place something to check this is actually true.
        println!("requires false;");
    }
    println!("{{");
    println!("\tvar st := st';");
}

// fn print_call() {
//     println!("\tvar CONTINUING(cc) := Call(st);");
//     println!("\t{{");
//     println!("\t\tvar inner := cc.CallEnter(1);");
//     println!("\t\tif inner.EXECUTING? {{ inner := external_call(cc.sender,inner); }}");
//     println!("\t\tst := cc.CallReturn(inner);");
//     println!("\t}}");
// }
