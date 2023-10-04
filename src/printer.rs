use evmil::bytecode::{Instruction};
use evmil::bytecode::Instruction::*;
use evmil::util::{ToHexString};

use crate::analysis::*;
use crate::opcodes::{OPCODES};
use crate::PreconditionFn;


pub fn print_preamble(bytes: &[u8]) {
    println!("include \"evm-dafny/src/dafny/evm.dfy\"");
    println!("include \"evm-dafny/src/dafny/evms/berlin.dfy\"");
    println!("import opened Int");
    println!("import opened Opcode");
    println!("import opened Memory");
    println!("import opened Bytecode");
    println!();
    println!("method external_call(sender: u160, st: EvmState.ExecutingState) returns (r:EvmState.TerminatedState)");
    println!("ensures r.RETURNS? ==> r.world.Exists(sender) {{");
    println!("\t return EvmState.ERROR(EvmState.INSUFFICIENT_GAS); // dummy");
    println!("}}");
    println!();
    // println!("method main(context: Context.T, world: map<u160,WorldState.Account>, gas: nat) returns (st': EvmState.State)");
    // println!("requires context.writePermission");
    // println!("requires gas > 100000");
    // println!("requires context.address in world {{");
    // println!("\tvar st := EvmBerlin.Create(context,world,gas,BYTECODE);");
}


pub fn print_code_section(id: usize, instructions: &[Instruction], analysis: &[Vec<State>], preconditions: PreconditionFn, blocksize: u16) {
    let mut pc = 0;
    let mut block = false;
    let mut size = 0;
    // Print out the bytecode (only for legacy contracts?)
    print_code_bytecode(id,instructions);
    //
    for (index,insn) in instructions.iter().enumerate() {
        // Manage jump dests
        if block && insn == &Instruction::JUMPDEST {
            // Jumpdest detected.  Therefore, we need to break the
            // current block up.
            println!("\tst := block_{id}_{:#06x}(st);",pc);
            // Block terminator
            println!("\treturn st;");
            println!("}}");
            println!("");
            block = false;
        }
        // If we are not currently within a block, then print out the
        // block header.        
        if !block {
            print_block_header(id,index,pc,analysis);
            block = true;
            size = blocksize;
        }
        // Check any preconditions
        preconditions(insn);
        // Print out the instruction
        print_instruction(index,insn,analysis);
        // Monitor size of current block
        size -= 1;
        // Manage control-flow
        if size == 0 || !insn.fallthru() {           
            if insn.can_branch() {
                // Unconditional branch
                let targets = branch_targets(index,insn,analysis);
                //
                if targets.len() == 1 {
                    println!("\tst := block_{id}_{:#06x}(st);", targets[0]);
                } else {
                    println!("\tmatch st.PC() {{");
                    for target in targets {
                        println!("\t\tcase {target:#x} => {{ st := block_{id}_{target:#06x}(st); }}");
                    }
                    println!("\t}}");
                }
            } else if size == 0 {
                let target = pc+insn.length();
                println!("\tst := block_{id}_{:#06x}(st);", target);                
            }
            // Block terminator
            println!("\treturn st;");
            println!("}}");
            println!("");
            block = false;
        } else if insn.can_branch() {
            // Conditional branch
            let targets = branch_targets(index,insn,analysis);
            if targets.len() == 1 {
                let target = targets[0];
                println!("\tif st.PC() == {target:#x} {{ st := block_{id}_{target:#06x}(st); return st; }}");                
            } else {
                println!("\tmatch st.PC() {{");
                for target in targets {
                    println!("\t\tcase {target:#x} => {{ st := block_{id}_{target:#06x}(st); return st; }}");                
                }
                println!("\t\tcase _ => {{}}");
                println!("\t}}");
            }
        }
        // Move passed instruction
        pc = pc + insn.length();
    }
}

fn print_code_bytecode(id: usize, insns: &[Instruction]) {
    // Convert instructions into bytes
    let mut bytes = Vec::new();
    let mut pc = 0;
    for b in insns {
        b.encode(pc,&mut bytes);
        pc += b.length();
    }
    //
    print!("const BYTECODE_{id} : seq<u8> := [");
    for i in 0..bytes.len() {
        print!("{:#02x}", bytes[i]);
        if (i + 1) != bytes.len() {
            print!(", ");
        }
    }
    println!("];");
    println!();
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
        match extract_free_mem_pointer(index,analysis) {
            Some(items) => {
                print!("requires Memory.Size(st'.evm.memory) >= 0x60 && (");
                for j in 0..items.len() {
                    if j != 0 { print!(" || "); }
                    print!("st'.Read(0x40) == {:#x}",items[j]);
                }
                println!(")");
            }
            None => {}
        }
    } else {
        // NOTE: min > max suggests unreachable code.  Therefore, put
        // in place something to check this is actually true.
        println!("requires false;");
    }
    println!("{{");
    println!("\tvar st := st';");
}

fn print_instruction(index: usize, insn: &Instruction, analysis: &[Vec<State>]) {
    match insn {
        DATA(bytes) => {
            println!("\t// {}", bytes.to_hex_string());
        }
        PUSH(bytes) => {
            let opcode = 0x5f + bytes.len();
            println!("\tst := {}(st,{});", OPCODES[opcode], bytes.to_hex_string());
        }
        CALL => {
            print_call();
        }
        DUP(n) => {
            println!("\tst := Dup(st,{});", n);
        }
        JUMP|JUMPI => {
            for target in branch_targets(index,insn,analysis) {
                println!("\tassume st.IsJumpDest({target:#x});");
            }
            println!("\tst := {}(st);", to_dfy_name(&insn));            
        }
        RJUMP(offset) => {
            println!("\tst := RJump(st,{offset:#x});");
        }
        RJUMPI(offset) => {
            println!("\tst := RJumpI(st,{offset:#x});");
        }
        SWAP(n) => {
            println!("\tst := Swap(st,{});", n);
        }
        HAVOC(n) => {
            println!("\t// havoc {n}");
        }
        _ => {
            println!("\tst := {}(st);", to_dfy_name(&insn));
        }
    }
}

fn to_dfy_name(insn: &Instruction) -> String {
    // Determine opcode
    let opcode = insn.opcode();
    //
    OPCODES[opcode as usize].to_string()
}


fn print_call() {
    println!("\tvar CONTINUING(cc) := Call(st);");
    println!("\t{{");
    println!("\t\tvar inner := cc.CallEnter(1);");
    println!("\t\tif inner.EXECUTING? {{ inner := external_call(cc.sender,inner); }}");
    println!("\t\tst := cc.CallReturn(inner);");
    println!("\t}}");
}
