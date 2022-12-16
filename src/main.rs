use std::env;
use evmil::{Instruction,FromHexString,CfaState};
use evmil::{Disassemble,Disassembly};
use evmil::Instruction::*;

pub static OPCODE : &'static [&'static str] = &[
    "Stop", // 0x
    "Add",  // 0x
    "Mul",  // 0x
    "Sub",  // 0x
    "Div",  // 0x
    "SDiv", // 0x
    "Mod",  // 0x
    "SMod", // 0x
    "AddMod",  // 0x
    "MulMod",  // 0x
    "Exp",  // 0x
    "SignExtend",  // 0x    
];

fn print_preamble() {
    println!("include \"../../dafny/evm.dfy\"");
    println!("include \"../../dafny/evms/berlin.dfy\"");
    println!("import opened Int");
    println!("import opened Opcode");
    println!("import opened Memory");
    println!("import opened Bytecode");
    println!("import opened EvmBerlin");
    println!("import opened EvmState");
    println!();
    println!("const BYTECODE : seq<u8> := [];");
    println!();
    println!("method main(context: Context.T, world: map<u160,WorldState.Account>, gas: nat)");
    println!("requires context.writePermission");
    println!("requires gas > 100000");
    println!("requires context.address in world }}");
    println!("\tvar st := EvmBerlin.Create(context,world,gas,BYTECODE);");
}

fn dfy_bytecode_name(insn: &Instruction) {
    // Determine opcode
    let opcode = insn.opcode(&[]).unwrap();
    //
    
}

// This is a hack script for now.
fn main() {
    let args: Vec<String> = env::args().collect();
    // Parse hex string into bytes
    let bytes = args[1].from_hex_string().unwrap();
    // Disassemble bytes into instructions
    let mut disasm : Disassembly<CfaState> = Disassembly::new(&bytes).build();
    // Convert into instruction stream
    let instructions = disasm.to_vec();
    //
    print_preamble();
    //
    for insn in instructions {
        
    }
}
