use clap::{arg, Arg, Command};
use evmil::evm::{AbstractStack, Disassembly};
use evmil::ll::Instruction;
use evmil::ll::Instruction::*;
use evmil::util::{w256, Concretizable, FromHexString, Interval, IsTop, ToHexString};
use std::env;

pub static OPCODES: &'static [&'static str] = &[
    "Stop",           //             0x00
    "Add",            //              0x01
    "Mul",            //              0x02
    "Sub",            //              0x03
    "Div",            //              0x04
    "SDiv",           //             0x05
    "Mod",            //              0x06
    "SMod",           //             0x07
    "AddMod",         //           0x08
    "MulMod",         //           0x09
    "Exp",            //              0x0a
    "SignExtend",     //       0x0b
    "",               //                 0x0c
    "",               //                 0x0d
    "",               //                 0x0e
    "",               //                 0x0f
    "Lt",             //               0x10
    "Gt",             //               0x11
    "SLt",            //              0x12
    "SGt",            //              0x13
    "Eq",             //               0x14
    "IsZero",         //           0x15
    "And",            //              0x16
    "Or",             //               0x17
    "Xor",            //              0x18
    "Not",            //              0x19
    "Byte",           //             0x1a
    "Shl",            //              0x1b
    "Shr",            //              0x1c
    "Sar",            //              0x1d
    "",               //                 0x1e
    "",               //                 0x1f
    "Keccak256",      //        0x20
    "",               //                 0x21
    "",               //                 0x22
    "",               //                 0x23
    "",               //                 0x24
    "",               //                 0x25
    "",               //                 0x26
    "",               //                 0x27
    "",               //                 0x28
    "",               //                 0x29
    "",               //                 0x2a
    "",               //                 0x2b
    "",               //                 0x2c
    "",               //                 0x2d
    "",               //                 0x2e
    "",               //                 0x2f
    "Address",        //          0x30
    "Balance",        //          0x31
    "Origin",         //           0x32
    "Caller",         //           0x33
    "CallValue",      //        0x34
    "CallDataLoad",   //     0x35
    "CallDataSize",   //     0x36
    "CallDataCopy",   //     0x37
    "CodeSize",       //         0x38
    "CodeCopy",       //         0x39
    "GasPrice",       //         0x3a
    "ExtCodeSize",    //      0x3b
    "ExtCodeCopy",    //      0x3c
    "ReturnDataSize", //   0x3d
    "ReturnDataCopy", //   0x3e
    "ExtCodeHash",    //      0x3f
    "BlockHash",      //        0x40
    "CoinBase",       //         0x41
    "TimeStamp",      //        0x42
    "Number",         //           0x43
    "Difficulty",     //       0x44
    "GasLimit",       //         0x45
    "ChainID",        //          0x46
    "SelfBalance",    //      0x47
    "",               //                 0x48
    "",               //                 0x49
    "",               //                 0x4a
    "",               //                 0x4b
    "",               //                 0x4c
    "",               //                 0x4d
    "",               //                 0x4e
    "",               //                 0x4f
    "Pop",            //              0x50
    "MLoad",          //            0x51
    "MStore",         //           0x52
    "MStore8",        //          0x53
    "SLoad",          //            0x54
    "SStore",         //           0x55
    "Jump",           //             0x56
    "JumpI",          //            0x57
    "Pc",             //               0x58
    "MSize",          //            0x59
    "Gas",            //              0x5a
    "JumpDest",       //         0x5b
    "",               //                 0x5c
    "",               //                 0x5d
    "",               //                 0x5e
    "",               //                 0x5f
    "Push1",          //            0x60
    "Push2",          //            0x61
    "Push3",          //            0x62
    "Push4",          //            0x63
    "Push5",          //            0x64
    "Push6",          //            0x65
    "Push7",          //            0x66
    "Push8",          //            0x67
    "Push9",          //            0x68
    "Push10",         //           0x69
    "Push11",         //           0x6a
    "Push12",         //           0x6b
    "Push13",         //           0x6c
    "Push14",         //           0x6d
    "Push15",         //           0x6e
    "Push16",         //           0x6f
    "Push17",         //           0x70
    "Push18",         //           0x71
    "Push19",         //           0x72
    "Push20",         //           0x73
    "Push21",         //           0x74
    "Push22",         //           0x75
    "Push23",         //           0x76
    "Push24",         //           0x77
    "Push25",         //           0x78
    "Push26",         //           0x79
    "Push27",         //           0x7a
    "Push28",         //           0x7b
    "Push29",         //           0x7c
    "Push30",         //           0x7d
    "Push31",         //           0x7e
    "Push32",         //           0x7f
    "Dup1",           //             0x80
    "Dup2",           //             0x81
    "Dup3",           //             0x82
    "Dup4",           //             0x83
    "Dup5",           //             0x84
    "Dup6",           //             0x85
    "Dup7",           //             0x86
    "Dup8",           //             0x87
    "Dup9",           //             0x88
    "Dup10",          //            0x89
    "Dup11",          //            0x8a
    "Dup12",          //            0x8b
    "Dup13",          //            0x8c
    "Dup14",          //            0x8d
    "Dup15",          //            0x8e
    "Dup16",          //            0x8f
    "Swap1",          //            0x90
    "Swap2",          //            0x91
    "Swap3",          //            0x92
    "Swap4",          //            0x93
    "Swap5",          //            0x94
    "Swap6",          //            0x95
    "Swap7",          //            0x96
    "Swap8",          //            0x97
    "Swap9",          //            0x98
    "Swap10",         //           0x99
    "Swap11",         //           0x9a
    "Swap12",         //           0x9b
    "Swap13",         //           0x9c
    "Swap14",         //           0x9d
    "Swap15",         //           0x9e
    "Swap16",         //           0x9f
    "Log0",           //             0xa0
    "Log1",           //             0xa1
    "Log2",           //             0xa2
    "Log3",           //             0xa3
    "Log4",           //             0xa4
    "",               //                 0xa5
    "",               //                 0xa6
    "",               //                 0xa7
    "",               //                 0xa8
    "",               //                 0xa9
    "",               //                 0xaa
    "",               //                 0xab
    "",               //                 0xac
    "",               //                 0xad
    "",               //                 0xae
    "",               //                 0xaf
    "",               //                 0xb0
    "",               //                 0xb1
    "",               //                 0xb2
    "",               //                 0xb3
    "",               //                 0xb4
    "",               //                 0xb5
    "",               //                 0xb6
    "",               //                 0xb7
    "",               //                 0xb8
    "",               //                 0xb9
    "",               //                 0xba
    "",               //                 0xbb
    "",               //                 0xbc
    "",               //                 0xbd
    "",               //                 0xbe
    "",               //                 0xbf
    "",               //                 0xc0
    "",               //                 0xc1
    "",               //                 0xc2
    "",               //                 0xc3
    "",               //                 0xc4
    "",               //                 0xc5
    "",               //                 0xc6
    "",               //                 0xc7
    "",               //                 0xc8
    "",               //                 0xc9
    "",               //                 0xca
    "",               //                 0xcb
    "",               //                 0xcc
    "",               //                 0xcd
    "",               //                 0xce
    "",               //                 0xcf
    "",               //                 0xd0
    "",               //                 0xd1
    "",               //                 0xd2
    "",               //                 0xd3
    "",               //                 0xd4
    "",               //                 0xd5
    "",               //                 0xd6
    "",               //                 0xd7
    "",               //                 0xd8
    "",               //                 0xd9
    "",               //                 0xda
    "",               //                 0xdb
    "",               //                 0xdc
    "",               //                 0xdd
    "",               //                 0xde
    "",               //                 0xdf
    "",               //                 0xe0
    "",               //                 0xe1
    "",               //                 0xe2
    "",               //                 0xe3
    "",               //                 0xe4
    "",               //                 0xe5
    "",               //                 0xe6
    "",               //                 0xe7
    "",               //                 0xe8
    "",               //                 0xe9
    "",               //                 0xea
    "",               //                 0xeb
    "",               //                 0xec
    "",               //                 0xed
    "",               //                 0xee
    "",               //                 0xef
    "Create",         //           0xf0
    "Call",           //             0xf1
    "CallCode",       //         0xf2
    "Return",         //           0xf3
    "DelegateCall",   //     0xf4
    "Create2",        //          0xf5
    "",               //                 0xf6
    "",               //                 0xf7
    "",               //                 0xf8
    "",               //                 0xf9
    "StaticCall",     //       0xfa
    "",               //                 0xfb
    "",               //                 0xfc
    "Revert",         //           0xfd
    "Invalid",        //          0xfe
    "SelfDestruct",   //     0xff
];

fn print_preamble(bytes: &[u8]) {
    println!("include \"evm-dafny/src/dafny/evm.dfy\"");
    println!("include \"evm-dafny/src/dafny/evms/berlin.dfy\"");
    println!("import opened Int");
    println!("import opened Opcode");
    println!("import opened Memory");
    println!("import opened Bytecode");
    println!();
    print!("const BYTECODE : seq<u8> := [");
    for i in 0..bytes.len() {
        print!("{:#02x}", bytes[i]);
        if (i + 1) != bytes.len() {
            print!(", ");
        }
    }
    println!("];");
    println!();
    println!("type ValidState = st:EvmState.State | st.OK? && st.WritesPermitted() && st.evm.code == Code.Create(BYTECODE)");
    println!("witness EvmState.OK(EvmState.EVM(Context.Create(0,0,0,0,[],true,0,Context.Block.Info(0,0,0,0,0,0)),");
    println!("           WorldState.Create(map[0:=WorldState.DefaultAccount()]),");
    println!(
        "           Stack.Create(),Memory.Create(),Code.Create(BYTECODE),SubState.Create(),0,0))"
    );
    println!();
    println!("method external_call(sender: u160, st: EvmState.OKState) returns (r:EvmState.State)");
    println!("ensures r.RETURNS? || r.REVERTS? || r.INVALID?");
    println!("ensures r.RETURNS? ==> r.world.Exists(sender) {{");
    println!("\t return EvmState.INVALID(EvmState.INSUFFICIENT_GAS); // dummy");
    println!("}}");
    println!();
    println!("method main(context: Context.T, world: map<u160,WorldState.Account>, gas: nat) returns (st': EvmState.State)");
    println!("requires context.writePermission");
    println!("requires gas > 100000");
    println!("requires context.address in world {{");
    println!("\tvar st := EvmBerlin.Create(context,world,gas,BYTECODE);");
}

fn to_dfy_name(insn: &Instruction) -> String {
    // Determine opcode
    let opcode = insn.opcode(&[]).unwrap();
    //
    OPCODES[opcode as usize].to_string()
}

/// Determine whether or not to split into true basic blocks, or into
/// larger blocks.
const BASIC_BLOCKS: bool = false;

fn gen_proof(bytes: &[u8], overflows: bool) {
    // Disassemble bytes into instructions
    let disasm: Disassembly<AbstractStack<Interval<w256>>> = Disassembly::new(&bytes).build();
    // Convert into instruction stream
    let instructions = disasm.to_vec();
    let mut pc = 0;
    let mut fallthru = true;
    //
    print_preamble(&bytes);
    //
    for insn in &instructions {
        match insn {
            DATA(bytes) => {
                println!("\t// {}", bytes.to_hex_string());
            }
            PUSH(bytes) => {
                let opcode = 0x5f + bytes.len();
                println!("\tst := {}(st,{});", OPCODES[opcode], bytes.to_hex_string());
            }
            JUMPDEST(_) => {
                if fallthru {
                    // Add explicit fallthru
                    println!("\tst := block_{:#08x}(st);", pc);
                    println!("\treturn st;");
                }
                print_block_break(pc, &disasm);
                println!("\tvar st := JumpDest(st');");
            }
            CALL => {
                print_call(pc);
            }
            JUMP => {
                let target = disasm.get_state(pc).peek(0);
                //
                if target.is_constant() {
                    // NOTE: following seems necessary in some cases.
                    println!("\tassume st.IsJumpDest({:#08x});", target.constant());
                    println!("\tst := Jump(st);");
                    println!("\tst := block_{:#08x}(st); return st;", target.constant());
                } else {
                    println!("\t// Unable to resolve JUMP address!");
                    println!("\tassert false;");
                }
            }
            JUMPI => {
                let target = disasm.get_state(pc).peek(0);
                //
                if target.is_constant() {
                    println!("\tvar tmp{} := st.Peek(1);", pc);
                    // NOTE: following seems necessary in some cases.
                    println!("\tassume st.IsJumpDest({:#08x});", target.constant());
                    println!("\tst := JumpI(st);");
                    println!(
                        "\tif tmp{} != 0 {{ st := block_{:#08x}(st); return st;}}",
                        pc,
                        target.constant()
                    );
                    if BASIC_BLOCKS {
                        println!("\tblock_{:#08x}(st);", pc + 1);
                        print_block_break(pc, &disasm);
                        println!("\tvar st := st';");
                    }
                } else {
                    println!("\t// Unable to resolve JUMPI address!");
                    println!("\tassert false;");
                }
            }
            DUP(n) => {
                println!("\tst := Dup(st,{});", n);
            }
            SWAP(n) => {
                println!("\tst := Swap(st,{});", n);
            }
            ADD => {
                if overflows {
                    println!("\tassert (st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256);");
                }
                println!("\tst := Add(st);");
            }
            MUL => {
                if overflows {
                    println!("\tassert (st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256);");
                }
                println!("\tst := Mul(st);");
            }
            SUB => {
                if overflows {
                    println!("\tassert st.Peek(1) <= st.Peek(0);");
                }
                println!("\tst := Sub(st);");
            }
            _ => {
                println!("\tst := {}(st);", to_dfy_name(&insn));
            }
        }
        pc = pc + insn.length(&[]);
        if fallthru && !insn.fallthru() {
            println!("\treturn st;");
        }
        fallthru = insn.fallthru();
    }
    // Print terminator (if necessary)
    if fallthru {
        println!("\tassert st.OK?;");
    }
    //
    println!("}}");
}

fn print_block_break(pc: usize, disasm: &Disassembly<AbstractStack<Interval<w256>>>) {
    let st = disasm.get_state(pc);
    // Determine stack height on entry
    let stack = st.stack;
    let stack_height = stack.len();
    //
    println!("}}");
    println!();
    println!("method block_{:#08x}(st': ValidState) returns (st'': EvmState.State)", pc);
    println!("requires st'.PC() == {:#08x}", pc);
    if stack_height.is_constant() {
        println!("requires st'.Operands() == {}", stack_height.unwrap());
    } else {
        println!(
            "requires st'.Operands() >= {} && st'.Operands() <= {}",
            stack_height.start, stack_height.end
        );
    }
    //
    for i in 0..stack.values().len() {
        let ith = stack.peek(i);
        //
        if !ith.is_top() {
            if ith.is_constant() {
                println!("requires st'.Peek({}) == {:#08x}", i, ith.constant());
            } else {
                println!(
                    "requires st'.Peek({}) >= {:#08x} && st'.Peek({}) <= {:#08x}",
                    i, ith.start, i, ith.end
                );
            }
        }
    }
    // Done
    println!("{{");
}

fn print_call(pc: usize) {
    println!("\tst := Call(st);");
    println!("\t{{");
    println!("\t\tvar inner := st.CallEnter(1);");
    println!("\t\tif inner.OK? {{ inner := external_call(st.sender,inner); }}");
    println!("\t\tst := st.CallReturn(inner);");
    println!("\t}}");
}

// This is a hack script for now.
fn main() {
    //let args: Vec<String> = env::args().collect();
    let matches = Command::new("devmpg")
        .about("DafnyEvm Proof Generation Tool")
        .arg(Arg::new("args"))
        .arg(Arg::new("overflow").long("overflows"))
        .get_matches();
    // Extract arguments
    let overflows = matches.is_present("overflow");
    let args: Vec<_> = matches.get_many::<String>("args").unwrap().collect();
    // Done
    for arg in args {
        // Parse hex string into bytes
        let bytes = arg.from_hex_string().unwrap();
        gen_proof(&bytes, overflows);
    }
}
