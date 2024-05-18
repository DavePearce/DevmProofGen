mod analysis;
mod block;
mod cfg;
mod opcodes;
mod printer;

use std::env;
use std::fs;
use std::fs::File;
use std::path::Path;
use std::io::{BufWriter,Write};
use std::collections::HashMap;
use std::error::Error;
use clap::{Arg, Command};
use serde::Deserialize;
use evmil::analysis::{BlockGraph,insert_havocs,trace};
use evmil::bytecode::{Assemble, Assembly, Instruction, StructuredSection};
use evmil::bytecode::Instruction::*;
use evmil::util::{dominators,FromHexString,SortedVec,ToHexString};
use analysis::{State};
use block::{Block,BlockSequence,Bytecode,PreconditionFn};
use cfg::ControlFlowGraph;
use printer::*;

fn main() -> Result<(), Box<dyn Error>> {
    //let args: Vec<String> = env::args().collect();
    let matches = Command::new("devmpg")
        .about("DafnyEvm Proof Generation Tool")
        .arg(Arg::new("overflow").long("overflows"))        
        .arg(Arg::new("blocksize")
             .long("blocksize")
             .value_name("SIZE")
             .value_parser(clap::value_parser!(usize))
             .default_value("65535"))
        .arg(Arg::new("outdir").long("outdir").short('o').value_name("DIR"))
        .arg(Arg::new("devmdir").long("devmdir").value_name("DIR").default_value("evm-dafny"))
        .arg(Arg::new("debug").long("debug"))	
        .arg(Arg::new("minimise").long("minimise"))
        .arg(Arg::new("minimise-all").long("minimise-all"))	
        .arg(Arg::new("split").long("split").value_name("json-file"))
        .arg(Arg::new("target").required(true))        
        .get_matches();
    // Extract arguments
    let target = matches.get_one::<String>("target").unwrap();   
    // Configure settings
    let settings = Config{
	outdir: matches.get_one("outdir").map(|s: &String| s.clone()),
	devmdir: matches.get_one::<String>("devmdir").unwrap().clone(),
	prefix: default_prefix(target),
	checks: overflow_checks, // for now
	blocksize: *matches.get_one("blocksize").unwrap(),
	debug: matches.is_present("debug"),
	minimise_requires: matches.is_present("minimise")||matches.is_present("minimise-all"),
	minimise_internal: matches.is_present("minimise-all"),
    };
    let overflows = matches.is_present("overflow");
    // Read from asm file
    let hex = fs::read_to_string(target)?;
    let bytes = hex.trim().from_hex_string()?;    
    // Setup configuration
    let mut roots = HashMap::new();    
    // Configure roots
    roots.insert((0,0),"main".to_string());
    // Check if a config is provided
    if matches.is_present("split") {
        let split_filename = matches.get_one::<String>("split").unwrap();
        let split_file = fs::read_to_string(split_filename)?;        
        let cf: ConfigFile = serde_json::from_str(&split_file)?;
        //
        for (n,hs) in cf.functions {
            // Strip off leader
            let ths = hs.trim_start_matches("0x");
            let pc = usize::from_str_radix(ths,16)?;
            roots.insert((0,pc),n);
        }
    }    
    // Disassemble bytes into instructions    
    let mut contract = Assembly::from_legacy_bytes(&bytes);    
    // Infer havoc instructions
    contract = infer_havoc_insns(contract);
    // Deconstruct into sequences
    let mut cfgs = deconstruct(&contract,&settings);
    // Configure roots
    for (c,r) in roots.keys() {
        cfgs[*c].add_root(*r);
    }
    // Group subsequences
    let groups = group(roots,&cfgs);
    // Set output directory
    configure_outdir(&settings.outdir);    
    write_headers(&contract,&settings);
    // Write files
    write_groups(groups,&settings);
    // Done
    Ok(())
}

fn default_prefix(name: &str) -> String {
    let filename = Path::new(name).file_stem().unwrap().to_str().unwrap();
    filename.replace(".","_")
}

fn configure_outdir(outdir: &Option<String>) {
    // Create output directory
    match outdir {
        None => {}
        Some(d) => {
            fs::create_dir_all(d);
            env::set_current_dir(d);            
        }
    };
}

#[derive(Clone,Debug)]
struct Config {
    /// Prefix to use when generating files.
    prefix: String,
    /// Determines where generated files should be placed.
    outdir: Option<String>,
    /// Identifies the path to the `evm-dafny` repository, so that can
    /// be included directly.
    devmdir: String,
    /// Determines what checks should be applied to the disassembled bytecode.
    checks: PreconditionFn,
    /// Determines a limit on how many bytecodes to include in each
    /// distinct block.
    blocksize: usize,
    /// Signals whether or not to generate debug information around
    /// minimisation.
    debug: bool,
    /// Signals whether or not to use mimimisation on `requires`
    /// clauses.
    minimise_requires: bool,
    /// Signals whether or not to minimise the internal stack/memory
    /// information reported as comments.
    minimise_internal: bool,
    
}

#[derive(Debug, Deserialize)]
struct PublicFunction {
    /// Name given for this code root (e.g. name of the public
    /// function it represents).
    name: String,
    /// Code id for this root (i.e. which code section this root
    /// applies to).
    cid: usize,
    /// Absolute byte offset within code section which demarks the
    /// start of this function.
    pc: usize 
}

#[derive(Debug, Deserialize)]
struct ConfigFile {
    functions: HashMap<String,String>
}

struct BlockGroup {
    id: usize,
    name: String,
    blocks: Vec<Block>,
    deps: Vec<usize>
}

type DomSet = SortedVec<usize>;

// Given an assembly, deconstruct it into a set of blocks of a given
// maximum size.
fn deconstruct<'a>(contract: &'a Assembly, settings: &'a Config) -> Vec<ControlFlowGraph<'a>> {
    let blocksize = settings.blocksize;
    let mut cfgs = Vec::new();
    //
    for (i,s) in contract.iter().enumerate() {
        match s {
            StructuredSection::Code(insns) => {
                let mut cfg = ControlFlowGraph::new(i,blocksize,insns.as_ref(), settings.checks);
                cfgs.push(cfg);
            }
            StructuredSection::Data(bytes) => {
                // Nothing (for now)
            }
        }
    }
    //
    cfgs
}

// Given a sequence of blocks, generate a set of block groups.
fn group(roots: HashMap<(usize,usize),String>, cfgs: &[ControlFlowGraph]) -> Vec<BlockGroup> {
    let mut groups = Vec::new();
    //
    for cfg in cfgs { groups.extend(split(&roots,cfg)); }
    //
    groups
}

/// Split a given sequence of blocks (in the same code segment) upto
/// into one or more groups.
fn split(roots: &HashMap<(usize,usize),String>, cfg: &ControlFlowGraph) -> Vec<BlockGroup> {
    let cid = cfg.cid();
    let mut groups = Vec::new();
    // Split out groups
    for r in cfg.roots() {
        let blocks = cfg.get_owned(*r);
        let name = roots.get(&(cid,*r)).unwrap().clone();
        groups.push(BlockGroup{id: cid, name, blocks, deps: Vec::new()});
    }
    // Add utility group (if applicable)
    let remainder = determine_remainder(&groups,&cfg);
    //
    if remainder.len() > 0 {
        // Yes, applicable
        groups.push(BlockGroup{
            id: cid,
            name: "util".to_string(),
            blocks: remainder,
            deps: Vec::new()
        });
    }
    // Determine dependencies
    for i in 0..groups.len() {
        groups[i].deps = dependencies(i,&groups, cfg);
    }
    //
    groups
}

/// Calculate the dependencies for the `ith` group in a give set of
/// groups.
fn dependencies(i: usize, groups: &[BlockGroup], cfg: &ControlFlowGraph) -> Vec<usize> {
    let ith = &groups[i];
    let mut deps = Vec::new();
    //
    for j in 0..groups.len() {
        let jth = &groups[j];
        if i != j && touches_any(cfg,&ith.blocks,&jth.blocks) {
            deps.push(j);
        }
    }
    //
    deps
}

/// Identify all blocks which have not been allocated to a group.
/// These constitute the "remainder".  They are blocks which are not
/// dominated by any root (except the entry) but are reachable by one
/// or more internal roots.  As such, they need to be put into a
/// catch-all utility file.
fn determine_remainder(groups: &[BlockGroup], cfg: &ControlFlowGraph) -> Vec<Block> {
    let mut blks = SortedVec::new();
    // Initialise remainder
    for b in cfg.blocks() { blks.insert(b.pc()); }
    // Subtract everything allocated to a group
    for g in groups {
        for b in &g.blocks { blks.remove(&b.pc()); }
    }
    // Is there anything left?
    let mut rem = Vec::new();
    //
    for b in cfg.blocks() {
        if blks.contains(b.pc()) {
            rem.push(b.clone());
        }
    }    
    // Done
    rem
}

/// Check whether any node from one set touches any other node in
/// another set.
fn touches_any(cfg: &ControlFlowGraph, from: &[Block], to: &[Block]) -> bool {
    for f in from {
        for t in to {
            if cfg.touches(f.pc(),t.pc()) {
                return true;
            }
        }
    }
    false
}    

/// Convert each block group into a sequence of one or more files
/// using a given prefix.
fn write_groups(groups: Vec<BlockGroup>, settings: &Config) -> Result<(), Box<dyn Error>> {
    let devmdir = &settings.devmdir;
    let prefix = &settings.prefix;
    //
    for i in 0..groups.len() {
        let g = &groups[i];
        let filename = format!("{prefix}_{}_{}.dfy",g.id,g.name);
        let header = format!("{prefix}_{}_header.dfy",g.id);        
        println!("Writing {filename}");
        let mut f = BufWriter::new(File::create(filename)?);
        writeln!(f,"include \"{devmdir}/src/dafny/evm.dfy\"");
        writeln!(f,"include \"{devmdir}/src/dafny/core/code.dfy\"");        
        writeln!(f,"include \"{header}\"");
        for d in &g.deps {
            let dep = format!("{prefix}_{}_{}.dfy",g.id,&groups[*d].name);
            writeln!(f,"include \"{dep}\"");            
        }
        writeln!(f,"");
        writeln!(f,"module {} {{",g.name);
        writeln!(f,"\timport opened Opcode");
        writeln!(f,"\timport opened Code");
        writeln!(f,"\timport opened Memory");
        writeln!(f,"\timport opened Bytecode");
        writeln!(f,"\timport opened Header");
        for d in &g.deps {
            writeln!(f,"\timport opened {}",&groups[*d].name);            
        }        
        // Write out imports for dependencies
        writeln!(f,"");                
        // Construct block printer
        let mut printer = BlockPrinter::new(g.id,&mut f,settings);
        //
        for blk in &g.blocks { printer.print_block(&blk); }
        writeln!(f,"}}");
    }
    Ok(())
}
 
/// Write out header files for all bytecode sections.
fn write_headers(contract: &Assembly, settings: &Config) -> Result<(), Box<dyn Error>> {
    let devmdir = &settings.devmdir;    
    let prefix = &settings.prefix;
    //
    for (i,s) in contract.iter().enumerate() {
        match s {
            StructuredSection::Code(insns) => {
                let filename = format!("{prefix}_{}_header.dfy",i);
                println!("Writing {filename}");
                let mut f = BufWriter::new(File::create(filename)?);
                writeln!(f,"include \"{devmdir}/src/dafny/evm.dfy\"")?;
                writeln!(f,"include \"{devmdir}/src/dafny/state.dfy\"")?;               
                writeln!(f,"")?;
                writeln!(f,"module Header {{")?;
                writeln!(f,"\timport opened Int");
                writeln!(f,"\timport EvmState");
                writeln!(f,"");                                
                writeln!(f,"\ttype u256 = Int.u256");
                writeln!(f,"\tconst MAX_U256 : nat := Int.MAX_U256");
                writeln!(f,"");                
                write_bytecode(&mut f, insns, i);
                // for now
                write_external_call(&mut f);
                writeln!(f,"}}")?;
            }
            StructuredSection::Data(bytes) => {
                // Nothing (for now)
            }
        }
    }
    Ok(())
}

/// Write out the contract bytecode as an array of bytes.
fn write_bytecode<T:Write>(mut f: T, insns: &[Instruction], id: usize) {
    // Convert instructions into bytes
    let mut bytes = insns.assemble();   
    //
    write!(f,"\tconst BYTECODE_{id} : seq<u8> := [");
    //
    for i in 0..bytes.len() {
        if i%8 == 0 { write!(f,"\n\t\t"); }
        write!(f,"{:#02x}", bytes[i]);
        if (i + 1) != bytes.len() {
            write!(f,", ");
        }
    }
    writeln!(f,"\n\t]");
}

fn write_external_call<T:Write>(mut f: T) {
    writeln!(f,"\tmethod external_call(sender: u160, st: EvmState.ExecutingState) returns (r:EvmState.TerminatedState)");
    writeln!(f,"\tensures r.RETURNS? ==> r.world.Exists(sender) {{");
    writeln!(f,"\t\treturn EvmState.ERROR(EvmState.INSUFFICIENT_GAS); // dummy");
    writeln!(f,"\t}}");
}


// ===================================================================
// Helpers
// ===================================================================

fn infer_havoc_insns(mut asm: Assembly) -> Assembly {
    // This could probably be more efficient :)
    let sections = asm.iter_mut().map(|section| {
        match section {
            StructuredSection::Code(ref mut insns) => {    
                let ninsns = insert_havocs(insns.clone());
	        StructuredSection::Code(ninsns)
            }
            _ => section.clone()
        }
    }).collect();
    // 
    Assembly::new(sections)
}

/// Add assertions to check against overflow / underflow in generated
/// bytecode.
fn overflow_checks(insn: &Instruction, codes: &mut Vec<Bytecode>) {
    let s = match insn {
        ADD => "(st.Peek(0) + st.Peek(1)) <= (MAX_U256 as u256)",
        MUL => "(st.Peek(0) * st.Peek(1)) <= (MAX_U256 as u256)",
        SUB => "st.Peek(1) <= st.Peek(0)",
        _ => {
            // Do nothing in other cases
            return;
        }
    };
    codes.push(Bytecode::Assert(vec![0,1],s.to_string()));
}
