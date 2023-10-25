use evmil::bytecode::{Assemble, Assembly, Instruction, StructuredSection};
use evmil::analysis::{BlockGraph};
use evmil::util::{dominators,SortedVec};
use crate::block::{Block,BlockSequence};

type DomSet = SortedVec<usize>;

/// An almagamation of information as required to split a given
/// instruction sequence into distincted regions of ownership.
pub struct ControlFlowGraph<'a> {
    /// Code section identifier
    cid: usize,
    /// Underlying digraph representation
    graph: BlockGraph<'a>,
    /// Computed dominators set
    dominators: Vec<DomSet>,
    /// Set of designated owners.  These are absolute byte offsets
    /// within the original instruction stream.
    roots: Vec<usize>,
    /// The designated block decomposition.  Observe that,
    /// unfortunately, this decomposition may differ from the
    /// decompisition used in the graph.
    blocks: BlockSequence
}

impl<'a> ControlFlowGraph<'a> {
    pub fn new(cid: usize, blocksize: usize, insns: &'a [Instruction]) -> Self {
        // Construct graph
        let graph = BlockGraph::from(insns);
        // Compute dominators
        let dominators = dominators(&graph);
        // Determine block decomposition based on the given block size.
        let blocks = BlockSequence::from_insns(blocksize,insns);        
        // Done
        Self{cid,graph,dominators,blocks, roots: Vec::new()}
    }

    pub fn cid(&self) -> usize {
        self.cid
    }
    
    pub fn roots(&self) -> &[usize] {
        &self.roots
    }
    
    pub fn add_root(&mut self, pc: usize) {
        self.roots.push(pc);
    }

    /// Get the set of owned blocks for a given root (i.e. absolute
    /// byte offset within the original bytecode sequence).
    pub fn get_owned(&self, root: usize) -> Vec<Block> {
        let mut blks = Vec::new();
        // Iterate each block and determine whether its owned or not.
        for blk in self.blocks.iter() {
            if self.owns(root,blk) {
                blks.push(blk.clone());
            }
        }
        // Done
        blks
    }

    /// Determine whether a given `root` owns a given block `blk`.  A
    /// root owns a block if that block is dominated by the root and
    /// there is no other internal root which owns the block. Here,
    /// roots are absolute byte offset within the original bytecode
    /// sequence.
    pub fn owns(&self, root: usize, blk: &Block) -> bool {
        print!("Does {root} own {}? ",blk.pc());
        // Dominator check
        if self.dominates(root,blk.pc()) {
            // Internal owner checker
            for r in &self.roots {
                if *r != root && self.dominates(*r,blk.pc()) && self.dominates(root,*r) {
                    // An inner root dominates this block.                    
                    println!("NOPE (1)");
                    return false;
                }
            }
            println!("YUP");            
            true
        } else {
            // Nope
            println!("NOPE (2)");
            false
        }
    }

    /// Check whether a given bytecode offset dominates another.
    pub fn dominates(&self, parent: usize, child: usize) -> bool {
        let gp = self.graph.nodes().lookup_pc(parent);
        let gc = self.graph.nodes().lookup_pc(child);
        // Dominator check
        let r = self.dominators[gc].contains(gp);
        println!("Does {parent} ({gp}) dominate {child} ({gc})? {r}");
        r
    }
}
