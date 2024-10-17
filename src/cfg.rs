use evmil::bytecode::{Assemble, Assembly,BlockVec, Instruction, StructuredSection};
use evmil::analysis::{BlockGraph};
use evmil::util::{dominators,SortedVec,transitive_closure};
use crate::block::{Block,BlockSequence,PreconditionFn};

type DomSet = SortedVec<usize>;

/// An almagamation of information as required to split a given
/// instruction sequence into distincted regions of ownership.
pub struct ControlFlowGraph<'a> {
    /// Code section identifier
    cid: usize,
    /// Underlying digraph representation
    graph: BlockGraph<'a>,
    /// Computed dominators sets.  That is, for each node, the set of
    /// its dominators (including itself).
    dominators: Vec<DomSet>,
    /// Transitive closure.  That is, for each node, the the set of
    /// nodes it can reach (not necessarily including itself).
    reaches: Vec<DomSet>,
    /// Set of designated owners.  These are absolute byte offsets
    /// within the original instruction stream.
    roots: Vec<usize>,
    /// The designated block decomposition.  Observe that,
    /// unfortunately, this decomposition may differ from the
    /// decompisition used in the graph.
    blocks: BlockSequence
}

impl<'a> ControlFlowGraph<'a> {
    pub fn new(cid: usize, blocksize: usize, insns: &'a [Instruction], precheck: PreconditionFn, limit: usize) -> Self {
        // Construct graph
        let graph = match BlockGraph::from_blocks(BlockVec::new(insns),limit) {
	    Ok(graph) => graph,
	    Err(graph) => {
		println!("WARNING: control-flow graph construction was incomplete");
		graph
	    }
	};
        // Compute dominators
        let dominators = dominators(&graph);
        // Compute transitive closure
        let reaches = transitive_closure(&graph);
        // Determine block decomposition based on the given block size.
        let blocks = BlockSequence::from_insns(blocksize,insns,precheck,limit);        
        // Done
        Self{cid,graph,dominators,reaches,blocks, roots: Vec::new()}
    }

    pub fn cid(&self) -> usize {
        self.cid
    }
    
    pub fn roots(&self) -> &[usize] {
        &self.roots
    }

    pub fn blocks(&self) -> &[Block] {
        self.blocks.as_ref()
    }
    
    /// Check whether a given root reaches another in one step
    /// (i.e. touches).
    pub fn touches(&self, from: usize, to: usize) -> bool {
        let f = self.graph.nodes().lookup_pc(from);
        let t = self.graph.nodes().lookup_pc(to);
        self.graph.outgoing(f).contains(t)
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
        // Dominator check
        if self.dominates(root,blk.pc()) {
            // Internal owner checker
            for r in &self.roots {
                if *r != root && self.dominates(root,*r) && self.reaches(*r,blk.pc()) {
                    // An inner root reaches this block, hence it cannot be owned.
                    return false;
                }
            }
            true
        } else {
            false
        }
    }

    /// Check whether a given bytecode offset dominates another.
    pub fn dominates(&self, parent: usize, child: usize) -> bool {
        let gp = self.graph.nodes().lookup_pc(parent);
        let gc = self.graph.nodes().lookup_pc(child);
        // Dominator check
        self.dominators[gc].contains(gp)
    }

    /// Check whether a given node can reach another through one or
    /// more steps.
    pub fn reaches(&self, parent: usize, child: usize) -> bool {        
        let gp = self.graph.nodes().lookup_pc(parent);
        let gc = self.graph.nodes().lookup_pc(child);
        // Reachability check
        parent == child || self.reaches[gp].contains(gc)
    }

    /// Minimise the information retained in this control-flow graph.
    pub fn minimise(&mut self) {
        self.blocks.minimise()
    }
}
