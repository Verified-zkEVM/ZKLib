/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ArkLib.Data.Math.Basic
import ArkLib.CommitmentScheme.Basic
import Mathlib.Data.Vector.Snoc

/-!
# Inductive Merkle Trees

This file implements Merkle Trees. In contrast to the other Merkle tree implementation in
`ArkLib.CommitmentScheme.MerkleTree`, this one is defined inductively.

## Notes & TODOs

We want this treatment to be as comprehensive as possible. In particular, our formalization
should (eventually) include all complexities such as the following:

- Multi-instance extraction & simulation
- Dealing with arbitrary trees (may have arity > 2, or is not complete)
- Path pruning optimization
-/

namespace BinaryTree

/-!
# Binary Trees

This section contains datatypes for working with binary trees.

There

-/

/--
Inductive data type for a binary tree skeleton.
A skeleton is a binary tree without values, used to represent the structure of the tree.
-/
inductive Skeleton where
  | leaf : Skeleton
  | internal : Skeleton → Skeleton → Skeleton

/-- Type of indices of leaves of a skeleton -/
inductive SkeletonLeafIndex : Skeleton → Type
  | ofLeaf : SkeletonLeafIndex Skeleton.leaf
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonLeafIndex left) :
      SkeletonLeafIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonLeafIndex right) :
      SkeletonLeafIndex (Skeleton.internal left right)

/-- Type of indices of any node of a skeleton -/
inductive SkeletonNodeIndex : Skeleton → Type
  | ofLeaf : SkeletonNodeIndex Skeleton.leaf
  | ofInternal {left right} :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofLeft {left right : Skeleton} (idxLeft : SkeletonNodeIndex left) :
      SkeletonNodeIndex (Skeleton.internal left right)
  | ofRight {left right : Skeleton} (idxRight : SkeletonNodeIndex right) :
      SkeletonNodeIndex (Skeleton.internal left right)

/-- Construct a `SkeletonLeafIndex` from a `SkeletonNodeIndex` -/
def SkeletonLeafIndex.toNodeIndex {s : Skeleton} (idx : SkeletonLeafIndex s) :
    SkeletonNodeIndex s :=
  match idx with
  | SkeletonLeafIndex.ofLeaf => SkeletonNodeIndex.ofLeaf
  | SkeletonLeafIndex.ofLeft idxLeft =>
    SkeletonNodeIndex.ofLeft (SkeletonLeafIndex.toNodeIndex idxLeft)
  | SkeletonLeafIndex.ofRight idxRight =>
    SkeletonNodeIndex.ofRight (SkeletonLeafIndex.toNodeIndex idxRight)

/-- Depth of a SkeletonNodeIndex -/
def SkeletonNodeIndex.depth {s : Skeleton} : SkeletonNodeIndex s → Nat
  | SkeletonNodeIndex.ofLeaf => 0
  | SkeletonNodeIndex.ofInternal => 0
  | SkeletonNodeIndex.ofLeft idxLeft => idxLeft.depth + 1
  | SkeletonNodeIndex.ofRight idxRight => idxRight.depth + 1

-- Analogous to `Cache`
/--
A binary tree with values stored in internal nodes.
-/
inductive InternalDataTree (α : Type) : Skeleton → Type
  | leaf : InternalDataTree α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : InternalDataTree α left)
      (rightData : InternalDataTree α right) : InternalDataTree α (Skeleton.internal left right)
  deriving Repr

/--
A binary tree with values stored at leaves.
-/
inductive LeafDataTree (α : Type) : Skeleton → Type
  | leaf (value : α) : LeafDataTree α Skeleton.leaf
  | internal {left right} (leftData : LeafDataTree α left) (rightData : LeafDataTree α right) :
      LeafDataTree α (Skeleton.internal left right)
  deriving Repr

/--
A binary tree with values stored at both leaves and internal nodes.
-/
inductive FullDataTree (α : Type) : Skeleton → Type
  | leaf (value : α) : FullDataTree α Skeleton.leaf
  | internal {left right} (value : α)
      (leftData : FullDataTree α left)
      (rightData : FullDataTree α right) :
      FullDataTree α (Skeleton.internal left right)

/-- Get the root value of a InternalDataTree. -/
def getRoot {s} {α : Type} : FullDataTree α s → α
  | FullDataTree.leaf value => value
  | FullDataTree.internal value _ _ => value

-- TODO not sure I got this right
def SkeletonNodeIndex.parent {s : Skeleton} (idx : SkeletonNodeIndex s) : Option (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonNodeIndex.ofLeaf => none
  | SkeletonNodeIndex.ofInternal => none
  | SkeletonNodeIndex.ofLeft (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofLeft (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofLeft idxLeft =>
    idxLeft.parent.map (SkeletonNodeIndex.ofLeft)
  | SkeletonNodeIndex.ofRight (.ofLeaf) => some .ofInternal
  | SkeletonNodeIndex.ofRight (.ofInternal) => some .ofInternal
  | SkeletonNodeIndex.ofRight idxRight =>
    idxRight.parent.map (SkeletonNodeIndex.ofRight)

lemma SkeletonNodeIndex.parent_of_depth_zero {s : Skeleton} (idx : SkeletonNodeIndex s) (h : idx.depth = 0) :
    parent idx = none := by
  cases idx with
  | ofLeaf => rfl
  | ofInternal => rfl
  | ofLeft idxLeft =>
    unfold depth at h
    simp_all
  | ofRight idxRight =>
    unfold depth at h
    simp_all

lemma SkeletonNodeIndex.parent_of_depth_succ {s : Skeleton} (idx : SkeletonNodeIndex s) (n : ℕ) (h : idx.depth = n + 1) :
    idx.parent.map depth = some n := by
  cases idx with
  | ofLeaf => sorry
  | ofInternal => sorry
  | ofLeft idxLeft => sorry
  | ofRight idxRight => sorry

/--
Given a `Skeleton`, and a node index of the skeleton, return a list of node indices which are the ancestors of the node.
-/
def SkeletonNodeIndex.findAncestors {s : Skeleton} (idx : SkeletonNodeIndex s) : List (SkeletonNodeIndex s) :=
  idx ::

/--
Given a `Skeleton`, and a leaf index of the skeleton, return a list of node indices which are the ancestors of the leaf.
-/
def findAncestors {s : Skeleton} (idx : SkeletonLeafIndex s) : List (SkeletonNodeIndex s) :=
  match idx with
  | SkeletonLeafIndex.ofLeaf => .ofLeaf :: []
  | SkeletonLeafIndex.ofLeft idxLeft =>
    (idxLeft.toNodeIndex :: (findAncestors idxLeft)).map (SkeletonNodeIndex.ofLeft)
  | SkeletonLeafIndex.ofRight idxRight =>
    idxRight.toNodeIndex.ofRight :: (findAncestors idxRight).map (SkeletonNodeIndex.ofRight)

end BinaryTree

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable (α : Type)

/-- Define the domain & range of the (single) oracle needed for constructing a Merkle tree with
    elements from some type `α`.

  We may instantiate `α` with `BitVec n` or `Fin (2 ^ n)` to construct a Merkle tree for boolean
  vectors of length `n`. -/
@[reducible]
def spec : OracleSpec Unit := fun _ => (α × α, α)

@[simp]
lemma domain_def : (spec α).domain () = (α × α) := rfl

@[simp]
lemma range_def : (spec α).range () = α := rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Example: a single hash computation -/
def singleHash (left : α) (right : α) : OracleComp (spec α) α := do
  let out ← query (spec := spec α) () ⟨left, right⟩
  return out

variable {α : Type}


-- /-- Find the path from root to a leaf with the given value. -/
-- def findPath [DecidableEq α] (a : α) : BinaryTree α → Option (List Bool)
--   | BinaryTree.nil => none
--   | BinaryTree.node _ left right =>
--     match findPath a left with
--     | some path => some (false :: path)
--     | none =>
--       match findPath a right with
--       | some path => some (true :: path)
--       | none => none

-- /-- Helper function to get the proof for a value at a given path. -/
-- def getProofHelper [DecidableEq α] : List Bool → BinaryTree α → List α
--   | _, BinaryTree.nil => []
--   | _, BinaryTree.leaf _ => []
--   | [], BinaryTree.node _ _ _ => []
--   | false :: rest, BinaryTree.node _ l r =>
--     match getRoot r with
--     | none => getProofHelper rest l
--     | some v => v :: getProofHelper rest l
--   | true :: rest, BinaryTree.node _ l r =>
--     match getRoot l with
--     | none => getProofHelper rest r
--     | some v => v :: getProofHelper rest r

def buildMerkleTree_with_hash (leaf_tree : LeafTree α) (hashFn : α → α → α) : (BinaryTree α) :=
  match leaf_tree with
  | LeafTree.leaf a => BinaryTree.node a none
  | LeafTree.node left right =>
    let leftTree := buildMerkleTree_with_hash left hashFn
    let rightTree := buildMerkleTree_with_hash right hashFn
    let root_hash := hashFn (getRoot leftTree) (getRoot rightTree)
    BinaryTree.node root_hash (some (leftTree, rightTree))

/-- Build the full Merkle tree, returning the cache -/
def buildMerkleTree (leaf_tree : LeafTree α) : OracleComp (spec α) (BinaryTree α) :=
  match leaf_tree with
  | LeafTree.leaf a => do
    return BinaryTree.node a none
  | LeafTree.node left right => do
    let leftTree ← buildMerkleTree left
    let rightTree ← buildMerkleTree right
    let rootHash ← singleHash α (getRoot leftTree) (getRoot rightTree)
    return BinaryTree.node rootHash (some (leftTree, rightTree))

/-- Generate a Merkle proof for a leaf with value 'a'.
    The proof consists of the sibling hashes needed to recompute the root. -/
def generateProof [DecidableEq α] (a : α) (tree : BinaryTree α) : Option (List α) :=
  match findPath a tree with
  | none => none
  | some path => some (getProofHelper path tree)

/-- Verify a Merkle proof that a value 'a' is in the tree with root 'root'.
    The 'proof' contains sibling hashes, and 'path' is the position (left/right) at each level. -/
def verifyProof [DecidableEq α] (hashFn : α → α → α) (a : α) (root : α)
    (proof : List α) (path : List Bool) : Bool :=
  let rec verify (current : α) (p : List α) (dirs : List Bool) : Bool :=
    match p, dirs with
    | [], [] => current = root
    | sibling :: restProof, dir :: restPath =>
      let nextHash := if dir then hashFn sibling current else hashFn current sibling
      verify nextHash restProof restPath
    | _, _ => false -- Proof and path lengths don't match
  verify a proof path
