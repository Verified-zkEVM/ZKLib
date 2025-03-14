/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import ZKLib.Data.Math.Operations
import ZKLib.CommitmentScheme.Basic

/-!
  # Merkle Trees as a vector commitment

  ## Notes & TODOs

  We want this treatment to be as comprehensive as possible. In particular, our formalization
  should (eventually) include all complexities such as the following:

  - Multi-instance extraction & simulation
  - Dealing with arbitrary trees (may have arity > 2, or is not complete)
  - Path pruning optimization
-/

namespace MerkleTree

open List OracleSpec OracleComp

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

/-- Cache for Merkle tree. Indexed by `j : Fin (n + 1)`, i.e. `j = 0, 1, ..., n`. -/
def Cache (n : ℕ) := (layer : Fin (n + 1)) → List.Vector α (2 ^ layer.val)

/-- Add a base layer to the cache -/
def Cache.cons (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) (cache : Cache α n) :
    Cache α (n + 1) :=
  -- (motive := fun j => Vector α (2 ^ j.val))
  Fin.reverseInduction leaves (fun layer _ => cache layer)

/-- Compute the next layer of the Merkle tree -/
def buildLayer (n : ℕ) (leaves : List.Vector α (2 ^ (n + 1))) :
    OracleComp (spec α) (List.Vector α (2 ^ n)) := do
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  -- Pair up the leaves to form pairs
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩))
  -- Hash each pair to get the next layer
  let hashes : List.Vector α (2 ^ n) ←
    List.Vector.mmap (fun ⟨left, right⟩ => query (spec := spec α) () ⟨left, right⟩) pairs
  return hashes

/-- Build the full Merkle tree, returning the cache -/
def buildMerkleTree (α) (n : ℕ) (leaves : List.Vector α (2 ^ n)) :
    OracleComp (spec α) (Cache α n) := do
  match n with
  | 0 => do
    return fun j => (by
      rw [Fin.val_eq_zero j]
      exact leaves)
  | n + 1 => do
    let lastLayer ← buildLayer α n leaves
    let cache ← buildMerkleTree α n lastLayer
    return Cache.cons α n leaves cache

/-- Get the root of the Merkle tree -/
def getRoot {n : ℕ} (cache : Cache α n) : α :=
  (cache 0).get ⟨0, by simp⟩

/-- Figure out the indices of the Merkle tree nodes that are needed to
recompute the root from the given leaf -/
def findNeighbors {n : ℕ} (i : Fin (2 ^ n)) (layer : Fin n) :
    Fin (2 ^ (layer.val + 1)) :=
  -- `finFunctionFinEquiv.invFun` gives the little-endian order, e.g. `6 = 011 little`
  -- so we need to reverse it to get the big-endian order, e.g. `6 = 110 big`
  let bits := (Vector.ofFn (finFunctionFinEquiv.invFun i)).reverse
  -- `6 = 110 big`, `j = 1`, we get `neighbor = 10 big`
  let neighbor := (bits.set layer (bits.get layer + 1)).take (layer.val + 1)
  have : min (layer.val + 1) n = layer.val + 1 := by omega
  -- `10 big` => `01 little` => `2`
  finFunctionFinEquiv.toFun (this ▸ neighbor.reverse.get)

end

@[simp]
theorem getRoot_trivial (a : α) : getRoot α <$> (buildMerkleTree α 0 ⟨[a], rfl⟩) = pure a := by
  simp [getRoot, buildMerkleTree, List.Vector.head]

@[simp]
theorem getRoot_single (a b : α) :
    getRoot α <$> buildMerkleTree α 1 ⟨[a, b], rfl⟩ = (query (spec := spec α) () (a, b)) := by
  simp [buildMerkleTree, buildLayer, List.Vector.ofFn, List.Vector.head, List.Vector.get]
  unfold Cache.cons getRoot
  simp [map_flatMap, Fin.reverseInduction]

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Generate a Merkle proof that a given leaf at index `i` is in the Merkle tree. The proof consists
  of the Merkle tree nodes that are needed to recompute the root from the given leaf. -/
def generateProof {n : ℕ} (i : Fin (2 ^ n)) (cache : Cache α n) :
    List.Vector α n :=
  let complement := findNeighbors i
  let proof := List.Vector.ofFn (fun (layer : Fin n) => (cache layer).get (complement layer))
  proof

/-- Verify a Merkle proof `proof` that a given `leaf` at index `i` is in the Merkle tree with given
  `root`.
  Outputs `failure` if the proof is invalid. -/
def verifyProof {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (root : α) (proof : List.Vector α n) :
    OracleComp (spec α) Unit := do
  if h : n = 0 then
    -- When we are at the root, just check whether `leaf` is equal to the root
    guard (leaf = root)
  else
    -- Get the sign bit of `i`
    let signBit := i.val % 2
    -- Show that `i / 2` is in `Fin (2 ^ (n - 1))`
    let i' : Fin (2 ^ (n - 1)) := i.val / 2
    if signBit = 0 then
      -- `i` is a left child
      let newLeaf ← query (spec := spec α) () ⟨leaf, proof.get ⟨n - 1, by omega⟩⟩
      verifyProof i' newLeaf root (proof.drop 1)
    else
      -- `i` is a right child
      let newLeaf ← query (spec := spec α) () ⟨proof.get ⟨n - 1, by omega⟩, leaf⟩
      verifyProof i' newLeaf root (proof.drop 1)

/-- Completeness theorem for Merkle trees: for any full binary tree with `2 ^ n` leaves, and for any
  index `i`, the verifier accepts the opening proof at index `i` generated by the prover. -/
theorem completeness {n : ℕ} (leaves : List.Vector α (2 ^ n)) (i : Fin (2 ^ n)) :
    [ fun ⟨leaf, root, proof⟩ => verifyProof α i leaf root proof = pure () | do
      let cache ← buildMerkleTree α n leaves
      let proof := generateProof α i cache
      return (leaves[i], getRoot α cache, proof) ] = 1 := by
  induction n with
  | zero =>
    simp [buildMerkleTree, getRoot, generateProof, verifyProof]
    have : i = 0 := by aesop
    subst i
    simp [Fin.instGetElemFinVal]
  | succ n ih =>
    simp_all [buildMerkleTree, getRoot, generateProof]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp [buildLayer]
    · intro x _
      exact (ih x ⟨0, by simp⟩).1
    · intro a b path newLeaves h1 h2
      unfold verifyProof
      simp
      -- simp [findNeighbors] at h2
      sorry

-- theorem soundness (i : Fin (2 ^ n)) (leaf : α) (proof : Vector α n) :
--     verifyMerkleProof i leaf proof = pure true →
--     getMerkleRoot (buildMerkleTree n (leaf ::ᵥ proof)) = leaf := sorry

end

section Test

-- 6 = 110_big
-- Third neighbor (`j = 0`): 0 = 0 big
-- Second neighbor (`j = 1`): 2 = 10 big
-- First neighbor (`j = 2`): 7 = 111 big
#eval findNeighbors (6 : Fin (2 ^ 3)) 0
#eval findNeighbors (6 : Fin (2 ^ 3)) 1
#eval findNeighbors (6 : Fin (2 ^ 3)) 2


end Test

end MerkleTree

-- Alternative definition of Merkle tree using inductive type

/-- A binary tree with (possibly null) values stored at both leaf and internal nodes. -/
inductive BinaryTree (α : Type*) where
  | leaf : α → BinaryTree α
  | node : α → BinaryTree α → BinaryTree α → BinaryTree α
  | nil : BinaryTree α
  deriving Inhabited, Repr

-- Example:
--        1
--       / \
--      2   3
--     / \   \
--    4   5   6
--       /
--      7
-- A tree with values at both leaf and internal nodes
def BinaryTree.example : BinaryTree (Fin 10) :=
  .node 1
    (.node 2
      (.leaf 4)
      (.node 5 (.leaf 7) .nil))
    (.node 3
      .nil
      (.leaf 6))

/-- A binary tree where only leaf nodes can have values.

Used as input to Merkle tree construction. -/
inductive LeafTree (α : Type*) where
  | leaf : α → LeafTree α
  | node : LeafTree α → LeafTree α → LeafTree α
  | nil : LeafTree α
deriving Inhabited, Repr

variable {α : Type}

/-- Get the root value of a Merkle tree, if it exists. -/
def getRoot : BinaryTree α → Option α
  | BinaryTree.nil => none
  | BinaryTree.leaf a => some a
  | BinaryTree.node a _ _ => some a

/-- Find the path from root to a leaf with the given value. -/
def findPath [DecidableEq α] (a : α) : BinaryTree α → Option (List Bool)
  | BinaryTree.nil => none
  | BinaryTree.leaf b => if a = b then some [] else none
  | BinaryTree.node _ left right =>
    match findPath a left with
    | some path => some (false :: path)
    | none =>
      match findPath a right with
      | some path => some (true :: path)
      | none => none

/-- Helper function to get the proof for a value at a given path. -/
def getProofHelper [DecidableEq α] : List Bool → BinaryTree α → List α
  | _, BinaryTree.nil => []
  | _, BinaryTree.leaf _ => []
  | [], BinaryTree.node _ _ _ => []
  | false :: rest, BinaryTree.node _ l r =>
    match getRoot r with
    | none => getProofHelper rest l
    | some v => v :: getProofHelper rest l
  | true :: rest, BinaryTree.node _ l r =>
    match getRoot l with
    | none => getProofHelper rest r
    | some v => v :: getProofHelper rest r

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

-- /-- Build a Merkle tree from a list of leaves using a hash function. -/
-- def buildMerkleTree [DecidableEq α] [Inhabited α]
--     (hashFn : α → α → α) (leaves : List α) : BinaryTree α :=
--   -- Find the smallest power of 2 that fits all leaves
--   -- We can estimate 2^n >= leaves.length by using n = ceiling(log2(leaves.length))
--   let n := Nat.ceil (Nat.log 2 (leaves.length + 1)) -- Ceiling of log base 2
--   LeafTree.toMerkleTree hashFn (LeafTree.fromList n leaves)
