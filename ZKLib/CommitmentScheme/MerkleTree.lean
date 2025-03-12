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

#check Tree

variable (α : Type)

/-- Define the domain & range of the (single) oracle needed for constructing a Merkle tree with
  elements from some type `α`. We may instantiate `α` with `BitVec n` or `Fin (2 ^ n)` to construct
  a Merkle tree for boolean vectors of length `n`. -/
def oracleSpec : OracleSpec Unit := fun _ => (α × α, α)
  -- domain _ := α × α
  -- range _ := α
  -- domain_decidableEq' := inferInstance
  -- range_decidableEq' := inferInstance
  -- range_inhabited' := inferInstance
  -- range_fintype' := inferInstance

@[simp]
lemma domain_def : (oracleSpec α).domain () = (α × α) := rfl

@[simp]
lemma range_def : (oracleSpec α).range () = α := rfl

section

variable [DecidableEq α] [Inhabited α] [Fintype α]

/-- Example: a single hash computation -/
def singleHash (left : α) (right : α) : OracleComp (oracleSpec α) α := do
  let out ← query (spec := oracleSpec α) () ⟨left, right⟩
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
    OracleComp (oracleSpec α) (List.Vector α (2 ^ n)) := do
  let leaves : List.Vector α (2 ^ n * 2) := by rwa [pow_succ] at leaves
  -- Pair up the leaves to form pairs
  let pairs : List.Vector (α × α) (2 ^ n) :=
    List.Vector.ofFn (fun i =>
      (leaves.get ⟨2 * i, by omega⟩, leaves.get ⟨2 * i + 1, by omega⟩))
  -- Hash each pair to get the next layer
  let hashes : List.Vector α (2 ^ n) ←
    List.Vector.mmap (fun ⟨left, right⟩ => query (spec := oracleSpec α) () ⟨left, right⟩) pairs
  return hashes

/-- Build the full Merkle tree, returning the cache -/
def buildMerkleTree (α) (n : ℕ) (leaves : List.Vector α (2 ^ n)) :
    OracleComp (oracleSpec α) (Cache α n) := do
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
    getRoot α <$> buildMerkleTree α 1 ⟨[a, b], rfl⟩ = (query (spec := oracleSpec α) () (a, b)) := by
  simp [buildMerkleTree, buildLayer, List.Vector.ofFn, List.Vector.head, List.Vector.get]
  unfold Cache.cons getRoot
  simp [map_bind, Fin.reverseInduction]

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
  `root`. -/
def verifyProof {n : ℕ} (i : Fin (2 ^ n)) (leaf : α) (root : α) (proof : List.Vector α n) :
    OracleComp (oracleSpec α) Bool := do
  if h : n = 0 then
    -- When we are at the root, just check whether `leaf` is equal to the root
    return leaf = root
  else
    -- Get the sign bit of `i`
    let signBit := i.val % 2
    -- Show that `i / 2` is in `Fin (2 ^ (n - 1))`
    let i' : Fin (2 ^ (n - 1)) := i.val / 2
    if signBit = 0 then
      -- `i` is a left child
      let newLeaf ← query (spec := oracleSpec α) () ⟨leaf, proof.get ⟨n - 1, by omega⟩⟩
      verifyProof i' newLeaf root (proof.drop 1)
    else
      -- `i` is a right child
      let newLeaf ← query (spec := oracleSpec α) () ⟨proof.get ⟨n - 1, by omega⟩, leaf⟩
      verifyProof i' newLeaf root (proof.drop 1)

-- theorem completeness (leaves : Vector α (2 ^ n)) (i : Fin (2 ^ n)) :
--   verifyMerkleProof i leaf (createMerkleProof i cache) = pure true := sorry

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

-- /-- Building the next layer of a Merkle tree, as an oracle computation. -/
-- def buildLayer (m : Nat) (leaves : Vector (α × α) (2 ^ m)) :
--     OracleComp (oracleSpec α) (Vector α (2 ^ m)) :=
--   (Vector.ofFn (n := 2 ^ m) (fun i => i)).mmap
--     fun i => query (spec := oracleSpec α) () (leaves.get i)

-- /-- Building the Merkle tree from the bottommost layer to the root. -/
-- def build (m : Nat) (leaves : Vector α (2 ^ m)) : OracleComp (oracleSpec α) α := match m with
--   | 0 => pure (leaves.get 0)
--   | m + 1 => do
--     have : 2 ^ (m + 1) = 2 * 2 ^ m := by omega
--     let leaves := by rw [this] at leaves; exact leaves
--     let leavesPair := Vector.chunkPairwise leaves
--     let nextLayer ← buildLayer α m leavesPair
--     return ← build m nextLayer

end MerkleTree
