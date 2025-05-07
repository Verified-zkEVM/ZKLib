/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # The Algebraic Group Model (With Oblivious Sampling)

We attempt to define the algebraic group model. Our mechanization follows recent papers of Jaeger &
 Mohan [JM24](https://link.springer.com/content/pdf/10.1007/978-3-031-68388-6_2) and Lipmaa,
 Parisella, and Siim [LPS24](https://eprint.iacr.org/2024/994.pdf). -/

class IsPrimeOrderWith (G : Type*) [Group G] (p : ℕ) [Fact (Nat.Prime p)] where
  hCard : Nat.card G = p

class IsPrimeOrder (G : Type*) [Group G] where
  -- hCard : ∃p, IsPrimeOrderWith G p
  hCard : ∃ p, Nat.Prime p ∧ Nat.card G = p

namespace IsPrimeOrder

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact (Nat.Prime p)] [IsPrimeOrder G]

instance : CommGroup G := sorry

-- instance : IsCyclic G := isCyclic_of_prime_card PrimeOrder.hCard

-- instance : Additive G ≃+ ZMod p := sorry

end IsPrimeOrder

open Polynomial

section AGM

/-- A type is **serializable** if it can be encoded and decoded to a bit string.

This is highly similar but inequivalent to other type classes like `ToString` or `Repr`.

A special case of `Encodable` except that we require all encodings have the same bit-length, and do
not require decoding. -/
class Serializable (α : Type*) where
  len : ℕ
  toBitVec : α → BitVec len

/-- A type is **deserializable** if it can be decoded from a bit string of a given length. -/
class Deserializable (α : Type*) where
  len : ℕ
  fromBitVec : BitVec len → Option α

-- #check LinearMap.mk₂'

-- #check LinearMap.BilinForm.linMulLin

-- #check isCyclic_of_prime_card

-- These imply a finite cyclic group of prime order `p`
variable {G : Type*} [Group G] {p : ℕ} [Fact (Nat.Prime p)] (h : Nat.card G = p)

@[ext]
structure GroupRepresentation (prev : List G) (target : G) where
  exponents : List (ZMod p)
  hEq : (prev.zipWith (fun g a => g ^ a.val) exponents).prod = target

-- #print GroupRepresentation

/-- An adversary in the Algebraic Group Model (AGM) may only access group elements via handles.

To formalize this, we let the handles be natural numbers, and assume that they are indices into an
(infinite) array storing potential group elements. -/
def GroupValTable (G : Type*) := Nat → Option G

local instance {α : Type*} : Zero (Option α) where
  zero := none

-- This might be a better abstraction since the type is finite
-- We put `DFinsupp` since it's computable, not sure if really needed (if not we use `Finsupp`)
def GroupVal (G : Type*) := Π₀ _ : Nat, Option G

-- This allows an adversary to perform the group operation on group elements stored at the indices
-- `i` and `j` (if they are both defined), storing the result at index `k`.
def GroupOpOracle : OracleSpec Unit := fun _ => (Nat × Nat × Nat, Unit)

/-- This oracle interface allows an adversary to get the bit encoding of a group element. -/
def GroupEncodeOracle (bitLength : ℕ) : OracleSpec Unit := fun _ => (Nat, BitVec bitLength)

/-- This oracle interface allows an adversary to get the bit encoding of a group element. -/
def GroupDecodeOracle (bitLength : ℕ) (G : Type) : OracleSpec Unit :=
  fun _ => (BitVec bitLength, Option G)

/-- An adversary in the Algebraic Group Model (AGM), given a single group `G` with elements having
    representation size `bitLength`, is a stateful oracle computation with oracle access to the
    `GroupOp` and `GroupEncode` oracles, and the state being the array of group elements (accessed
    via handles).

  How to make the adversary truly independent of the group description? It could have had `G`
  hardwired. Perhaps we need to enforce parametricity, i.e. it should be of type
  `∀ G, Group G → AGMAdversary G bitLength α`? -/
def AGMAdversary (G : Type) (bitLength : ℕ) : Type → Type _ := fun α => StateT (GroupVal G)
  (OracleComp ((GroupEncodeOracle bitLength) ++ₒ (GroupDecodeOracle bitLength G))) α

end AGM

namespace KZG

/-! ## The KZG Polynomial Commitment Scheme -/

-- TODO: figure out how to get `CommGroup` for free
variable {G : Type*} [CommGroup G] {p : ℕ} [Fact (Nat.Prime p)] (h : Nat.card G = p)
  {g : G}

instance {α : Type} [CommGroup α] : AddCommMonoid (Additive α) := inferInstance

variable {G₁ : Type*} [CommGroup G₁] [IsPrimeOrderWith G₁ p] {g₁ : G₁}
  {G₂ : Type*} [CommGroup G₂] [IsPrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type*} [CommGroup Gₜ] [IsPrimeOrderWith Gₜ p]
  -- TODO: need to make this a `ZMod p`-linear map
  (pairing : (Additive G₁) →ₗ[ℤ] (Additive G₂) →ₗ[ℤ] (Additive Gₜ))

-- instance : IsCyclic G := isCyclic_of_prime_card h

-- #check unique_of_prime_card

/-- The vector of length `n + 1` that consists of powers:
  `#v[1, g, g ^ a.val, g ^ (a.val ^ 2), ..., g ^ (a.val ^ n)` -/
def towerOfExponents (g : G) (a : ZMod p) (n : ℕ) : Vector G (n + 1) :=
  .ofFn (fun i => g ^ (a.val ^ i.val))

variable {n : ℕ}

/-- The `srs` (structured reference string) for the KZG commitment scheme with secret exponent `a`
    is defined as `#v[g₁, g₁ ^ a, g₁ ^ (a ^ 2), ..., g₁ ^ (a ^ (n - 1))], #v[g₂, g₂ ^ a]` -/
def generateSrs (n : ℕ) (a : ZMod p) : Vector G₁ (n + 1) × Vector G₂ 2 :=
  (towerOfExponents g₁ a n, towerOfExponents g₂ a 1)

/-- One can verify that the `srs` is valid via using the pairing -/
def checkSrs (proveSrs : Vector G₁ (n + 1)) (verifySrs : Vector G₂ 2) : Prop :=
  ∀ i : Fin n,
    pairing (proveSrs[i.succ]) (verifySrs[0]) = pairing (proveSrs[i.castSucc]) (verifySrs[1])

/-- To commit to an `n`-tuple of coefficients `coeffs` (corresponding to a polynomial of degree less
    than `n`), we compute: `∏ i : Fin n, srs[i] ^ (p.coeff i)` -/
def commit (srs : Vector G₁ n) (coeffs : Fin n → ZMod p) : G₁ :=
  ∏ i : Fin n, srs[i] ^ (coeffs i).val

/-- When committing `coeffs` using `srs` generated by `towerOfExponents`, and `coeffs` correspond to
  a polynomial `poly : (ZMod p)[X]` of degree `< n + 1`, we get the result `g₁ ^ (p.eval a).val` -/
theorem commit_eq {g : G₁} {a : ZMod p} (poly : degreeLT (ZMod p) (n + 1)) :
    commit (towerOfExponents g a n) (degreeLTEquiv _ _ poly) = g ^ (poly.1.eval a).val := by
  simp [commit, towerOfExponents]
  simp_rw [← pow_mul, Finset.prod_pow_eq_pow_sum]
  rw [eval_eq_sum_degreeLTEquiv poly.property]
  simp
  -- simp_rw [← ZMod.val_pow]
  sorry

/-- To generate an opening proving that a polynomial `poly` has a certain evaluation at `z`,
  we return the commitment to the polynomial `q(X) = (poly(X) - poly.eval z) / (X - z)` -/
noncomputable def generateOpening [Fact (Nat.Prime p)] (srs : Vector G₁ (n + 1))
    (coeffs : Fin (n + 1) → ZMod p) (z : ZMod p) : G₁ :=
  letI poly : degreeLT (ZMod p) (n + 1) := (degreeLTEquiv (ZMod p) (n + 1)).invFun coeffs
  letI q : degreeLT (ZMod p) (n + 1) :=
    ⟨(poly.val - C (poly.val.eval z)) / (X - C z), by
      apply mem_degreeLT.mpr
      have : Field (ZMod p) := sorry
      sorry⟩
      -- Don't know why `degree_div_le` time out here
      -- refine lt_of_le_of_lt (degree_div_le _ (X - C z)) ?_
      -- refine lt_of_le_of_lt (degree_sub_le _ _) (sup_lt_iff.mpr ?_)
      -- constructor
      -- · exact mem_degreeLT.mp poly.property
      -- · exact lt_of_lt_of_le degree_C_lt (by norm_cast; omega)⟩
  commit srs (degreeLTEquiv (ZMod p) (n + 1) q)

/-- To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed
  evaluation `v`, we use the pairing to check "in the exponent" that `p(a) - p(z) = q(a) * (a - z)`,
  where `p` is the polynomial and `q` is the quotient of `p` at `z` -/
noncomputable def verifyOpening (verifySrs : Vector G₂ 2) (commitment : G₁) (opening : G₁)
    (z : ZMod p) (v : ZMod p) : Prop :=
  pairing (commitment / g₁ ^ v.val) (verifySrs[0]) = pairing opening (verifySrs[1] / g₂ ^ z.val)

-- p(a) - p(z) = q(a) * (a - z)
-- e ( C / g₁ ^ v , g₂ ) = e ( O , g₂ ^ a / g₂ ^ z)

-- theorem correctness {g : G} {a : ZMod p} {coeffs : Fin n → ZMod p} {z : ZMod p} :

end KZG
