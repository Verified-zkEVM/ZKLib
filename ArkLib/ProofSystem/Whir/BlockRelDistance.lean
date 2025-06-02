/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.ConstraintReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.RelativeHammingDistance
import ArkLib.Data.CodingTheory.SmoothDomainGeneric


namespace BlockRelDistance

open SmoothDomain ReedSolomon NNReal ListDecodable
variable {F : Type*} [Field F] {ι : Type*} [Field ι] [Fintype ι] [Pow ι ℕ]

/--The type of `2^k`-th power images over a domain `ι ⊆ F`.
  This defines the set of field elements `y ∈ F` for which there exists `x ∈ ι`
  such that `y = x^(2^k)`. It models the image of the map `x ↦ x^(2^k)` restricted to `ι`.
  Semantically: `indexPowT ι k = { x^(2^k) | x ∈ ι } ⊆ F`.
-/
def indexPowT (S : Finset ι) (φ : ι ↪ F) (k : ℕ) := { y : F // ∃ x ∈ S, y = (φ x) ^ (2^k) }

/--The `2^k`-power fiber over `y ∈ indexPowT ι k`.
  This defines the preimage of `y` under the map `x ↦ x^(2^k)` restricted to `x ∈ ι`.
  It returns the subset of `ι` consisting of all `x` such that `x^(2^k) = y`.
  Semantically: `powFiberT ι k y = { x ∈ ι | x^(2^k) = y }`.
-/
def powFiberT (S : Finset ι) (φ : ι ↪ F) (k : ℕ) (y : indexPowT S φ k) :=
  { x : ι // x ∈ S ∧ (φ x) ^ (2^k) = y.val }

/--Definition 4.16
  For `ι` be a smooth evaluation domain, `k` be a folding parameter, `z ∈ ι ^ 2^k`,
  Block is the set of elements `{ y ∈ ι, y ^ 2^k = z }`.-/
def block [DecidableEq F] [DecidableEq ι] (S : Finset ι) (φ : ι ↪ F) (k : ℕ)
  (z : indexPowT S φ k) [Smooth φ]:=
    powFiberT S φ k z

/--The class DecidableBlockDisagreement provides a decidability instance for testing
  pointwise inequality of two functions `f, g : ι → F` on elements of `block ι k z domain`,
  for all `z ∈ LpowT ι k`.

  This class abstracts the decidability condition required to determine whether two
  functions disagree on any point in the preimage of `z` under the map `x ↦ x^(2^k)` over the
  evaluation domain `ι`. This is useful in defining sets of such `z`.
-/
class DecidableBlockDisagreement
  [DecidableEq F] [DecidableEq ι] (S : Finset ι) (φ : ι ↪ F) (f : ι → F) (k : ℕ)
  [Smooth φ] where
  dec_inst :
    ∀ z : indexPowT S φ k, ∀ g : ι → F,
      Decidable (∃ y : block S φ k z, f y.val ≠ g y.val)

/--Let `C = CRS[F, ι, m, w, σ]` be a ConstrainReedSolomon code and `f,g : ι → F`, then
  the k-wise block relative distance is defined as
    Δᵣ(C,ι,f,g) = |{z ∈ ι ^ 2^k : ∃ y ∈ Block(ι,k,z) f(y) ≠ g(y)}| / |ι^(2^k)|.
  Below, we define a disagreementSet(ι, f, k, domain) as a map (g → Finset (indexPow ι k))
  using the class DecidableBlockDisagreement, to filter a finite subset of the Finset
  (indexPow ι k), as per {z ∈ ι ^ 2^k : ∃ y ∈ Block(ι,k,z) f(y) ≠ g(y)} for a given g.  -/
noncomputable def disagreementSet
  [DecidableEq F] [DecidableEq ι] (S : Finset ι) (φ : ι ↪ F) (f : ι → F)
  (k : ℕ) [Fintype (indexPowT S φ k)]
  [Smooth φ] [h : DecidableBlockDisagreement S φ f k] :
  (g : ι → F) → Finset (indexPowT S φ k) :=
  fun g =>
    Finset.univ.filter (fun z => @decide _ (h.dec_inst z g))

/--Definition 4.17
  Given the disagreementSet from above, we obtain the block relative distance as
  |disagreementSet|/ |ι ^ (2^k|.-/
noncomputable def blockRelDistance
  [DecidableEq F] [DecidableEq ι] (S : Finset ι) (φ : ι ↪ F) (f : ι → F)
  (k : ℕ) [Fintype (indexPowT S φ k)] [Smooth φ]
  [h : DecidableBlockDisagreement S φ f k] :
  (g : ι → F) → ℝ≥0 :=
  fun g =>
    (disagreementSet S φ f k g).card / (Fintype.card (indexPowT S φ k) : ℝ≥0)

/--notation Δᵣ(ι, f, k, domain, g) is the k-wise block relative distance.-/
scoped notation "Δᵣ( "S", "φ", "f", "k", "g")"  => blockRelDistance S φ f k g

/--For the set S ⊆ F^ι, we define the minimum block relative distance wrt set S.-/
noncomputable def minBlockRelDistance
  [DecidableEq F] [DecidableEq ι] (S : Finset ι) (φ : ι ↪ F) (f : ι → F)
  (Set : Set (ι → F)) (k : ℕ) [Fintype (indexPowT S φ k)]
  [Smooth φ] [h : DecidableBlockDisagreement S φ f k] : ℝ≥0 :=
    sInf { d : ℝ≥0 | ∃ g ∈ Set, Δᵣ(S, φ, f, k, g) = d}

/--notation Δₛ(ι, f, S, k, domain)  denotes the minimum block relative distance wrt set S.-/
scoped notation "Δₛ( "S", "f", "φ", "k", "domain" )"  => minBlockRelDistance S f φ k domain

/--Definition 4.18
  For a constrained ReedSolomon code C = CRS[F, ι, m, w, σ], proximity parameter δ ∈ [0,1]
  function f : ι → F, we define the following as the ball of radius `δ` centered at
  word `f`, i.e., u ∈ C such that Δᵣ(ι, f, k, domain, u) ≤ δ.-/
noncomputable def listBlockRelDistance
  [DecidableEq F] [DecidableEq ι] (S : Finset ι) {φ : ι ↪ F} (f : ι → F)
  (k : ℕ) [Fintype (indexPowT S φ k)] [Smooth φ]
  {m : ℕ} {w : MvPolynomial (Fin (m+1)) F} {σ : F}
  (C : Set (ι → F)) (hcode : C = constraintCode F ι φ m w σ) (δ : ℝ≥0)
  [h : DecidableBlockDisagreement S φ f k]
  : (Set (ι → F)) :=
    let hδLe := δ ≤ 1
    { u ∈ C | Δᵣ(S, φ, f, k, u) ≤ δ }

 /--Λᵣ(ι, f, C, hcode, δ) denotes the ball of radius `δ` centered at word `f`.-/
scoped notation "Λᵣ( "S", "f", "k", "C", "hcode", "δ")" => listBlockRelDistance S f k C hcode δ

/--Claim 4.19
  For a constrained ReedSolomon code `C = CRS[F, ι, m, w, σ]`, codewords `f, g : ι → F`,
  we have that the block relative distance `Δᵣ(f, k, domain, g)` is bounded by the
  relative Hamming distance `δᵣ(f,g)`. As a result, we have
    `Λᵣ(f, C, hcode, δ)` is bounded by `Λ(f, C, hcode, δ)`-/
lemma blockRelDistance_le_hammingDistance
  [DecidableEq F] [DecidableEq ι] {S : Finset ι} {φ : ι ↪ F} (f g : ι → F)
  (k : ℕ) [Fintype (indexPowT S φ k)] [Smooth φ]
  {m : ℕ} {w : MvPolynomial (Fin (m+1)) F} {σ : F}
  (C : Set (ι → F)) (hcode : C = constraintCode F ι φ m w σ)
  [h : DecidableBlockDisagreement S φ f k]
  (hBound : Δᵣ(S, φ, f, k, g) ≤ (δᵣ(f, g) : ℝ)) :
    ∀ {δ : ℝ≥0} (hδLe : δ ≤ 1),
      let listHamming := relHammingBall C f δ
      let listBlock := Λᵣ(S, f, k, C, hcode, δ)
      listBlock ⊆ listHamming := by sorry



end BlockRelDistance
