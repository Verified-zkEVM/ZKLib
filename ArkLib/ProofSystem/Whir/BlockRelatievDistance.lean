/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.ConstraintReedSolomon
import ArkLib.Data.CodingTheory.SmoothDomain


namespace BlockRelDistance

open SmoothDomain ReedSolomon NNReal
variable {F : Type*} [Field F] {ι : Finset F} [Pow ι ℕ]

/--Type-level version of Lpow: elements of the image S.map (x ↦ x ^ 2^k).-/
def LpowT (ι : Finset F) (k : ℕ) := { y : F // ∃ x ∈ ι, y = x ^ (2^k) }

def powFiberT (ι : Finset F) (k : ℕ) (y : LpowT ι k) :=
  { x : F // x ∈ ι ∧ x ^ (2^k) = y.val }

/--Definition 4.16
  For `ι` be a smooth evaluation domain, `k` be a folding parameter, `z ∈ ι ^ 2^k`,
  Block is the set of elements `{ y ∈ ι, y ^ 2^k = z }`.-/
def block (ι : Finset F) (k : ℕ) (z : LpowT ι k) (domain : ι ↪ F) [Smooth domain k]:=
  powFiberT ι k z

/--Let `C = CRS[F, ι, m, w, σ]` be a ConstrainReedSolomon code and `f,g : ι → F`, then
  the k-wise block relative distance is defined as
    Δᵣ(C,ι,f,g) = |{z ∈ ι ^ 2^k : ∃ y ∈ Block(ι,k,z) f(y) ≠ g(y)}| / |ι^(2^k)|.-/
noncomputable def disagreementSet (ι : Finset F) [DecidableEq F]
  (f : ι → F) (k : ℕ) [Fintype (LpowT ι k)] (domain : ι ↪ F) [Smooth domain k]
  [∀ z, ∀ g : ι → F, Decidable (∃ y : block ι k z domain,
                  f ⟨y.val, y.property.left⟩ ≠ g ⟨y.val, y.property.left⟩)] :
  (g : ι → F) → Finset (LpowT ι k) :=
  fun g =>
    {z | ∃ y : block ι k z domain, f ⟨y.val, y.property.left⟩ ≠ g ⟨y.val, y.property.left⟩}

noncomputable def blockRelDistance (ι : Finset F) [DecidableEq F]
  (f : ι → F) (k : ℕ) [Fintype (LpowT ι k)] (domain : ι ↪ F) [Smooth domain k]
  [∀ z, ∀ g : ι → F, Decidable (∃ y : block ι k z domain,
                  f ⟨y.val, y.property.left⟩ ≠ g ⟨y.val, y.property.left⟩)]:
  (g : ι → F) → ℝ≥0 :=
  fun g =>
    (disagreementSet ι f k domain g).card / (Fintype.card (LpowT ι k) : ℝ≥0)

scoped notation "Δₛ( "ι", "f", "k", "domain")" g => blockRelDistance ι f k domain g

noncomputable def listBlockRelDistance (ι : Finset F) [DecidableEq F]
  (f : ι → F) (k : ℕ) [Fintype (LpowT ι k)] {domain : ι ↪ F} [Smooth domain k]
  {m : ℕ} {w : MvPolynomial (Fin (m+1)) F} {σ : F} (C : Set (ι → F)) (δ : ℝ≥0)
  (hc : C = constraintCode F ι domain k m w σ) (hδLe : δ ≤ 1)
  [∀ z, ∀ g : ι → F, Decidable (∃ y : block ι k z domain,
                  f ⟨y.val, y.property.left⟩ ≠ g ⟨y.val, y.property.left⟩)]
  : (Set (ι → F)) :=
    { u ∈ C | blockRelDistance ι f k domain u ≤ δ }



end BlockRelDistance
