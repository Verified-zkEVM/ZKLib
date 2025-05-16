/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.ListDecodeability
import ArkLib.Data.CodingTheory.RelativeHammingDistance

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic

open ReedSolomon ListDecodable Finset
namespace OutOfDomSmpl
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Finset F} {domain : ι ↪ F}

/-! Section 4.3 in https://eprint.iacr.org/2024/390.pdf -/

def domainComplement (ι : Finset F) : Finset F :=
  Finset.univ \ ι

/-- Pr_{r₀, …, rₛ₋ ₁  ← 𝔽\L} [∃ distinct u, u′ ∈ List(f, d, δ) :
∀ i ∈ [0...s-1], u(r_i) = u′(r_i)] -/
noncomputable def listDecodingCollisionProbability
  {degree : ℕ} (C : code F ι domain degree) (f : ι → F)
  (δ : ℝ) (s : ℕ) (h_nonempty : Nonempty (domainComplement ι))  : ENNReal :=
  (PMF.uniformOfFintype (Fin s → domainComplement ι)).toOuterMeasure { r |
    ∃ (u u' : (relHammingBall (toLinearCode C) f δ)),
        u.val ≠ u'.val ∧ -- both u and u' lie within δ of some target f
      -- their interpolating polynomials agree on each sampled r_i
        ∀ i : Fin s,
        (decode ↑u).eval (r i).val = (decode ↑u').eval (r i).val
  }

lemma out_of_dom_smpl_1
  {degree : ℕ} (C : code F ι domain degree)
  (δ l : ℝ) (s : ℕ) (f : ι → F)
  (h_decodable : listDecodable (toLinearCode C) δ l) :
  listDecodingCollisionProbability C f δ s h_nonempty ≤
    (l.choose 2) * ((degree - 1) / (Fintype.card F - ι.card))^s := by sorry

lemma out_of_dom_smpl_2
  {degree : ℕ} (f : ι → F)
  (C : code F ι domain degree)
  (δ l : ℝ) (s : ℕ)
  (h_decodable : listDecodable (toLinearCode C) δ l) :
  listDecodingCollisionProbability C f δ s h_nonempty ≤
    (l^2 / 2) * (degree / (Fintype.card F - ι.card))^s := by sorry

end OutOfDomSmpl
