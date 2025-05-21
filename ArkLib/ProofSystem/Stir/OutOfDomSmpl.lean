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
         {ι : Finset F}

/-! Section 4.3 in https://eprint.iacr.org/2024/390.pdf -/

def domainComplement (ι : Finset F) : Finset F :=
  Finset.univ \ ι

/-- Pr_{r₀, …, rₛ₋ ₁  ← 𝔽\L} [∃ distinct u, u′ ∈ List(f, d, δ) :
∀ i ∈ [0...s-1], u(r_i) = u′(r_i)] -/
noncomputable def listDecodingCollisionProbability
  (f : ι → F) (δ : ℝ) (s : ℕ) (degree : ℕ) (domain : ι ↪ F)
  (h_nonempty : Nonempty (domainComplement ι)) : ENNReal :=
  (PMF.uniformOfFintype (Fin s → domainComplement ι)).toOuterMeasure { r |
    ∃ (u u' : code F ι domain degree),
    -- ∃ (u u' : (relHammingBall (toLinearCode C) f δ)),
      u.val ≠ u'.val ∧ -- both u and u' lie within δ of some target f
      u.val ∈ relHammingBall ↑(code F ι domain degree) f δ ∧
      u'.val ∈ relHammingBall ↑(code F ι domain degree) f δ ∧
    -- their interpolating polynomials agree on each sampled r_i
      ∀ i : Fin s,
        (decode u).eval (r i).val = (decode u').eval (r i).val
  }

lemma out_of_dom_smpl_1
  {δ l : ℝ} {s : ℕ} {f : ι → F} {degree : ℕ} {domain : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code F ι domain degree)
  (h_decodable : listDecodable ↑C δ l)
  (h_nonempty : Nonempty (domainComplement ι))  :
  listDecodingCollisionProbability f δ s degree domain h_nonempty ≤
    (ENNReal.ofReal (l * (l-1) / 2)) * ((degree - 1) / (Fintype.card F - ι.card))^s
  := by sorry

lemma out_of_dom_smpl_2
  {δ l : ℝ} {s : ℕ} {f : ι → F} {degree : ℕ} {domain : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code F ι domain degree)
  (h_decodable : listDecodable ↑C δ l)
  (h_nonempty : Nonempty (domainComplement ι)) :
  listDecodingCollisionProbability f δ s degree domain h_nonempty ≤
    (ENNReal.ofReal (l^2 / 2)) * (degree / (Fintype.card F - ι.card))^s
  := by sorry

end OutOfDomSmpl
