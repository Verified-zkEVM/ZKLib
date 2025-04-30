/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Stir.ToCodingTheory.ReedSolomonCodes

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Basic


namespace OutOfDomSmpl

/-! Section 4.3 in https://eprint.iacr.org/2024/390.pdf -/


/-- Pr_{r₀, …, rₛ₋ ₁  ← 𝔽\L} [∃ distinct u, u′ ∈ List(f, d, δ) : ∀ i ∈ [0...s-1], u(r_i) = u′(r_i)] -/
noncomputable def listDecodingCollisionProbability
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : ℝ)
  (s : ℕ)
  (h_nonempty : Nonempty C.domainComplement) : ENNReal :=
  (PMF.uniformOfFintype (Fin s → C.domainComplement)).toOuterMeasure { r |
    ∃ (u u' : ↥C.code),
      u.val ≠ u'.val ∧
      -- both u and u' lie within δ of some target f
      u.val ∈ C.list u.val δ ∧
      u'.val ∈ C.list u.val δ ∧
      -- their interpolating polynomials agree on each sampled r_i
      ∀ i : Fin s,
        (C.poly u).eval (r i).val = (C.poly u').eval (r i).val
  }

lemma out_of_dom_smpl_1
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : ℝ)
  (l s : ℕ)
  (h_decodable : C.listDecodable δ l) :
  listDecodingCollisionProbability C δ s C.domain_complement_nonempty ≤
    (l.choose 2) * ((d - 1) / (Fintype.card F - L.card))^s := by sorry

lemma out_of_dom_smpl_2
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : ℝ)
  (l s : ℕ)
  (h_decodable : C.listDecodable δ l) :
  listDecodingCollisionProbability C δ s C.domain_complement_nonempty ≤
    (l^2 / 2) * (d / (Fintype.card F - L.card))^s := by sorry

end OutOfDomSmpl
