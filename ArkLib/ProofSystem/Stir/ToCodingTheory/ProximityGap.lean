/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/


import ArkLib.ProofSystem.Stir.ToCodingTheory.ReedSolomonCodes
import ArkLib.ProofSystem.Stir.ToCodingTheory.FracHammingDist
import ArkLib.ProofSystem.Stir.ToCodingTheory.ProximityBound

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/-! Section 4.1 in https://eprint.iacr.org/2024/390.pdf -/


lemma proximity_gap
  {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  {L : Finset F}
  {d : ℕ}
  (C : ReedSolomonCode F L d)
  (δ : {x : ℝ // 0 < x ∧ x < 1 - Bstar C.rate})
  (m : ℕ)
  (f : Fin m → (L → F))
  (h : (PMF.uniformOfFintype F).toOuterMeasure { r |
          fractionalHammingDistSet
            (λ x ↦ ∑ j : Fin m, (r^(j : ℕ)) • (f j x))
            (C.code)
            (C.nonempty)
          ≤ δ.val } > err' F d C.rate δ m) :
  ∃ (S : Finset F), -- better S Finset L ? then S subset L is automatic
    S ⊆ L ∧
    S.card ≥ (1 - δ.val) * L.card ∧
    ∀ i : Fin m, ∃ u ∈ C.code, ∀ x ∈ S, ∀ hx : x ∈ L, f i ⟨x, hx⟩ = u ⟨x, hx⟩ := by
  sorry
