/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

/-- Proximity bound function -/
noncomputable def Bstar (x: ℝ) : ℝ := Real.sqrt x

/-- Proximity error function
 -- coerced to ENNReal, because it is exclusively used in probability inequalities and
  we agreed to coerce ℝ → ENNReal not vice versa -/
noncomputable def err' (F : Type*) [Fintype F] (d : ℕ) (ρ : ℝ) (δ : ℝ) (m: ℕ) : ENNReal :=
  ENNReal.ofReal (
  if δ ≤ (1 - ρ) / 2 then
    ((m - 1) * d) / (ρ * (Fintype.card F))
  else
    let min_val := min (1 - (Real.sqrt ρ) - δ ) ((Real.sqrt ρ) / 20)
    ((m - 1) * d^2) / ((Fintype.card F) * (2 * min_val)^7)
)
