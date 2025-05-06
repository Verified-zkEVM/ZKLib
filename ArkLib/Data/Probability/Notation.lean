/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform

/-!
  # Notation for probability sampling statements

  The goal is to be able to write statements like:
  ```
  Pr_{ x ←$ F, y ←$ F, z ←$ F × F }[ z = (x, y) ]
  ```
  which should parse as:
  ```
  (do let x ← PMF.uniformOfFintype F
      let y ← PMF.uniformOfFintype F
      let z ← PMF.uniformOfFintype (F × F)
      return z = (x, y)).val True
  ```
  The `.val True` is used to extract the probability of the condition holding.
  In general the `do` notation is more restrictive than `PMF.bind`, as the latter allows for
  changing universe levels. This should not be an issue in general if we always work over `Type`.

  We should also allow for non-uniform distributions, e.g.
  `Pr_{ e ← discreteGaussian (ZMod p) }[ e = 0 ]`.
-/

open scoped ProbabilityTheory NNReal ENNReal

variable {F : Type} [Nonempty F] [Fintype F]

noncomputable example :
  (do
    let x ← PMF.uniformOfFintype F
    let y ← PMF.uniformOfFintype F
    let z ← PMF.uniformOfFintype (F × F)
    return z = (x, y)).val True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by
  sorry


open Lean Elab Term Meta PMF

-- Output from Gemini. TODO: debug

-- -- Syntax for sampling from an existing PMF: r ← D
-- syntax prob_binder_direct := ident " ← " term:maxPrec
-- -- Syntax for uniform sampling from a Type: r ←$ T
-- syntax prob_binder_uniform := ident " ←$ " term:maxPrec

-- -- A choice between the two binder types
-- syntax prob_binder_choice := prob_binder_direct <|> prob_binder_uniform

-- -- A comma-separated list of these chosen binders
-- syntax binders_prob := sepBy(prob_binder_choice, ", ")

-- -- The main notation
-- syntax (name := probNotationDualBinders) "Pr_{" binders:binders_prob "} [" cond:term "]" : term

-- macro_rules
--   | `(probNotationDualBinders| Pr_{ $binders_stx:binders_prob } [ $condition_stx:term ]) => do
--     let binder_elements := binders_stx.getSepArgs -- These are `prob_binder_choice`
--     if binder_elements.isEmpty then
--       Macro.throwError "Pr_{...} notation requires at least one sampling binder."

--     -- Start with PMF.pure of the condition
--     let mut current_pmf_expr ← `(PMF.pure ($condition_stx : Bool))

--     -- Iterate backwards through the binders
--     for i in (Array.range binder_elements.size).reverse do
--       let binder_choice_stx := binder_elements[i]! -- This is a `prob_binder_choice`

--       -- binder_choice_stx is a Syntax node that has one child,
--       -- which is either prob_binder_direct or prob_binder_uniform.
--       let actual_binder_stx := binder_choice_stx[0]

--       let current_ident := actual_binder_stx[0]       -- rᵢ
--       let source_term_stx := actual_binder_stx[2] -- T or Dᵢ

--       let actual_dist_for_bind_stx : Syntax ←
--         if actual_binder_stx.getKind == ``prob_binder_uniform then
--           -- User wrote: rᵢ ←$ T
--           -- T needs [Fintype T] and [Nonempty T]
--           `(PMF.uniformOfFintype $source_term_stx)
--         else if actual_binder_stx.getKind == ``prob_binder_direct then
--           -- User wrote: rᵢ ← Dᵢ
--           -- Dᵢ must be a PMF Sᵢ
--           `($source_term_stx)
--         else
--           Macro.throwErrorAt actual_binder_stx "Internal macro error: unexpected binder kind."

--       current_pmf_expr ← `(PMF.bind ($actual_dist_for_bind_stx)
--         (fun $current_ident => $current_pmf_expr))

--     -- The final expression
--     `(ensure_suffices% {
--         open PMF -- For PMF.bind, PMF.pure, and .val
--         ($current_pmf_expr).val True
--       } : ENNReal)
