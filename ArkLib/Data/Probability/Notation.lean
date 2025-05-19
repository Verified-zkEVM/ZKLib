/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform

/-!
  # Notation for probability sampling statements

  The goal is to be able to write readable statements like:
  ```
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ F × F }[ z = (x, y) ]
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
  `Pr_{ let e ← discreteGaussian (ZMod p) }[ e = 0 ]`.
-/

open scoped ProbabilityTheory NNReal ENNReal

open Lean Elab Term Meta PMF

-- #check Lean.Parser.doElemParser

-- #check Lean.Parser.Term.doExpr

/-- Notation for uniform sampling from a finite, non-empty type. Just converts to
  `PMF.uniformOfFintype`. -/
scoped[ProbabilityTheory] notation "$ᵖ" => PMF.uniformOfFintype

-- Define `probStmts` to capture a sequence of `doElem`s.
-- `doElem*` means zero or more `doElem`
-- `doElem` covers `let x ← ...`, `let y := ...`, pure actions, etc.
-- syntax probStmts := many(Lean.Parser.Term.doSeq)

-- notation "Pr_{" probStmts "}[" term "]" =>
--   `(ensure_suffices% {
--       open PMF -- Ensure PMF is in scope for .val and for the do block itself
--       (do $probStmts  -- Use $stmts directly, it's a doSeq
--           return ($term : Prop) -- The final return of the boolean condition
--       ).val True
--     } : ENNReal)

-- notation "Pr_{" probStmts "}[" term "]" =>
--   `(do $probStmts; `(return $term)).val True

-- syntax (name := probThing)
--   "[" term " | " sepBy((sepBy(ident, ",") " ← " term),";") "]" : term

variable {F : Type} [Nonempty F] [Fintype F]

noncomputable example :
  (do
    let x ← $ᵖ F
    let y ← $ᵖ F
    let z ← $ᵖ (F × F)
    return z = (x, y)).val True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by sorry

-- Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ F × F }[ z = (x, y) ]


/- Notation for simple, non sequencial, dependent probabilities of the form
   Pr_{r ← α} [predicate(r)], where `predicate` is of type `α → Prop)` -/
noncomputable def Pr {α : Type _} (P : α → Prop)
  [Fintype α] [DecidableEq α] [Nonempty α] : ENNReal :=
  (PMF.uniformOfFintype α).toOuterMeasure { r | P r }

notation (priority := high) "Pr_{" x " ← " A "}" "[" P "]" =>
  Pr (fun (x : A) => P)

example {α : Type _} [Semiring α] [Fintype α] [DecidableEq α]
    (predicate : α → Prop) (ERR : ENNReal) :
    Pr_{r ← α}[predicate r] > ERR := by sorry
