/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # The Trivial (Oracle) Reduction: Do Nothing!

  This is a zero-round (oracle) reduction. Both the (oracle) prover and the (oracle) verifier simply
  pass on their inputs unchanged.

  We still define this as the base for realizing other zero-round reductions, via lens / lifting.
-/

namespace DoNothing

variable {ι : Type} (oSpec : OracleSpec ι) (Statement Witness : Type)

section Reduction

/-- The prover for the `DoNothing` reduction. -/
@[inline, specialize]
def prover : Prover ![] oSpec Statement Witness Statement Witness where
  PrvState | 0 => Statement × Witness
  input := id.curry
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := id

/-- The verifier for the `DoNothing` reduction. -/
@[inline, specialize]
def verifier : Verifier ![] oSpec Statement Statement where
  verify := fun stmt _ => pure stmt

/-- The reduction for the `DoNothing` reduction.
  - Prover simply returns the statement and witness.
  - Verifier simply returns the statement.
-/
@[inline, specialize]
def reduction : Reduction ![] oSpec Statement Witness Statement Witness where
  prover := prover oSpec Statement Witness
  verifier := verifier oSpec Statement

variable [oSpec.FiniteRange] (rel : Statement → Witness → Prop)

/-- The `DoNothing` reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement Witness).perfectCompleteness rel rel := by
  simp [Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
    reduction, prover, verifier]

-- theorem reduction_rbr_knowledge_soundness :
--     (reduction oSpec Statement Witness).rbrKnowledgeSoundness rel rel := by
  -- simp [Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
  --   reduction, prover, verifier]

end Reduction

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]

/-- The oracle prover for the `DoNothing` oracle reduction. -/
@[inline, specialize]
def oracleProver : OracleProver ![] oSpec Statement Witness Statement Witness
    OStatement OStatement where
  PrvState | 0 => (Statement × (∀ i, OStatement i)) × Witness
  input := id.curry
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := id

/-- The oracle verifier for the `DoNothing` oracle reduction. -/
@[inline, specialize]
def oracleVerifier : OracleVerifier ![] oSpec Statement Statement OStatement OStatement where
  verify := fun stmt _ => pure stmt
  embed := Function.Embedding.inl
  hEq := by intro i; simp

/-- The oracle reduction for the `DoNothing` oracle reduction.
  - Prover simply returns the (non-oracle and oracle) statement and witness.
  - Verifier simply returns the (non-oracle and oracle) statement.
-/
@[inline, specialize]
def oracleReduction : OracleReduction ![] oSpec Statement Witness Statement Witness
    OStatement OStatement where
  prover := oracleProver oSpec Statement Witness OStatement
  verifier := oracleVerifier oSpec Statement OStatement

variable [oSpec.FiniteRange] (rel : Statement × (∀ i, OStatement i) → Witness → Prop)

/-- The `DoNothing` oracle reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem oracleReduction_completeness :
    (oracleReduction oSpec Statement Witness OStatement).perfectCompleteness rel rel := by
  simp [OracleReduction.perfectCompleteness, OracleReduction.toReduction, OracleVerifier.toVerifier,
    oracleReduction, oracleProver, oracleVerifier]
  -- Need to simp the below separately, otherwise we get timeout
  simp [Reduction.run, Prover.run, Verifier.run]
  aesop

-- theorem oracleReduction_rbr_knowledge_soundness :
--     (oracleReduction oSpec Statement Witness OStatement).rbrKnowledgeSoundness rel rel := by
--   simp [OracleReduction.rbrKnowledgeSoundness, OracleReduction.toReduction,
--     OracleVerifier.toVerifier, oracleReduction, oracleProver, oracleVerifier]
--   -- Need to simp the below separately, otherwise we get timeout
--   simp [Reduction.run, Prover.run, Verifier.run]
--   aesop

end OracleReduction

end DoNothing
