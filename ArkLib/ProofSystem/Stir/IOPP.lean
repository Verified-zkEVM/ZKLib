/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.OracleReduction.Security.Basic
import Mathlib.Tactic


namespace Reduction
open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {ι : Type}

section IOPP

/-- An *interactive-oracle proof of proximity* (IOPP) is an
    Interactive oracle proof enriched with three security properties
    of (perfect) completeness, soundness and round-by-round soundness.-/
structure IOPP
    (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [∀ i, VCVCompatible (pSpec.Challenge i)][oSpec.FiniteRange]
    [∀ i, ToOracle (pSpec.Message i)]
    (StmtIn WitIn : Type)
    { ιₛₒ: Type} (OStmtOut : ιₛₒ → Type)[∀ i, ToOracle (OStmtOut i)]
    (ε_sound : ℝ≥0) (ε_rbr : pSpec.ChallengeIndex → ℝ≥0)
    where

  /-- The underlying interactive-oracle proof-/
  iop : OracleProof pSpec oSpec StmtIn WitIn OStmtOut

  /--necessary parameters to state the completeness property-/
  relIn  : StmtIn  → WitIn → Prop
  relOut : Bool → Unit → Prop
  reduction : Reduction pSpec oSpec StmtIn WitIn Bool Unit

  ioppCompleteness : perfectCompleteness relIn relOut reduction

  /--necessary parameters to state the soundness property-/
  langIn : Set StmtIn
  langOut : Set Bool
  verifier : Verifier pSpec oSpec StmtIn Bool

  /--**One-shot soundness**-/
  ioppSoundness : soundness langIn langOut verifier ε_sound

  /-- A *state function* used for round-by-round soundness. -/
  stateFn :
    StateFunction langIn langOut verifier

  /--**round-by-round soundness** -/
  ioppRBRSoundness : rbrSoundness langIn langOut verifier stateFn ε_rbr

end IOPP
end Reduction
