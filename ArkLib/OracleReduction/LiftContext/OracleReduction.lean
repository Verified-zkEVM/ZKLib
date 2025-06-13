/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.LiftContext.Reduction

/-!
  ## Lifting Oracle Reductions to Larger Contexts

  This file is a continuation of `LiftContext/Reduction.lean`, where we lift oracle reductions to
  larger contexts.

  The only new thing here is the definition of the oracle verifier. The rest (oracle prover +
  security properties) are just ported from `LiftContext/Reduction.lean`, with suitable conversions.
-/

open OracleSpec OracleComp ProtocolSpec

open scoped NNReal

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {Outer_ιₛᵢ : Type} {OuterOStmtIn : Outer_ιₛᵢ → Type} [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} {OuterOStmtOut : Outer_ιₛₒ → Type} [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} {InnerOStmtIn : Inner_ιₛᵢ → Type} [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} {InnerOStmtOut : Inner_ιₛₒ → Type} [∀ i, OracleInterface (InnerOStmtOut i)]
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- The outer prover after lifting invokes the inner prover on the projected input, and
  lifts the output -/
def OracleProver.liftContext
    [oLens : OracleContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    (P : OracleProver pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut
      InnerOStmtIn InnerOStmtOut) :
      OracleProver pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut
      OuterOStmtIn OuterOStmtOut :=
  Prover.liftContext P (lens := oLens.instContextLens)

variable [∀ i, OracleInterface (pSpec.Message i)]

def OracleVerifier.liftContext
    [oLens : OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut]
    (V : OracleVerifier pSpec oSpec InnerStmtIn InnerStmtOut InnerOStmtIn InnerOStmtOut) :
      OracleVerifier pSpec oSpec OuterStmtIn OuterStmtOut OuterOStmtIn OuterOStmtOut where
  verify := fun outerStmtIn transcript => sorry
  embed := by
    have := V.embed

    sorry
  hEq := sorry

def OracleReduction.liftContext
    [oLens : OracleContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    (R : OracleReduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut
      InnerOStmtIn InnerOStmtOut) :
      OracleReduction pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut
        OuterOStmtIn OuterOStmtOut where
  prover := R.prover.liftContext
  verifier := R.verifier.liftContext

section Execution

theorem OracleVerifier.liftContext_toVerifier_comm
    [oLens : OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut]
    {V : OracleVerifier pSpec oSpec InnerStmtIn InnerStmtOut InnerOStmtIn InnerOStmtOut} :
      V.liftContext.toVerifier = V.toVerifier.liftContext (lens := oLens.instStatementLens) := by
  sorry

def OracleReduction.liftContext_toReduction_comm
    [oLens : OracleContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                              OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {R : OracleReduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut
      InnerOStmtIn InnerOStmtOut} :
      R.liftContext.toReduction = R.toReduction.liftContext (lens := oLens.instContextLens) := by
  sorry

end Execution

section Security

variable [oSpec.FiniteRange]
  {outerRelIn : OuterStmtIn × (∀ i, OuterOStmtIn i) → OuterWitIn → Prop}
  {outerRelOut : OuterStmtOut × (∀ i, OuterOStmtOut i) → OuterWitOut → Prop}
  {innerRelIn : InnerStmtIn × (∀ i, InnerOStmtIn i) → InnerWitIn → Prop}
  {innerRelOut : InnerStmtOut × (∀ i, InnerOStmtOut i) → InnerWitOut → Prop}

namespace OracleReduction

variable
  {R : OracleReduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut
    InnerOStmtIn InnerOStmtOut}
  {completenessError : ℝ≥0}
  [lens : OracleContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
  [lensComplete : lens.instContextLens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
    (R.toReduction.compatContext lens.instContextLens)]

theorem liftContext_completeness
    (h : R.completeness innerRelIn innerRelOut completenessError) :
      R.liftContext.completeness outerRelIn outerRelOut completenessError := by
  unfold OracleReduction.completeness at h ⊢
  rw [liftContext_toReduction_comm]
  exact R.toReduction.liftContext_completeness h (lens := lens.instContextLens)

theorem liftContext_perfectCompleteness
    (h : R.perfectCompleteness innerRelIn innerRelOut) :
      R.liftContext.perfectCompleteness outerRelIn outerRelOut :=
  liftContext_completeness h

end OracleReduction

namespace OracleVerifier

variable {outerLangIn : Set (OuterStmtIn × (∀ i, OuterOStmtIn i))}
    {outerLangOut : Set (OuterStmtOut × (∀ i, OuterOStmtOut i))}
    {innerLangIn : Set (InnerStmtIn × (∀ i, InnerOStmtIn i))}
    {innerLangOut : Set (InnerStmtOut × (∀ i, InnerOStmtOut i))}
    [Inhabited InnerStmtOut] [∀ i, Inhabited (InnerOStmtOut i)]

/-- Lifting the reduction preserves soundness, assuming the lens satisfies its soundness
  conditions -/
theorem liftContext_soundness
    {soundnessError : ℝ≥0}
    [lens : OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut]
    (V : OracleVerifier pSpec oSpec InnerStmtIn InnerStmtOut InnerOStmtIn InnerOStmtOut)
    [lensSound : lens.instStatementLens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens.instStatementLens)]
    (h : V.soundness innerLangIn innerLangOut soundnessError) :
      V.liftContext.soundness outerLangIn outerLangOut soundnessError := by
  unfold OracleVerifier.soundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_soundness h (lens := lens.instStatementLens)

theorem liftContext_knowledgeSoundness [Inhabited InnerWitIn]
    {knowledgeError : ℝ≥0}
    [lens : OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut]
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (V : OracleVerifier pSpec oSpec InnerStmtIn InnerStmtOut InnerOStmtIn InnerOStmtOut)
    [lensKnowledgeSound : lens.instStatementLens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement lens.instStatementLens) (fun _ _ => True) lensInv]
    (h : V.knowledgeSoundness innerRelIn innerRelOut knowledgeError) :
      V.liftContext.knowledgeSoundness outerRelIn outerRelOut
        knowledgeError := by
  unfold OracleVerifier.knowledgeSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_knowledgeSoundness lensInv h (lens := lens.instStatementLens)

theorem liftContext_rbr_soundness
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    [lens : OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut]
    (V : OracleVerifier pSpec oSpec InnerStmtIn InnerStmtOut InnerOStmtIn InnerOStmtOut)
    [lensRBRSound : lens.instStatementLens.IsRBRSound
      outerLangIn outerLangOut innerLangIn innerLangOut
      (V.toVerifier.compatStatement lens.instStatementLens)]
    (h : V.rbrSoundness innerLangIn innerLangOut rbrSoundnessError) :
      V.liftContext.rbrSoundness outerLangIn outerLangOut rbrSoundnessError := by
  unfold OracleVerifier.rbrSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_rbr_soundness h (lens := lens.instStatementLens)

theorem liftContext_rbr_knowledgeSoundness [Inhabited InnerWitIn]
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    [lens : OStatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                              OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut]
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (V : OracleVerifier pSpec oSpec InnerStmtIn InnerStmtOut InnerOStmtIn InnerOStmtOut)
    [lensKnowledgeSound : lens.instStatementLens.IsKnowledgeSound
      outerRelIn innerRelIn outerRelOut innerRelOut
      (V.toVerifier.compatStatement lens.instStatementLens) (fun _ _ => True) lensInv]
    (h : V.rbrKnowledgeSoundness innerRelIn innerRelOut rbrKnowledgeError) :
      V.liftContext.rbrKnowledgeSoundness outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold OracleVerifier.rbrKnowledgeSoundness at h ⊢
  rw [liftContext_toVerifier_comm]
  exact V.toVerifier.liftContext_rbr_knowledgeSoundness lensInv h (lens := lens.instStatementLens)

end OracleVerifier

end Security
