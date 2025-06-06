/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic
import Mathlib.Data.FinEnum

/-!
# Simple Oracle Reduction - SendWitness

This file contains the (oracle) reduction for the trivial one-message protocol where the prover
sends the (entire) witness to the verifier. There are two variants:

1. For oracle reduction: the witness is a finitely indexed type, and sent as a series of oracle
   statements to the verifier.

2. For reduction: the witness is a type, and sent as a statement to the verifier.
-/

open OracleSpec OracleComp OracleQuery ProtocolSpec

namespace SendWitness

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

/-!
  First, the reduction version (no oracle statements)
-/

section Reduction

variable (Witness : Type)

@[reducible, simp]
def pSpec : ProtocolSpec 1 := ![(.P_to_V, Witness)]

instance : ∀ i, VCVCompatible ((pSpec Witness).Challenge i) | ⟨0, h⟩ => nomatch h

@[inline, specialize]
def prover : Prover (pSpec Witness) oSpec Statement Witness (Statement × Witness) Unit where
  PrvState
  | 0 => Statement × Witness
  | 1 => Statement × Witness
  input := fun stmt wit => ⟨stmt, wit⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ => (⟨stmt, wit⟩, ())

@[inline, specialize]
def verifier : Verifier (pSpec Witness) oSpec Statement (Statement × Witness) where
  verify := fun stmt transcript => pure ⟨stmt, transcript 0⟩

@[inline, specialize]
def reduction : Reduction (pSpec Witness) oSpec Statement Witness (Statement × Witness) Unit where
  prover := prover oSpec Statement Witness
  verifier := verifier oSpec Statement Witness

variable {Statement} {Witness} [oSpec.FiniteRange] (relIn : Statement → Witness → Prop)

@[reducible, simp]
def toRelOut : Statement × Witness → Unit → Prop :=
  fun ⟨stmt, wit⟩ _ => relIn stmt wit

/-- The `SendWitness` reduction satisfies perfect completeness. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement Witness).perfectCompleteness relIn (toRelOut relIn) := by
  simp [Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
    reduction, prover, verifier]
  aesop

#check MonadLiftT

theorem reduction_rbr_knowledge_soundness : True := sorry

end Reduction

/-!
  Now, the oracle reduction version
-/

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  {ιw : Type} [FinEnum ιw] (Witness : ιw → Type) [∀ i, OracleInterface (Witness i)]

@[reducible, simp]
def oraclePSpec : ProtocolSpec (FinEnum.card ιw) :=
  fun i => (.P_to_V, Witness (FinEnum.equiv.symm i))

instance : IsEmpty (oraclePSpec Witness).ChallengeIdx where
  false := by aesop
instance : ∀ i, OracleInterface ((oraclePSpec Witness).Message i) :=
  fun _ => inferInstance
instance : ∀ i, VCVCompatible ((oraclePSpec Witness).Challenge i) :=
  fun _ => by aesop

end OracleReduction

end SendWitness
