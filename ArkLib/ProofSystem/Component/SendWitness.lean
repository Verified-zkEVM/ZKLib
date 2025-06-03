/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic

/-!
# Simple Oracle Reduction - SendWitness

- The prover sends an oracle of type `WitEquiv` (supposed to be the witness up to equivalence) to
     the verifier.
   - The verifier does nothing.
   - The output data has the same `Statement`, have output `OStatement` be the previous `OStatement`
     plus an oracle for `EncWit`, and have no witness.
   - The new relation is `rel` but replacing `Witness` with `EncWit`.

This is usually used as the first step of an oracle reduction, to replace the witness with an
oracle statement.
-/

open OracleSpec OracleComp OracleQuery

namespace SendWitness

variable {ι : Type} (oSpec : OracleSpec ι) (Statement Witness : Type)
  {ιₛᵢ : Type} (OStatement : ιₛᵢ → Type) [∀ i, OracleInterface (OStatement i)]
  (WitEquiv : Type) [OracleInterface WitEquiv] (equiv : Witness ≃ WitEquiv)

@[reducible]
def pSpec : ProtocolSpec 1 := ![(.P_to_V, WitEquiv)]

-- TODO: figure out why `OracleInterface` & `VCVCompatible` instances cannot be automatically
-- synthesized
instance : ∀ i, OracleInterface ((pSpec WitEquiv).Message i)
  | ⟨0, _⟩ => by dsimp; infer_instance
instance : ∀ i, VCVCompatible ((pSpec WitEquiv).Challenge i) | ⟨0, h⟩ => nomatch h

def prover : OracleProver (pSpec WitEquiv) oSpec Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  PrvState
  | 0 => Statement × (∀ i, OStatement i) × Witness
  | 1 => Statement × (∀ i, OStatement i) × WitEquiv
  input := fun ⟨stmt, oStmt⟩ wit => ⟨stmt, oStmt, wit⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => pure (equiv wit, ⟨stmt, oStmt, equiv wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, oStmt, encWit⟩ => (⟨stmt, (Sum.rec oStmt (fun _ => encWit))⟩, ())

def verifier : OracleVerifier (pSpec WitEquiv) oSpec Statement Statement
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  verify := fun stmt _ => pure stmt
  embed := by simp [pSpec, ProtocolSpec.MessageIdx]; sorry
  hEq := sorry

def oracleReduction : OracleReduction (pSpec WitEquiv) oSpec Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) where
  prover := prover oSpec Statement Witness OStatement WitEquiv equiv
  verifier := verifier oSpec Statement OStatement WitEquiv

variable (relIn : Statement × (∀ i, OStatement i) → Witness → Prop)

def toRelOut : Statement × (∀ i, (OStatement ⊕ᵥ (fun _ : Unit => WitEquiv)) i) → Unit → Prop :=
  fun ⟨stmt, oStmt⟩ _ => relIn ⟨stmt, fun i => oStmt (Sum.inl i)⟩ (equiv.invFun <| oStmt (.inr ()))

variable [oSpec.FiniteRange]

theorem completeness : OracleReduction.perfectCompleteness
    relIn
    (toRelOut Statement Witness OStatement WitEquiv equiv relIn)
    (oracleReduction oSpec Statement Witness OStatement WitEquiv equiv) := by
  sorry
  -- simp [OracleReduction.perfectCompleteness]

end SendWitness
