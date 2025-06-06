/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Simple (Oracle) Reduction: Check if a predicate on a statement is satisfied

  This is a zero-round (oracle) reduction.

  1. Reduction version: the input relation is constant on witness, and becomes a predicate on the
  statement. Verifier checks this statement, and returns yes / no.

  Verifier may decide to keep the statement or not (send it to Unit)?

  2. Oracle reduction version: the input relation is constant on witness, and there is an oracle
  computation having as oracles the oracle statements, and taking in the (non-oracle) statement as
  an input (i.e. via `ReaderT`), and returning a `Prop`.

  Verifier performs this oracle computation, and may decide to keep the (oracle) statement or not
-/

open OracleComp ProtocolSpec

namespace CheckPred

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

section Reduction

def prover : Prover (default : ProtocolSpec 0) oSpec Statement Unit Statement Unit where
  PrvState := fun _ => Statement
  input := fun stmt _ => stmt
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun stmt => (stmt, ())

variable (pred : Statement → Prop) [DecidablePred pred]

def verifier : Verifier (default : ProtocolSpec 0) oSpec Statement Statement where
  verify := fun stmt _ => do guard (pred stmt); return stmt

def reduction : Reduction (default : ProtocolSpec 0) oSpec Statement Unit Statement Unit where
  prover := prover oSpec Statement
  verifier := verifier oSpec Statement pred

instance : ∀ i, VCVCompatible ((default : ProtocolSpec 0).Challenge i) := fun i => by aesop

variable [oSpec.FiniteRange]

/-- The `CheckPred` reduction satisfies perfect completeness. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement pred).perfectCompleteness (fun stmt _ => pred stmt)
    (fun stmt _ => pred stmt) := by
  simp [reduction, Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
    prover, verifier]
  aesop

theorem reduction_rbr_knowledge_soundness : True := sorry

end Reduction

section OracleReduction


end OracleReduction

end CheckPred
