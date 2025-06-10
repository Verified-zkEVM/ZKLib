/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Simple (Oracle) Reduction: Locally / non-interactively reduce a claim

  This is a zero-round (oracle) reduction.

  1. Reduction version: there are mappings between `StmtIn → StmtOut` and `WitIn → WitOut`. The
     prover and verifier applies these mappings to the input statement and witness, and returns the
     output statement and witness.

  This reduction is secure via pull-backs on relations. In other words, the outputs of the reduction
  satisfies some relation `relOut` if and only if the inputs satisfy the relation
  `relIn := relOut (mapStmt ·) (mapWit ·)`.

  2. Oracle reduction version: same as above, but with the extra mapping `OStmtIn → OStmtOut`,
     defined as an oracle simulation / embedding.

  This oracle reduction is secure via pull-backs on relations. In other words, the outputs of the
  reduction satisfies some relation `relOut` if and only if the inputs satisfy the relation
  `relIn := relOut ((mapStmt ·) ⊗ (mapOStmt ·)) (mapWit ·)`.
-/

namespace ReduceClaim

variable {ι : Type} (oSpec : OracleSpec ι) (StmtIn WitIn StmtOut WitOut : Type)
  (mapStmt : StmtIn → StmtOut) (mapWit : WitIn → WitOut)

section Reduction

/-- The prover for the `ReduceClaim` reduction. -/
def prover : Prover ![] oSpec StmtIn WitIn StmtOut WitOut where
  PrvState | 0 => StmtIn × WitIn
  input := fun stmt wit => ⟨stmt, wit⟩
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨stmt, wit⟩ => (mapStmt stmt, mapWit wit)

/-- The verifier for the `ReduceClaim` reduction. -/
def verifier : Verifier ![] oSpec StmtIn StmtOut where
  verify := fun stmt _ => pure (mapStmt stmt)

/-- The reduction for the `ReduceClaim` reduction. -/
def reduction : Reduction ![] oSpec StmtIn WitIn StmtOut WitOut where
  prover := prover oSpec StmtIn WitIn StmtOut WitOut mapStmt mapWit
  verifier := verifier oSpec StmtIn StmtOut mapStmt

variable [oSpec.FiniteRange] (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)

/-- The `ReduceClaim` reduction satisfies perfect completeness for any relation. -/
@[simp]
theorem reduction_completeness (hRel : ∀ stmtIn witIn, relIn stmtIn witIn ↔
    relOut (mapStmt stmtIn) (mapWit witIn)) :
    (reduction oSpec StmtIn WitIn StmtOut WitOut mapStmt mapWit).perfectCompleteness
      relIn relOut := by
  simp [reduction, Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
    prover, verifier, hRel]

end Reduction

section OracleReduction

variable {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)]
  {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type)
  -- Require map on indices to go the other way
  (embedIdx : ιₛₒ ↪ ιₛᵢ) (hEq : ∀ i, OStmtIn (embedIdx i) = OStmtOut i)

/-- The oracle prover for the `ReduceClaim` oracle reduction. -/
def oracleProver : OracleProver ![] oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut where
  PrvState | 0 => (StmtIn × (∀ i, OStmtIn i)) × WitIn
  input := fun stmt wit => ⟨stmt, wit⟩
  sendMessage := fun i => nomatch i
  receiveChallenge := fun i => nomatch i
  output := fun ⟨⟨stmt, oStmt⟩, wit⟩ =>
    ((mapStmt stmt, fun i => (hEq i) ▸ oStmt (embedIdx i)), mapWit wit)

/-- The oracle verifier for the `ReduceClaim` oracle reduction. -/
def oracleVerifier : OracleVerifier ![] oSpec StmtIn StmtOut OStmtIn OStmtOut where
  verify := fun stmt _ => pure (mapStmt stmt)
  embed := .trans embedIdx .inl
  hEq := by intro i; simp [hEq]

/-- The oracle reduction for the `ReduceClaim` oracle reduction. -/
def oracleReduction : OracleReduction ![] oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut where
  prover := oracleProver oSpec StmtIn WitIn StmtOut WitOut mapStmt mapWit
    OStmtIn OStmtOut embedIdx hEq
  verifier := oracleVerifier oSpec StmtIn StmtOut mapStmt OStmtIn OStmtOut embedIdx hEq

variable [oSpec.FiniteRange] (relIn : StmtIn → WitIn → Prop) (relOut : StmtOut → WitOut → Prop)

-- /-- The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. -/
-- @[simp]
-- theorem oracleReduction_completeness (hRel : ∀ stmtIn witIn, relIn stmtIn witIn ↔
--     relOut (mapStmt stmtIn) (mapWit witIn)) :
--     (oracleReduction oSpec StmtIn WitIn StmtOut WitOut OStmtIn OStmtOut embedIdx hEq).perfectCompleteness
--       relIn relOut := by
--   sorry


end OracleReduction

end ReduceClaim
