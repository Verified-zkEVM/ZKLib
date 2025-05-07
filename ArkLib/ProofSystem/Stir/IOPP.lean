import ArkLib.OracleReduction.Security.Basic
import Mathlib.Tactic


namespace Reduction
open OracleComp OracleSpec ProtocolSpec
open scoped NNReal

variable {n : ℕ} {ι : Type}

section IOPP

/-- An *interactive-oracle proof of proximity* (IOPP) is just an
    `OracleProof … Bool Unit` enriched with three security guarantees. -/
structure IOPP
    (pSpec : ProtocolSpec n) (oSpec : OracleSpec ι)
    [∀ i, VCVCompatible (pSpec.Challenge i)][oSpec.FiniteRange]
    [∀ i, ToOracle (pSpec.Message i)]
    (StmtIn WitIn StmtOut : Type)
    { ιₛₒ: Type} (OStmtOut : ιₛₒ → Type)[∀ i, ToOracle (OStmtOut i)] where

  /-- The underlying interactive-oracle proof (Boolean output). -/
  iop : OracleProof pSpec oSpec StmtIn WitIn OStmtOut


  relIn  : StmtIn  → WitIn → Prop
  relOut : Bool → Unit → Prop
  reduction : Reduction pSpec oSpec StmtIn WitIn Bool Unit

  ioppCompleteness : perfectCompleteness relIn relOut reduction

  /-- Set of valid input statements.  (Usually `proj₁ '' relIn`.) -/
  langIn : Set StmtIn
  langOut : Set StmtOut
  /-- One-shot soundness error. -/
  ε_sound : ℝ≥0
  verifier : Verifier pSpec oSpec StmtIn StmtOut

  ioppSoundness : soundness langIn langOut verifier ε_sound

  /-- A *state function* used for round-by-round soundness. -/
  stateFn :
    StateFunction langIn langOut verifier

  /-- Per-round RBR error budget. -/
  ε_rbr : pSpec.ChallengeIndex → ℝ≥0

  ioppRBRSoundness : rbrSoundness langIn langOut verifier stateFn ε_rbr

end IOPP
end Reduction
