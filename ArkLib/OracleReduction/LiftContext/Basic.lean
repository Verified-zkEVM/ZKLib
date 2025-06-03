import ArkLib.OracleReduction.Security.Basic
import ToMathlib.PFunctor.Basic

/-!
  ## Lifting (Oracle) Reductions to Larger Contexts

  Sequential composition is usually not enough to represent oracle reductions in a modular way. We
  also need to formalize **virtual** oracle reductions, which lift reductions from one
  (virtual / inner) context into the another (real / outer) context.

  This is what is meant when we informally say "apply so-and-so protocol to this quantity (derived
  from the input statement & witness)".

  Put in other words, we define a mapping between the input-output interfaces of two (oracle)
  reductions, without changing anything about the underlying reductions.

  Recall that the input-output interface of an oracle reduction consists of:
  - Input: `OuterStmtIn : Type`, `OuterOStmtIn : ιₛᵢ → Type`, and `OuterWitIn : Type`
  - Output: `OuterStmtOut : Type`, `OuterOStmtOut : ιₛₒ → Type`, and `OuterWitOut : Type`

  The liftContext is defined as the following mappings of projections / lifts:

  - `projStmt : OuterStmtIn → InnerStmtIn`
  - `projOStmt : (simulation involving OuterOStmtIn to produce InnerOStmtIn)`
  - `projWit : OuterWitIn → InnerWitIn`
  - `liftStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut`
  - `liftOStmt : (simulation involving InnerOStmtOut to produce OuterOStmtOut)`
  - `liftWit : OuterWitIn × InnerWitOut → OuterWitOut`

  Note that since completeness & soundness for oracle reductions are defined in terms of the same
  properties after converting to (non-oracle) reductions, we only need to focus our efforts on the
  non-oracle case.

  Note that this _exactly_ corresponds to lenses in programming languages / category theory.
  Namely, liftContext on the inputs correspond to a `view`/`get` operation (our "proj"), while
  liftContext on the output corresponds to a `modify`/`set` operation (our "lift").

  More precisely, the `proj/lift` operations correspond to a Lens between two monomial polyonmial
  functors: `OuterCtxIn y^ OuterCtxOut ⇆ InnerCtxIn y^ InnerCtxOut`.

  What are some expected properties of the liftContext (via the connection to lenses)?

  First, we recall the expected properties of lenses:

  1. `get(lens, set(lens, value, store)) = value`
  2. `set(lens, new, set(lens, old, store)) = set(lens, new, store)`
  3. `set(lens, get(lens, store), store) = store`
  4. and more

  What should this mean here?
  - one property not mentioned above, is that the pre-image of `projInput` should be invariant
    for `liftOutput`.

  That is, if `projInput(inp1) = projInput(inp2) = inp*`, then `liftOutput(inp1, out)
  = liftOutput(inp2, out)` for all `out` which is a possible result of running the oracle
  reduction on `inp*`. This basically implies a decomposition of sorts between the input to be
  transported.
-/

open OracleSpec OracleComp ProtocolSpec

section Transport

open scoped NNReal

/-- A lens for transporting (non-oracle) statements between outer and inner contexts -/
class StatementLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type) where
  projStmt : OuterStmtIn → InnerStmtIn
  liftStmt : OuterStmtIn × InnerStmtOut → OuterStmtOut

#check ReaderT.run

/-- A lens for transporting oracle statements between outer and inner contexts

We require knowledge of the (non-oracle) input statement in the outer context, along with the
(non-oracle) output statement in the inner context. -/
class OStatementLens (OuterStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
  where
  -- To access an input oracle statement in the inner context, we may simulate it using the input
  -- (non-oracle) statement of the outer context, along with oracle access to the outer input oracle
  -- statements
  projOStmt : ∀ i, OuterOStmtIn i → ∀ i, InnerOStmtIn i

  simOStmt : QueryImpl [InnerOStmtIn]ₒ
    (ReaderT OuterStmtIn (OracleComp [OuterOStmtIn]ₒ))

  -- simOStmt_eq_projOStmt :

  -- projOStmt_neverFails : ∀ i, ∀ t, ∀ outerStmtIn,
  --   ((projOStmt.impl (query i t)).run outerStmtIn).neverFails
  -- To get back an output oracle statement in the outer context, we may simulate it using the input
  -- (non-oracle) statement of the outer context, the output (non-oracle) statement of the inner
  -- context, along with oracle access to the inner output oracle statements
  liftOStmt : QueryImpl [OuterOStmtOut]ₒ
    (ReaderT (OuterStmtIn × InnerStmtOut) (OracleComp ([OuterOStmtIn]ₒ ++ₒ [InnerOStmtOut]ₒ)))
  liftOStmt_neverFails : ∀ i, ∀ t, ∀ outerStmtIn, ∀ innerStmtOut,
    ((liftOStmt.impl (query i t)).run (outerStmtIn, innerStmtOut)).neverFails

/-- A lens for transporting witnesses between outer and inner contexts -/
class WitnessLens (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) where
  projWit : OuterWitIn → InnerWitIn
  liftWit : OuterWitIn × InnerWitOut → OuterWitOut

/-- A lens for transporting between outer and inner contexts of a (non-oracle) reduction -/
class ContextLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type)
    extends StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut,
      WitnessLens OuterWitIn OuterWitOut InnerWitIn InnerWitOut

/-- A lens for transporting between outer and inner contexts of an oracle reduction -/
class OracleContextLens (OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type)
    {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
    {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
    {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
    {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
    (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) extends

      StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut,

      OStatementLens OuterStmtIn InnerStmtOut
        OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut,

      WitnessLens OuterWitIn OuterWitOut InnerWitIn InnerWitOut

namespace OracleContextLens

#check OracleComp.simulateQ

variable {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
  {Outer_ιₛᵢ : Type} (OuterOStmtIn : Outer_ιₛᵢ → Type) [∀ i, OracleInterface (OuterOStmtIn i)]
  {Outer_ιₛₒ : Type} (OuterOStmtOut : Outer_ιₛₒ → Type) [∀ i, OracleInterface (OuterOStmtOut i)]
  {Inner_ιₛᵢ : Type} (InnerOStmtIn : Inner_ιₛᵢ → Type) [∀ i, OracleInterface (InnerOStmtIn i)]
  {Inner_ιₛₒ : Type} (InnerOStmtOut : Inner_ιₛₒ → Type) [∀ i, OracleInterface (InnerOStmtOut i)]
  {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
  {oLens : OracleContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                            OuterOStmtIn OuterOStmtOut InnerOStmtIn InnerOStmtOut
                            OuterWitIn OuterWitOut InnerWitIn InnerWitOut}

/-- Converting an oracle context lens to a non-oracle context lens, via moving oracle statements
into non-oracle statements -/
instance instContextLens : ContextLens
    (OuterStmtIn × ∀ i, OuterOStmtIn i) (OuterStmtOut × ∀ i, OuterOStmtOut i)
    (InnerStmtIn × ∀ i, InnerOStmtIn i) (InnerStmtOut × ∀ i, InnerOStmtOut i)
    OuterWitIn OuterWitOut InnerWitIn InnerWitOut where
  projStmt := fun ⟨outerStmtIn, outerOStmtIn⟩ =>
    ⟨oLens.projStmt outerStmtIn, sorry⟩
  liftStmt := fun ⟨outerStmtIn, innerStmtOut⟩ => sorry
  projWit := fun outerWitIn => sorry
  liftWit := fun ⟨outerWitIn, innerWitOut⟩ => sorry

end OracleContextLens


/-
  Recall the interface of an extractor:
  - Takes in `WitOut`, `StmtIn`, `Transcript`, `QueryLog`
  (note: no need for `StmtOut` as it can be derived from `StmtIn`, `Transcript`, and `QueryLog`)
  - Returns `WitIn`

  We need a lens for the extractor as well.

  Assume we have an inner extractor
    `E : InnerWitOut → InnerStmtIn → Transcript → QueryLog → InnerWitIn`

  We need to derive an outer extractor
    `E' : OuterWitOut → OuterStmtIn → Transcript → QueryLog → OuterWitIn`

  Note that `Transcript` and `QueryLog` are the same due to the lens only changing the
  input-output interface, and not the inside (oracle) reduction.

  So, `E' outerWitOut outerStmtIn transcript queryLog` needs to call
    `E (map to innerWitOut) (projStmt outerStmtIn) transcript queryLog`
  and then post-process the result, which is some `innerWitIn`, to get some `outerWitIn`.

  This processing is exactly the same as a lens in the opposite direction between the outer and
  inner witness types.
-/

/-- Inverse lens between outer and inner witnesses (going the other direction with respect to
  input-output), for extractors / knowledge soundness.
-/
@[reducible]
def WitnessLensInv (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) :=
  WitnessLens OuterWitOut OuterWitIn InnerWitOut InnerWitIn
-- structure ContextLensInv (OuterStmtOut InnerStmtOut : Type)
--     (OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type) extends
--       WitnessLens OuterWitOut OuterWitIn InnerWitOut InnerWitIn where
--   projStmt : OuterStmtOut → InnerStmtOut
  -- projWitInv : InnerWitOut → OuterWitOut
  -- liftWitInv : InnerWitIn × OuterWitOut → OuterWitIn

/-- For round-by-round knowledge soundness, we require an _equivalence_ on the input witness
  (inner <=> outer). Otherwise, we cannot extract.

  (imagine a reduction from R1 x R2 => R3 x R4, that is the sequential composition of R1 => R3 and
  then R2 => R4. This reduction is not round-by-round knowledge sound, since if we are in the
  R1 => R3 rounds, we have no way of invoking the second extractor for recovering the witness for
  R2.)-/
class RBRWitnessLensInv (OuterWitIn InnerWitIn : Type) where
  liftWit : InnerWitIn → OuterWitIn

/-- Conditions for the lens / transformation to preserve completeness

For `lift`, we require compatibility relations between the outer input statement/witness and
the inner output statement/witness -/
class ContextLens.IsComplete {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compat : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → Prop)
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  proj_complete : ∀ stmtIn witIn,
    outerRelIn stmtIn witIn →
    innerRelIn (lens.projStmt stmtIn) (lens.projWit witIn)

  lift_complete : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    outerRelIn outerStmtIn outerWitIn →
    innerRelOut innerStmtOut innerWitOut →
    compat (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) →
    outerRelOut (lens.liftStmt (outerStmtIn, innerStmtOut))
                (lens.liftWit (outerWitIn, innerWitOut))

/-- Conditions for the lens / transformation to preserve soundness -/
class StatementLens.IsSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compat : OuterStmtIn → InnerStmtOut → Prop)
    (stmtLens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → stmtLens.projStmt outerStmtIn ∉ innerLangIn

  lift_sound : ∀ outerStmtIn innerStmtOut,
    outerStmtIn ∉ outerLangIn →
    innerStmtOut ∉ innerLangOut →
    compat outerStmtIn innerStmtOut →
      stmtLens.liftStmt (outerStmtIn, innerStmtOut) ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve round-by-round soundness

This is nearly identical to the `IsSound` condition, _except_ that we do not require
`outerStmtIn ∉ outerLangIn` in the `lift_sound` condition.

(we need to relax that condition to prove `toFun_full` of the lifted state function) -/
class StatementLens.IsRBRSound {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (compat : OuterStmtIn → InnerStmtOut → Prop)
    (stmtLens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut) where

  proj_sound : ∀ outerStmtIn,
    outerStmtIn ∉ outerLangIn → stmtLens.projStmt outerStmtIn ∉ innerLangIn

  lift_sound : ∀ outerStmtIn innerStmtOut,
    innerStmtOut ∉ innerLangOut →
    compat outerStmtIn innerStmtOut →
      stmtLens.liftStmt (outerStmtIn, innerStmtOut) ∉ outerLangOut

/-- Conditions for the lens / transformation to preserve knowledge soundness

(TODO: double-check) -/
class ContextLens.IsKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)
    (compat : OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → Prop)
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut) where

  /-- Projecting using the inverse lens from outer to inner context preserves satisfaction of
    relations -/
  proj_knowledge_sound : ∀ outerStmtIn outerWitIn,
    outerRelIn outerStmtIn outerWitIn →
    innerRelIn (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)

  lift_knowledge_sound : ∀ outerStmtIn outerWitIn innerStmtOut innerWitOut,
    outerRelIn outerStmtIn outerWitIn →
    innerRelOut innerStmtOut innerWitOut →
    compat (outerStmtIn, outerWitIn) (innerStmtOut, innerWitOut) →
    outerRelOut (lens.liftStmt (outerStmtIn, innerStmtOut))
                (lens.liftWit (outerWitIn, innerWitOut))

namespace ContextLens.IsKnowledgeSound

-- Convert knowledge soundness into soundness

end ContextLens.IsKnowledgeSound

class ContextLens.IsRBRKnowledgeSound
    {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (outerRelIn : OuterStmtIn → OuterWitIn → Prop)
    (innerRelIn : InnerStmtIn → InnerWitIn → Prop)
    (outerRelOut : OuterStmtOut → OuterWitOut → Prop)
    (innerRelOut : InnerStmtOut → InnerWitOut → Prop)

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut : Type}
  {InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut : Type}
  [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- The outer prover after lifting invokes the inner prover on the projected input, and
  lifts the output -/
def Prover.liftContext
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      Prover pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut where
  PrvState := fun i => P.PrvState i × OuterStmtIn × OuterWitIn
  input := fun stmtIn witIn =>
    ⟨P.input (lens.projStmt stmtIn) (lens.projWit witIn), stmtIn, witIn⟩
  sendMessage := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨msg, prvState'⟩ ← P.sendMessage i prvState
    return ⟨msg, ⟨prvState', stmtIn, witIn⟩⟩
  receiveChallenge := fun i ⟨prvState, stmtIn, witIn⟩ chal =>
    ⟨P.receiveChallenge i prvState chal, stmtIn, witIn⟩
  output := fun ⟨prvState, stmtIn, witIn⟩ =>
    let ⟨innerStmtOut, innerWitOut⟩ := P.output prvState
    ⟨lens.liftStmt (stmtIn, innerStmtOut), lens.liftWit (witIn, innerWitOut)⟩

/-- The outer verifier after lifting invokes the inner verifier on the projected input, and
  lifts the output -/
def Verifier.liftContext
    [lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut]
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut) :
      Verifier pSpec oSpec OuterStmtIn OuterStmtOut where
  verify := fun stmtIn transcript => do
    let innerStmtIn := lens.projStmt stmtIn
    let innerStmtOut ← V.verify innerStmtIn transcript
    return lens.liftStmt (stmtIn, innerStmtOut)

/-- The outer reduction after lifting is the combination of the lifting of the prover and
  verifier -/
def Reduction.liftContext
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      Reduction pSpec oSpec OuterStmtIn OuterWitIn OuterStmtOut OuterWitOut where
  prover := R.prover.liftContext
  verifier := R.verifier.liftContext

open Verifier in
/-- The outer extractor after lifting invokes the inner extractor on the projected input, and
  lifts the output -/
def StraightlineExtractor.liftContext
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    [lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    (E : StraightlineExtractor pSpec oSpec InnerStmtIn InnerWitIn InnerWitOut) :
      StraightlineExtractor pSpec oSpec OuterStmtIn OuterWitIn OuterWitOut :=
  fun outerWitOut outerStmtIn fullTranscript proveQueryLog verifyQueryLog =>
    let innerStmtIn := lens.projStmt outerStmtIn
    let innerWitOut := lensInv.projWit outerWitOut
    let innerWitIn := E innerWitOut innerStmtIn fullTranscript proveQueryLog verifyQueryLog
    lensInv.liftWit (outerWitOut, innerWitIn)

open Verifier in
/-- The outer round-by-round extractor after lifting invokes the inner extractor on the projected
  input, and lifts the output -/
def RBRExtractor.liftContext
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    [rbrLensInv : RBRWitnessLensInv OuterWitIn InnerWitIn]
    (E : RBRExtractor pSpec oSpec InnerStmtIn InnerWitIn) :
      RBRExtractor pSpec oSpec OuterStmtIn OuterWitIn :=
  fun roundIdx outerStmtIn fullTranscript proveQueryLog =>
    rbrLensInv.liftWit (E roundIdx (lens.projStmt outerStmtIn) fullTranscript proveQueryLog)

/-- Compatibility relation between the outer input statement and the inner output statement,
relative to a verifier.

We require that the inner output statement is a possible output of the verifier on the outer
input statement, for any given transcript. Note that we have to existentially quantify over
transcripts since we only reference the verifier, and there's no way to get the transcript without
a prover. -/
def Verifier.compatStatement {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    (lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut) :
      OuterStmtIn → InnerStmtOut → Prop :=
  fun outerStmtIn innerStmtOut =>
    innerStmtOut ∈ ⋃ transcript, (V.run (lens.projStmt outerStmtIn) transcript).support

/-- Compatibility relation between the outer input context and the inner output context, relative
to a reduction.

We require that the inner output context (statement + witness) is a possible output of the reduction
on the outer input context (statement + witness). -/
def Reduction.compatContext {OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut : Type}
    {OuterWitIn OuterWitOut InnerWitIn InnerWitOut : Type}
    (lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
      OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      OuterStmtIn × OuterWitIn → InnerStmtOut × InnerWitOut → Prop :=
  fun ⟨outerStmtIn, outerWitIn⟩ innerContextOut =>
    innerContextOut ∈
      Prod.fst <$> (R.run (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)).support

/-- The outer state function after lifting invokes the inner state function on the projected
  input, and lifts the output -/
def Verifier.StateFunction.liftContext [oSpec.FiniteRange]
    [lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut]
    (outerLangIn : Set OuterStmtIn) (outerLangOut : Set OuterStmtOut)
    (innerLangIn : Set InnerStmtIn) (innerLangOut : Set InnerStmtOut)
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    [lensRBRSound : lens.IsRBRSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (stF : V.StateFunction pSpec oSpec innerLangIn innerLangOut) :
      V.liftContext.StateFunction pSpec oSpec outerLangIn outerLangOut
where
  toFun := fun m outerStmtIn transcript =>
    stF m (lens.projStmt outerStmtIn) transcript
  toFun_empty := fun stmt hStmt =>
    stF.toFun_empty (lens.projStmt stmt) (lensRBRSound.proj_sound stmt hStmt)
  toFun_next := fun m hDir outerStmtIn transcript hStmt msg =>
    stF.toFun_next m hDir (lens.projStmt outerStmtIn) transcript hStmt msg
  toFun_full := fun outerStmtIn transcript hStmt => by
    have h := stF.toFun_full (lens.projStmt outerStmtIn) transcript hStmt
    simp [Verifier.run, Verifier.liftContext] at h ⊢
    intro innerStmtOut hSupport
    apply lensRBRSound.lift_sound
    · exact h innerStmtOut hSupport
    · simp [compatStatement]; exact ⟨transcript, hSupport⟩

-- def OracleProver.liftContext

-- def OracleVerifier.liftContext

-- def OracleReduction.liftContext

section Theorems

/- Theorems about liftContext interacting with reduction execution and security properties -/

section Prover

/- Breaking down the intertwining of liftContext and prover execution -/

/-- Lifting the prover intertwines with the process round function -/
theorem Prover.liftContext_processRound
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {i : Fin n}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut)
    {resultRound : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
      (pSpec.Transcript i.castSucc × P.liftContext.PrvState i.castSucc)} :
      (P.liftContext (lens := lens)).processRound i resultRound
      = do
        let ⟨transcript, prvState, outerStmtIn, outerWitIn⟩ ← resultRound
        let ⟨newTranscript, newPrvState⟩ ← P.processRound i (do return ⟨transcript, prvState⟩)
        return ⟨newTranscript, ⟨newPrvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold processRound liftContext
  simp
  congr 1; funext
  split <;> simp

/-- Lemma needed for the proof of `Prover.liftContext_runToRound` -/
private lemma Prover.bind_map_processRound_pure {i : Fin n}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut)
    (comp : OracleComp (oSpec ++ₒ [pSpec.Challenge]ₒ)
        (pSpec.Transcript i.castSucc × P.PrvState i.castSucc))
    {α : Type} (f : pSpec.Transcript i.succ × P.PrvState i.succ → α) :
      (do let result ← comp; f <$> P.processRound i (pure result))
      = f <$> P.processRound i comp := by
  simp [processRound]

theorem Prover.liftContext_runToRound
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (P.liftContext (lens := lens)).runToRound i outerStmtIn outerWitIn
      = do
        let ⟨transcript, prvState⟩ ←
          P.runToRound i (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)
        return ⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩⟩ := by
  unfold runToRound
  induction i using Fin.induction with
  | zero => simp [liftContext]
  | succ i ih => simp [liftContext_processRound, ih, bind_map_processRound_pure]

-- Requires more lemmas about `simulateQ` for logging oracles
theorem Prover.liftContext_runWithLogToRound
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn} {i : Fin (n + 1)}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      (P.liftContext (lens := lens)).runWithLogToRound i outerStmtIn outerWitIn
      = do
        let ⟨transcript, prvState, queryLog⟩ ←
          P.runWithLogToRound i (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)
        return ⟨transcript, ⟨prvState, outerStmtIn, outerWitIn⟩, queryLog⟩ := by
  unfold runWithLogToRound
  induction i using Fin.induction with
  | zero => simp [liftContext]
  | succ i ih => simp [liftContext_runToRound]

/-- Running the lifted outer prover is equivalent to running the inner prover on the projected
  input, and then integrating the output -/
theorem Prover.liftContext_run
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      P.liftContext.run outerStmtIn outerWitIn
      = do
        let ⟨innerStmtOut, innerWitOut, fullTranscript⟩ ←
          P.run (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)
        return ⟨lens.liftStmt (outerStmtIn, innerStmtOut),
                lens.liftWit (outerWitIn, innerWitOut),
                fullTranscript⟩ := by
  simp only [Prover.run, liftContext_runToRound]
  simp [liftContext]

/- Lifting the prover intertwines with the runWithLog function -/
theorem Prover.liftContext_runWithLog
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (P : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      P.liftContext.runWithLog outerStmtIn outerWitIn
      = do
        let ⟨innerStmtOut, innerWitOut, fullTranscript, queryLog⟩ ←
          P.runWithLog (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)
        return ⟨lens.liftStmt (outerStmtIn, innerStmtOut),
                lens.liftWit (outerWitIn, innerWitOut),
                fullTranscript,
                queryLog⟩ := by
  simp only [runWithLog, liftContext_runWithLogToRound]
  simp [liftContext]

end Prover

theorem Reduction.liftContext_run
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      R.liftContext.run outerStmtIn outerWitIn = do
        let ⟨⟨prvInnerStmtOut, innerWitOut⟩, verInnerStmtOut, fullTranscript⟩ ←
          R.run (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)
        return ⟨⟨lens.liftStmt (outerStmtIn, prvInnerStmtOut),
                lens.liftWit (outerWitIn, innerWitOut)⟩,
                lens.liftStmt (outerStmtIn, verInnerStmtOut),
                fullTranscript⟩ := by
  unfold Reduction.run
  simp [Reduction.liftContext, Prover.liftContext_run, Verifier.liftContext, Verifier.run]

theorem Reduction.liftContext_runWithLog
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    {outerStmtIn : OuterStmtIn} {outerWitIn : OuterWitIn}
    (R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut) :
      R.liftContext.runWithLog outerStmtIn outerWitIn = do
        let ⟨⟨prvInnerStmtOut, innerWitOut⟩, verInnerStmtOut, fullTranscript, queryLog⟩ ←
          R.runWithLog (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)
        return ⟨⟨lens.liftStmt (outerStmtIn, prvInnerStmtOut),
          lens.liftWit (outerWitIn, innerWitOut)⟩,
          lens.liftStmt (outerStmtIn, verInnerStmtOut), fullTranscript, queryLog⟩ := by
  unfold Reduction.runWithLog
  simp [Reduction.liftContext, Prover.liftContext_runWithLog, Verifier.liftContext, Verifier.run]

variable [oSpec.FiniteRange]

section Completeness

variable
    {outerRelIn : OuterStmtIn → OuterWitIn → Prop} {outerRelOut : OuterStmtOut → OuterWitOut → Prop}
    {innerRelIn : InnerStmtIn → InnerWitIn → Prop} {innerRelOut : InnerStmtOut → InnerWitOut → Prop}
    {R : Reduction pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut}
    {completenessError : ℝ≥0}
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                    OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    [lensComplete : lens.IsComplete outerRelIn innerRelIn outerRelOut innerRelOut
      (R.compatContext lens)]

/--
  Lifting the reduction preserves completeness, assuming the lens satisfies its completeness
  conditions
-/
theorem Reduction.liftContext_completeness
    (h : R.completeness innerRelIn innerRelOut completenessError) :
      R.liftContext.completeness outerRelIn outerRelOut completenessError := by
  unfold completeness at h ⊢
  intro outerStmtIn outerWitIn hRelIn
  have hR := h (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)
    (lensComplete.proj_complete _ _ hRelIn)
  rw [Reduction.liftContext_run]
  refine le_trans hR ?_
  simp
  refine probEvent_mono ?_
  intro ⟨innerContextOut, a, b⟩ hSupport ⟨hRelOut, hRelOut'⟩
  have : innerContextOut ∈
      Prod.fst <$> (R.run (lens.projStmt outerStmtIn) (lens.projWit outerWitIn)).support := by
    simp
    exact ⟨a, b, hSupport⟩
  simp_all
  refine lensComplete.lift_complete _ _ _ _ hRelIn hRelOut ?_
  rw [← hRelOut']
  simp [compatContext]; exact this

-- Can't turn the above into an instance because Lean needs to synthesize `innerRelIn` and
-- `innerRelOut` out of thin air.

-- instance [Reduction.IsComplete innerRelIn innerRelOut R completenessError] :
--     R.liftContext.IsComplete outerRelIn outerRelOut completenessError :=
--   ⟨R.liftContext.completeness⟩

-- instance [R.IsPerfectComplete relIn relOut] :
--     R.liftContext.IsPerfectComplete relIn relOut :=
--   ⟨fun _ => R.liftContext.perfectCompleteness _ _ _⟩

end Completeness

/-- Lifting the reduction preserves soundness, assuming the lens satisfies its soundness
  conditions -/
theorem Verifier.liftContext_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {soundnessError : ℝ≥0}
    [lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut]
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    -- TODO: figure out the right compatibility relation for the IsSound condition
    [lensSound : lens.IsSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.soundness innerLangIn innerLangOut soundnessError) :
      V.liftContext.soundness outerLangIn outerLangOut soundnessError := by
  unfold soundness Reduction.run at h ⊢
  -- Note: there is no distinction between `Outer` and `Inner` here
  intro WitIn WitOut outerWitIn outerP outerStmtIn hOuterStmtIn
  simp at h ⊢
  have innerP : Prover pSpec oSpec InnerStmtIn WitIn InnerStmtOut WitOut := {
    PrvState := outerP.PrvState
    input := fun _ _ => outerP.input outerStmtIn outerWitIn
    sendMessage := outerP.sendMessage
    receiveChallenge := outerP.receiveChallenge
    output := fun state =>
      let ⟨outerStmtOut, outerWitOut⟩ := outerP.output state
      ⟨default, outerWitOut⟩
  }
  have : lens.projStmt outerStmtIn ∉ innerLangIn := by
    apply lensSound.proj_sound
    exact hOuterStmtIn
  have hSound := h WitIn WitOut outerWitIn innerP (lens.projStmt outerStmtIn) this
  refine le_trans ?_ hSound
  simp [Verifier.liftContext, Verifier.run]
  -- Need to massage the two `probEvent`s so that they have the same base computation `oa`
  -- Then apply `lensSound.lift_sound`?
  sorry

/-
  Lifting the reduction preserves knowledge soundness, assuming the lens satisfies its
  knowledge soundness conditions
-/
theorem Verifier.liftContext_knowledgeSoundness [Inhabited InnerStmtOut]
    {outerRelIn : OuterStmtIn → OuterWitIn → Prop} {outerRelOut : OuterStmtOut → OuterWitOut → Prop}
    {innerRelIn : InnerStmtIn → InnerWitIn → Prop} {innerRelOut : InnerStmtOut → InnerWitOut → Prop}
    {knowledgeError : ℝ≥0}
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    [lensKnowledgeSound : lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (fun _ _ => True) lensInv]
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    (h : V.knowledgeSoundness innerRelIn innerRelOut knowledgeError) :
      V.liftContext.knowledgeSoundness outerRelIn outerRelOut
        knowledgeError := by
  unfold knowledgeSoundness at h ⊢
  obtain ⟨E, h'⟩ := h
  refine ⟨E.liftContext (lens := lens), ?_⟩
  intro outerStmtIn outerWitIn outerP
  simp [StraightlineExtractor.liftContext]
  let innerP : Prover pSpec oSpec InnerStmtIn InnerWitIn InnerStmtOut InnerWitOut :=
    {
      PrvState := outerP.PrvState
      input := fun _ _ => outerP.input outerStmtIn outerWitIn
      sendMessage := outerP.sendMessage
      receiveChallenge := outerP.receiveChallenge
      output := fun state =>
        let ⟨outerStmtOut, outerWitOut⟩ := outerP.output state
        ⟨default, lensInv.projWit outerWitOut⟩
    }
  have h_innerP_input {innerStmtIn} {innerWitIn} :
      innerP.input innerStmtIn innerWitIn = outerP.input outerStmtIn outerWitIn := rfl
  have hR := h' (lens.projStmt outerStmtIn) (lens.projWit outerWitIn) innerP
  simp at hR
  simp [Reduction.runWithLog, Verifier.liftContext, Verifier.run] at hR ⊢
  have h_innerP_runWithLog {innerStmtIn} {innerWitIn} :
      innerP.runWithLog innerStmtIn innerWitIn
      = do
        let ⟨_, outerWitOut, rest⟩ ← outerP.runWithLog outerStmtIn outerWitIn
        return ⟨default, lensInv.projWit outerWitOut, rest⟩ := by
    sorry
  refine le_trans ?_ hR
  -- Massage the two `probEvent`s so that they have the same base computation `oa`?
  simp [h_innerP_runWithLog]
  -- apply probEvent_mono ?_
  sorry

/-
  Lifting the reduction preserves round-by-round soundness, assuming the lens satisfies its
  soundness conditions
-/
theorem Verifier.liftContext_rbr_soundness [Inhabited InnerStmtOut]
    {outerLangIn : Set OuterStmtIn} {outerLangOut : Set OuterStmtOut}
    {innerLangIn : Set InnerStmtIn} {innerLangOut : Set InnerStmtOut}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    [lens : StatementLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut]
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    -- TODO: figure out the right compatibility relation for the IsSound condition
    [lensRBRSound : lens.IsRBRSound outerLangIn outerLangOut innerLangIn innerLangOut
      (V.compatStatement lens)]
    (h : V.rbrSoundness innerLangIn innerLangOut rbrSoundnessError) :
      V.liftContext.rbrSoundness outerLangIn outerLangOut rbrSoundnessError := by
  unfold rbrSoundness at h ⊢
  obtain ⟨stF, h⟩ := h
  simp at h ⊢
  refine ⟨stF.liftContext (lens := lens) (lensRBRSound := lensRBRSound), ?_⟩
  intro outerStmtIn hOuterStmtIn WitIn WitOut witIn outerP roundIdx hDir
  have innerP : Prover pSpec oSpec InnerStmtIn WitIn InnerStmtOut WitOut := {
    PrvState := outerP.PrvState
    input := fun _ _ => outerP.input outerStmtIn witIn
    sendMessage := outerP.sendMessage
    receiveChallenge := outerP.receiveChallenge
    output := fun state =>
      let ⟨outerStmtOut, outerWitOut⟩ := outerP.output state
      ⟨default, outerWitOut⟩
  }
  have h' := h (lens.projStmt outerStmtIn) (lensRBRSound.proj_sound _ hOuterStmtIn)
    WitIn WitOut witIn innerP roundIdx hDir
  refine le_trans ?_ h'
  sorry

/-
  Lifting the reduction preserves round-by-round knowledge soundness, assuming the lens
  satisfies its knowledge soundness conditions
-/
theorem Verifier.liftContext_rbr_knowledgeSoundness
    {outerRelIn : OuterStmtIn → OuterWitIn → Prop} {outerRelOut : OuterStmtOut → OuterWitOut → Prop}
    {innerRelIn : InnerStmtIn → InnerWitIn → Prop} {innerRelOut : InnerStmtOut → InnerWitOut → Prop}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    [lens : ContextLens OuterStmtIn OuterStmtOut InnerStmtIn InnerStmtOut
                        OuterWitIn OuterWitOut InnerWitIn InnerWitOut]
    (lensInv : WitnessLensInv OuterWitIn OuterWitOut InnerWitIn InnerWitOut)
    [lensKnowledgeSound : lens.IsKnowledgeSound outerRelIn innerRelIn outerRelOut innerRelOut
      (fun _ _ => True) lensInv]
    (V : Verifier pSpec oSpec InnerStmtIn InnerStmtOut)
    (h : V.rbrKnowledgeSoundness innerRelIn innerRelOut rbrKnowledgeError) :
      V.liftContext.rbrKnowledgeSoundness outerRelIn outerRelOut
        rbrKnowledgeError := by
  unfold rbrKnowledgeSoundness at h ⊢
  obtain ⟨stF, E, h⟩ := h
  simp at h ⊢
  -- refine ⟨stF.liftContext (lens := lens.toStatementLens)
  --   (lensSound := lensKnowledgeSound.toSound),
  --         ?_, ?_⟩
  sorry


-- TODO: state definitions & theorems about oracle reduction as well

-- def OracleReduction.liftContext_eq_reduction_liftContext

-- def OracleReduction.liftContext_completeness

-- def OracleVerifier.liftContext_soundness

-- def OracleVerifier.liftContext_knowledgeSoundness

-- def OracleVerifier.liftContext_rbr_soundness

-- def OracleVerifier.liftContext_rbr_knowledgeSoundness

end Theorems

end Transport

section Test

open Polynomial

-- Testing out sum-check-like relations

noncomputable section

def OuterStmtIn_Test := ℤ[X] × ℤ[X] × ℤ
def InnerStmtIn_Test := ℤ[X] × ℤ

def outerRelIn_Test : OuterStmtIn_Test → Unit → Prop :=
  fun ⟨p, q, t⟩ _ => ∑ x ∈ {0, 1}, (p * q).eval x = t
def innerRelIn_Test : InnerStmtIn_Test → Unit → Prop :=
  fun ⟨f, t⟩ _ => ∑ x ∈ {0, 1}, f.eval x = t

def OuterStmtOut_Test := ℤ[X] × ℤ[X] × ℤ × ℤ
def InnerStmtOut_Test := ℤ[X] × ℤ × ℤ

def outerRelOut_Test : OuterStmtOut_Test → Unit → Prop :=
  fun ⟨p, q, t, r⟩ _ => (p * q).eval r = t
def innerRelOut_Test : InnerStmtOut_Test → Unit → Prop :=
  fun ⟨f, t, r⟩ _ => f.eval r = t

def testLens :
    ContextLens OuterStmtIn_Test OuterStmtOut_Test InnerStmtIn_Test InnerStmtOut_Test
                Unit Unit Unit Unit where
  projStmt := fun ⟨p, q, t⟩ => ⟨p * q, t⟩
  liftStmt := fun ⟨⟨p, q, _⟩, ⟨_, t', u⟩⟩ => (p, q, t', u)
  projWit := fun (_ : Unit) => (() : Unit)
  liftWit := fun (_ : Unit × Unit) => (() : Unit)

def testLensInv : WitnessLensInv Unit Unit Unit Unit where
  projWit := fun _ => ()
  liftWit := fun _ => ()

def testLensComplete : testLens.IsComplete
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨⟨p, q, _⟩, ()⟩ ⟨⟨f, _⟩, ()⟩ => p * q = f) where
  proj_complete := fun ⟨p, q, t⟩ () hRelIn => by
    simp [outerRelIn_Test] at hRelIn
    simp [innerRelIn_Test, testLens, hRelIn]
  lift_complete := fun ⟨p, q, t⟩ _ ⟨f, t', r⟩ _ hRelIn hRelOut' hCompat => by
    simp [outerRelIn_Test] at hRelIn
    simp [innerRelOut_Test] at hRelOut'
    simp at hCompat
    simp [outerRelOut_Test, testLens, hRelIn, ← hRelOut', hCompat]

def testLensKnowledgeSound : testLens.IsKnowledgeSound
      outerRelIn_Test innerRelIn_Test outerRelOut_Test innerRelOut_Test
      (fun ⟨⟨p, q, _⟩, ()⟩ ⟨⟨f, _⟩, ()⟩ => p * q = f) testLensInv where
  proj_knowledge_sound := fun ⟨p, q, t⟩ () hRelIn => by
    simp [outerRelIn_Test] at hRelIn
    simp [innerRelIn_Test, testLens, hRelIn]
  lift_knowledge_sound := fun ⟨p, q, t⟩ _ ⟨f, t', r⟩ _ hRelIn hRelOut' hCompat => by
    simp [outerRelIn_Test] at hRelIn
    sorry
end

end Test
