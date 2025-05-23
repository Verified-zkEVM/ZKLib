import ArkLib.OracleReduction.Security.Basic

/-!
  ## Semantics of Virtual (Oracle) Reductions

  Sequential composition is usually not enough to represent oracle reductions in a modular way. We
  also need to formalize **virtual** oracle reductions, which lift reductions from one (virtual)
  context into the another (real) context.

  This is what is meant when we informally say "apply so-and-so protocol to this quantity (derived
  from the input statement & witness)".

-/


open OracleSpec OracleComp ProtocolSpec

section find_home

end find_home

section Transport

open scoped NNReal

-- sub-reduction: (StmtIn, WitIn) →[..] (StmtOut, WitOut)

-- current reduction : (StmtIn', WinIn')

-- there's a mapping : (StmtIn', WinIn') → (StmtIn, WitIn), and an inverse mapping : WitIn → WitIn'
-- (for extraction)

-- what should be (StmtOut' = StmtIn × transcript, WitOut')?

structure TransportStatement (StmtIn StmtOut StmtIn' StmtOut' : Type) where
  fStmtIn : StmtIn → StmtIn'
  fStmtOut : StmtIn × StmtOut' → StmtOut

structure TransportWitness (WitIn WitOut WitIn' WitOut' : Type) where
  fWitIn : WitIn → WitIn'
  fWitOut : WitIn × WitOut' → WitOut

structure TransportData (StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut' : Type)
    extends TransportStatement StmtIn StmtOut StmtIn' StmtOut',
      TransportWitness WitIn WitOut WitIn' WitOut'

structure TransportStatementInv (StmtIn StmtOut StmtIn' StmtOut' : Type) where
  fStmtInInv : StmtOut × StmtIn' → StmtIn
  fStmtOutInv : StmtOut → StmtOut'

structure TransportWitnessInv (WitIn WitOut WitIn' WitOut' : Type) where
  fWitInInv : WitOut × WitIn' → WitIn
  fWitOutInv : WitOut → WitOut'

structure TransportDataInv (StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut' : Type)
    extends TransportStatementInv StmtIn StmtOut StmtIn' StmtOut',
      TransportWitnessInv WitIn WitOut WitIn' WitOut'

/-- Conditions for the transformation to preserve completeness

NOTE: this is not the correct condition for now (see example) -/
structure TransportDataComplete (StmtIn WitIn StmtOut WitOut : Type)
    (StmtIn' WitIn' StmtOut' WitOut' : Type)
    (relIn : StmtIn → WitIn → Prop) (relIn' : StmtIn' → WitIn' → Prop)
    (relOut : StmtOut → WitOut → Prop) (relOut' : StmtOut' → WitOut' → Prop)
    extends TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut' where

  relIn_implies : ∀ stmtIn witIn, relIn stmtIn witIn → relIn' (fStmtIn stmtIn) (fWitIn witIn)

  relOut_implied_by : ∀ stmtIn witIn stmtOut' witOut',
    relIn stmtIn witIn → relOut' stmtOut' witOut'
      → relOut (fStmtOut (stmtIn, stmtOut')) (fWitOut (witIn, witOut'))

structure TransportDataSound (StmtIn StmtOut StmtIn' StmtOut' : Type)
    (langIn : Set StmtIn) (langOut : Set StmtOut) (langIn' : Set StmtIn') (langOut' : Set StmtOut')
    extends TransportStatement StmtIn StmtOut StmtIn' StmtOut',
      TransportStatementInv StmtIn StmtOut StmtIn' StmtOut' where
  -- langIn_implies : ∀ stmtIn, stmtIn ∈ langIn → fStmtIn stmtIn ∈ langIn'
  -- langOut_implies : ∀ stmtOut, stmtOut ∈ langOut → fStmtOut stmtOut ∈ langOut'

structure TransportDataKnowledgeSound (StmtIn WitIn StmtOut WitOut : Type)
    (StmtIn' WitIn' StmtOut' WitOut' : Type)
    (relIn : StmtIn → WitIn → Prop) (relIn' : StmtIn' → WitIn' → Prop)
    (relOut : StmtOut → WitOut → Prop) (relOut' : StmtOut' → WitOut' → Prop)
    extends TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut',
      TransportDataInv StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut' where

-- Conditions for (round-by-round) (knowledge) soundness?

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {StmtIn' WitIn' StmtOut' WitOut' : Type}
  [∀ i, VCVCompatible (pSpec.Challenge i)] [oSpec.FiniteRange]

/-- How does the prover change? Only in input & output, and keep around the input statement &
  witness -/
def Prover.transport
    (data : TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut')
    (P : Prover pSpec oSpec StmtIn' WitIn' StmtOut' WitOut') :
      Prover pSpec oSpec StmtIn WitIn StmtOut WitOut where
  PrvState := fun i => P.PrvState i × StmtIn × WitIn
  input := fun stmtIn witIn => ⟨P.input (data.fStmtIn stmtIn) (data.fWitIn witIn), stmtIn, witIn⟩
  sendMessage := fun i ⟨prvState, stmtIn, witIn⟩ => do
    let ⟨msg, prvState'⟩ ← P.sendMessage i prvState
    return ⟨msg, ⟨prvState', stmtIn, witIn⟩⟩
  receiveChallenge := fun i ⟨prvState, stmtIn, witIn⟩ chal =>
    ⟨P.receiveChallenge i prvState chal, stmtIn, witIn⟩
  output := fun ⟨prvState, stmtIn, witIn⟩ =>
    let ⟨stmtOut', witOut'⟩ := P.output prvState
    ⟨data.fStmtOut (stmtIn, stmtOut'), data.fWitOut (witIn, witOut')⟩

def Verifier.transport
    (data : TransportStatement StmtIn StmtOut StmtIn' StmtOut')
    (V : Verifier pSpec oSpec StmtIn' StmtOut') :
      Verifier pSpec oSpec StmtIn StmtOut where
  verify := fun stmtIn transcript => do
    let stmtIn' := data.fStmtIn stmtIn
    let stmtOut' ← V.verify stmtIn' transcript
    return data.fStmtOut (stmtIn, stmtOut')

def Reduction.transport
    (data : TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut')
    (R : Reduction pSpec oSpec StmtIn' WitIn' StmtOut' WitOut') :
      Reduction pSpec oSpec StmtIn WitIn StmtOut WitOut where
  prover := R.prover.transport data
  verifier := R.verifier.transport data.toTransportStatement

open Reduction in
def StraightlineExtractor.transport
    (data : TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut')
    (dataInv : TransportDataInv StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut')
    (E : @StraightlineExtractor _ pSpec _ oSpec StmtIn' WitIn' StmtOut' WitOut') :
      @StraightlineExtractor _ pSpec _ oSpec StmtIn WitIn StmtOut WitOut :=
  fun stmtIn stmtOut witOut fullTranscript queryLog =>
    let stmtIn' := data.fStmtIn stmtIn
    let stmtOut' := dataInv.fStmtOutInv stmtOut
    let witOut' := dataInv.fWitOutInv witOut
    let witIn' := E stmtIn' stmtOut' witOut' fullTranscript queryLog
    dataInv.fWitInInv (witOut, witIn')

theorem Prover.run_transport
    {data : TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut'}
    {stmtIn : StmtIn} {witIn : WitIn}
    (P : Prover pSpec oSpec StmtIn' WitIn' StmtOut' WitOut') :
      (P.transport data).run stmtIn witIn = do
        let ⟨stmtOut, witOut, fullTranscript⟩ ←
          P.run (data.fStmtIn stmtIn) (data.fWitIn witIn)
        return ⟨data.fStmtOut (stmtIn, stmtOut), data.fWitOut (witIn, witOut),
          fullTranscript⟩ := by
  unfold Prover.run Prover.runToRound
  simp [Prover.transport]
  sorry

theorem Reduction.run_transport
    {data : TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut'}
    {stmtIn : StmtIn} {witIn : WitIn}
    (R : Reduction pSpec oSpec StmtIn' WitIn' StmtOut' WitOut') :
      (R.transport data).run stmtIn witIn = do
        let ⟨⟨prvStmtOut, witOut⟩, verStmtOut, fullTranscript⟩ ←
          R.run (data.fStmtIn stmtIn) (data.fWitIn witIn)
        return ⟨⟨data.fStmtOut (stmtIn, prvStmtOut), data.fWitOut (witIn, witOut)⟩,
          data.fStmtOut (stmtIn, verStmtOut), fullTranscript⟩ := by
  unfold Reduction.run
  simp [Reduction.transport, Prover.run_transport, Verifier.transport]
  sorry

theorem Reduction.runWithLog_transport
    {data : TransportData StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut'}
    {stmtIn : StmtIn} {witIn : WitIn}
    (R : Reduction pSpec oSpec StmtIn' WitIn' StmtOut' WitOut') :
      (R.transport data).runWithLog stmtIn witIn = do
        let ⟨⟨prvStmtOut, witOut⟩, verStmtOut, fullTranscript, queryLog⟩ ←
          R.runWithLog (data.fStmtIn stmtIn) (data.fWitIn witIn)
        return ⟨⟨data.fStmtOut (stmtIn, prvStmtOut), data.fWitOut (witIn, witOut)⟩,
          data.fStmtOut (stmtIn, verStmtOut), fullTranscript, queryLog⟩ := by
  unfold Reduction.runWithLog
  simp [Reduction.transport, Prover.run_transport, Verifier.transport]
  sorry

/--
  Informally, if `(stmtIn, witIn) ∈ relIn`, we want `(stmtIn', witIn') ∈ relIn'`.
  Using the completeness guarantee, we get that `(stmtOut', witOut') ∈ relOut'`.
  From these, we need to deduce that `(stmtOut, witOut) ∈ relOut`.
-/
theorem Reduction.transport_completeness
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop}
    {relIn' : StmtIn' → WitIn' → Prop} {relOut' : StmtOut' → WitOut' → Prop}
    {completenessError : ℝ≥0}
    (data : TransportDataComplete StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut'
      relIn relIn' relOut relOut')
    (R : Reduction pSpec oSpec StmtIn' WitIn' StmtOut' WitOut')
    (h : R.completeness relIn' relOut' completenessError) :
      (R.transport data.toTransportData).completeness relIn relOut completenessError := by
  unfold completeness at h ⊢
  intro stmtIn witIn hRelIn
  have hR := h (data.fStmtIn stmtIn) (data.fWitIn witIn) (data.relIn_implies _ _ hRelIn)
  rw [Reduction.run_transport]
  refine le_trans hR ?_
  simp
  refine probEvent_mono ?_
  intro _ _ hRelOut'
  sorry
  -- exact data.relOut_implied_by _ _ _ _ hRelIn hRelOut'

/-- -/
theorem Reduction.transport_soundness
    {langIn : Set StmtIn} {langOut : Set StmtOut} {langIn' : Set StmtIn'} {langOut' : Set StmtOut'}
    {soundnessError : ℝ≥0}
    (data : TransportDataSound StmtIn StmtOut StmtIn' StmtOut' langIn langOut langIn' langOut')
    (V : Verifier pSpec oSpec StmtIn' StmtOut')
    (h : Reduction.soundness langIn' langOut' V soundnessError) :
      Reduction.soundness langIn langOut
        (V.transport data.toTransportStatement) soundnessError := by
  unfold soundness at h ⊢
  intro stmtIn hStmtIn WitIn WitOut witIn prover
  sorry

theorem Reduction.transport_knowledgeSoundness
    {relIn : StmtIn → WitIn → Prop} {relOut : StmtOut → WitOut → Prop}
    {relIn' : StmtIn' → WitIn' → Prop} {relOut' : StmtOut' → WitOut' → Prop}
    {soundnessError : ℝ≥0}
    (data : TransportDataKnowledgeSound StmtIn WitIn StmtOut WitOut StmtIn' WitIn' StmtOut' WitOut'
      relIn relIn' relOut relOut')
    (V : Verifier pSpec oSpec StmtIn' StmtOut')
    (h : Reduction.knowledgeSoundness relIn' relOut' V soundnessError) :
      Reduction.knowledgeSoundness relIn relOut
        (V.transport data.toTransportStatement) soundnessError := by
  unfold knowledgeSoundness at h ⊢
  obtain ⟨E, h'⟩ := h
  stop
  refine ⟨E.transport data, ?_⟩
  intro stmtIn witIn hRelIn
  have hR := h (data.fStmtIn stmtIn) (data.fWitIn witIn) (data.relIn_implies _ _ hRelIn)
  rw [Reduction.run_transport]
  sorry

end Transport

section Test

open Polynomial

-- Testing out sum-check-like relations

noncomputable section

def StmtIn := ℤ[X] × ℤ[X] × ℤ

def StmtIn' := ℤ[X] × ℤ

def relIn : StmtIn → Unit → Prop := fun ⟨p, q, t⟩ _ => ∑ x ∈ {0, 1}, (p * q).eval x = t

def relIn' : StmtIn' → Unit → Prop := fun ⟨f, t⟩ _ => ∑ x ∈ {0, 1}, f.eval x = t

def StmtOut := ℤ[X] × ℤ[X] × ℤ × ℤ

def StmtOut' := ℤ[X] × ℤ × ℤ

def relOut : StmtOut → Unit → Prop := fun ⟨p, q, t, r⟩ _ => (p * q).eval r = t

def relOut' : StmtOut' → Unit → Prop := fun ⟨f, t, r⟩ _ => f.eval r = t

def data : TransportData StmtIn Unit StmtOut Unit StmtIn' Unit StmtOut' Unit where
  fStmtIn := fun ⟨p, q, t⟩ => ⟨p * q, t⟩
  fStmtOut := fun ⟨⟨p, q, _⟩, ⟨_, t', u⟩⟩ => (p, q, t', u)
  fWitIn := fun _ => ()
  fWitOut := fun _ => ()

def dataComplete : TransportDataComplete StmtIn Unit StmtOut Unit StmtIn' Unit StmtOut' Unit
    relIn relIn' relOut relOut' where
  toTransportData := data
  relIn_implies := fun ⟨p, q, t⟩ () hRelIn => by
    simp [relIn] at hRelIn
    simp [relIn', data, hRelIn]
  relOut_implied_by := fun ⟨p, q, t⟩ () ⟨f, t', r⟩ () hRelIn hRelOut' => by
    simp [relIn] at hRelIn
    simp [relOut'] at hRelOut'
    simp [relOut, data, hRelIn, hRelOut']
    sorry

end

end Test
