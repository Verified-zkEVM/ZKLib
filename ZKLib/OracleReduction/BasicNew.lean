import ZKLib.OracleReduction.ToOracle
import ZKLib.OracleReduction.Prelude


/-!

# Interactive Oracle Reductions

We give a **new** modeling of IORs based on continuations / session types.

-/

universe u v w

inductive OracleCompAlt {ι : Type u} (spec : OracleSpec.{u,v} ι) : Type w → Type (max u v w) where
  | pure {α} (x : α) : OracleCompAlt spec α
  | queryBind {α} (i : ι) (t : spec.domain i) (oa : spec.range i → OracleCompAlt spec α) :
      OracleCompAlt spec α
  | failure {α} : OracleCompAlt spec α

#print FreeMonad

#print OracleSpec

#print OracleSpec.OracleQuery

def test (f : Type u → Type v) := f

#check test

inductive ProverMessageType where
  | Plain (α : Type u)
  | Oracle (α : Type u) (O : ToOracle α)

inductive OracleProtocolMessageType where
  | P_to_V (m : ProverMessageType)
  | V_to_P (m : Type u)

@[reducible]
def ProtocolSpec := List (Direction × Type u)

def OracleProtocolSpec := List OracleProtocolMessageType

def ProverInteractionType (pSpec : ProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun (dir, α) acc => match dir with
    | .P_to_V => m (α × acc)
    | .V_to_P => m (α → acc))

def VerifierInteractionType (pSpec : ProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun (dir, α) acc => match dir with
    | .P_to_V => m (α → acc)
    | .V_to_P => m (α × acc))

/-- Takes in the input statement and the whole transcript, returns the next message and the rest of
  the transcript. -/
def PublicCoinVerifierType (pSpec : ProtocolSpec) (m : Type u → Type u) (Input : Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Input) (fun (_, α) acc => α × acc) → m Output

def PublicCoinOracleVerifierType (pSpec : OracleProtocolSpec) (m : Type u → Type u)
    (Input : Type u) (Output : Type u) :=
  pSpec.foldr (init := Input) (fun Message acc => match Message with
    | .P_to_V (.Plain α) => m (α × acc)
    | .P_to_V (.Oracle α _) => m (α × acc)
    | .V_to_P α => m (α → acc)) → m Output

def OracleProverInteractionType (pSpec : OracleProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun Message acc => match Message with
    | .P_to_V (.Plain α) => m (α × acc)
    | .P_to_V (.Oracle α _) => m (α × acc)
    | .V_to_P α => m (α → acc))

/-- TODO: add in the right `OracleCompAlt` wrapper -/
def OracleVerifierInteractionType (pSpec : OracleProtocolSpec) (m : Type u → Type u)
    (Output : Type u) :=
  pSpec.foldr (init := Output) (fun Message acc => match Message with
    | .P_to_V (.Plain α) => m (α → acc)
    | .P_to_V (.Oracle α _) => m (α → acc)
    | .V_to_P α => m (α × acc))

/-- The type of the prover, allowing for an arbitrary initial witness type (for adversaries). -/
def Prover (pSpec : ProtocolSpec) (m : Type u → Type u)
    (StmtIn StmtOut WitOut : Type u) : Type _ :=
  (WitIn : Type u) × (StmtIn × WitIn → ProverInteractionType pSpec m (StmtOut × WitOut))

/-- The type of the honest prover. -/
def HonestProver (pSpec : ProtocolSpec) (m : Type u → Type u)
    (StmtIn StmtOut WitIn WitOut : Type u) : Type _ :=
  StmtIn × WitIn → ProverInteractionType pSpec m (StmtOut × WitOut)

/-- A malicious prover may choose to use a different witness type than the honest prover. -/
def MaliciousProver (pSpec : ProtocolSpec) (m : Type u → Type u)
    (StmtIn StmtOut WitOut : Type u) : Type _ :=
  (WitIn : Type u) × HonestProver pSpec m StmtIn StmtOut WitIn WitOut

/-- The type of the verifier. -/
def Verifier (pSpec : ProtocolSpec) (m : Type u → Type u)
    (StmtIn StmtOut : Type u) : Type _ :=
  StmtIn → VerifierInteractionType pSpec m StmtOut

@[reducible]
def ProtocolSpec.append (pSpec pSpec' : ProtocolSpec) : ProtocolSpec :=
  List.append pSpec pSpec'

section Lemmas

variable {m : Type u → Type u}

theorem ProverInteractionType.cons_eq (firstRound : Direction × Type u)  (pSpec : ProtocolSpec)
    {Output : Type u} :
    ProverInteractionType (firstRound :: pSpec) m Output = match firstRound.1 with
    | .P_to_V => m (firstRound.2 × ProverInteractionType pSpec m Output)
    | .V_to_P => m (firstRound.2 → ProverInteractionType pSpec m Output) := rfl

section ExampleCompose

variable {Input Msg1 Chal1 Middle Msg2 Chal2 Output : Type} {m : Type → Type} [Monad m]

-- def p1 : Input → m (Msg1 × m Middle) := sorry
-- def p1' : Input → m (Chal1 → m Middle) := sorry
-- def p2 : Middle → m (Msg2 × m Output) := sorry
-- def p2' : Middle → m (Chal2 → m Output) := sorry

def p1_compose_p2
    (p1 : Input → m (Msg1 × m Middle))
    (p2 : Middle → m (Msg2 × m Output)) :
    Input → m (Msg1 × m (Msg2 × m Output)) := fun input => do
  let ⟨msg1, rest1⟩ ← p1 input
  return (msg1, do
    let mid ← rest1
    let (msg2, rest2) ← p2 mid
    return (msg2, do
      let output ← rest2
      return output))

def p1'_compose_p2
    (p1' : Input → m (Chal1 → m Middle))
    (p2 : Middle → m (Msg2 × m Output)) :
    Input → m (Chal1 → m (Msg2 × m Output)) := fun input => do
  let rest1 ← p1' input
  return (fun chal => do
    let mid ← rest1 chal
    p2 mid)
    -- return (msg2, do
    --   let output ← rest2
    --   return output))

def p1_compose_p2'
    (p1 : Input → m (Msg1 × m Middle))
    (p2' : Middle → m (Chal2 → m Output)) :
    Input → m (Msg1 × m (Chal2 → m Output)) := fun input => do
  let (msg1, rest1) ← p1 input
  return (msg1, do
    let mid ← rest1
    p2' mid)
    -- return (fun chal => do
    --   let output ← rest2 chal
    --   return output))

def p1'_compose_p2'
    (p1' : Input → m (Chal1 → m Middle))
    (p2' : Middle → m (Chal2 → m Output)) :
    Input → m (Chal1 → m (Chal2 → m Output)) := fun input => do
  let rest1 ← p1' input
  return (fun chal1 => do
    let mid ← rest1 chal1
    let rest2 ← p2' mid
    return (fun chal2 => do
      let output ← rest2 chal2
      return output))

end ExampleCompose

end Lemmas

section Composition

def HonestProver.cons (firstRound : Direction × Type u) (pSpec : ProtocolSpec) (m : Type u → Type u)
    [Monad m] (StmtIn StmtMid StmtOut WitIn WitMid WitOut : Type u)
    (proverFirst : HonestProver [firstRound] m StmtIn StmtMid WitIn WitMid)
    (proverRest : HonestProver pSpec m StmtMid StmtOut WitMid WitOut) :
    HonestProver (firstRound :: pSpec) m StmtIn StmtOut WitIn WitOut :=
  match h : firstRound.1 with
  | .P_to_V => fun input => by
    unfold HonestProver at proverFirst
    dsimp [ProverInteractionType] at proverFirst ⊢
    rw [h] at proverFirst ⊢
    exact (do
      let (msg1, rest) ← proverFirst input
      return (msg1, proverRest rest))
  | .V_to_P => fun input => by
    unfold HonestProver at proverFirst
    dsimp [ProverInteractionType] at proverFirst ⊢
    rewrite [h] at proverFirst ⊢
    exact (do
      let rest ← proverFirst input
      return (fun chal => proverRest (rest chal)))

  --   by
  -- dsimp [HonestProver] at proverFirst proverRest ⊢
  -- dsimp [ProverInteractionType] at proverFirst ⊢
  -- exact (match h : firstRound.1 with
  -- | .P_to_V => fun input => by
  --   rw [h] at proverFirst
  --   exact (do
  --     let (msg1, rest) ← proverFirst input
  --     return (msg1, proverRest rest))
  -- | .V_to_P => fun input => by
  --   rw [h] at proverFirst
  --   exact (do
  --     let rest ← proverFirst input
  --     return (fun chal => proverRest (rest chal))))

#print HonestProver.cons

def HonestProver.concat (pSpec : ProtocolSpec) (lastRound : Direction × Type u) (m : Type u → Type u) [Monad m]
    (StmtIn StmtMid StmtOut WitIn WitMid WitOut : Type u)
    (proverFirst : HonestProver pSpec m StmtIn StmtMid WitIn WitMid)
    (proverLast : HonestProver [lastRound] m StmtMid StmtOut WitMid WitOut) :
    HonestProver (pSpec.concat lastRound) m StmtIn StmtOut WitIn WitOut := by
  sorry

def HonestProver.append (pSpec pSpec' : ProtocolSpec) (m : Type u → Type u) [Monad m]
    (StmtIn StmtMid StmtOut WitIn WitMid WitOut : Type u)
    (prover1 : HonestProver pSpec m StmtIn StmtMid WitIn WitMid)
    (prover2 : HonestProver pSpec' m StmtMid StmtOut WitMid WitOut) :
    HonestProver (pSpec.append pSpec') m StmtIn StmtOut WitIn WitOut := by
  induction pSpec with
  | nil => exact prover2 ∘ prover1
  | cons firstRound pSpec ih =>
    dsimp [ProtocolSpec.append]
    sorry
    -- dsimp [HonestProver, ProverInteractionType] at prover1
    -- exact HonestProver.cons firstRound pSpec m StmtIn StmtMid StmtOut WitIn WitMid WitOut prover1 ih
  -- | [] => prover' ∘ prover
  -- | (firstRound :: pSpec) ih => by
  --     dsimp [ProtocolSpec.append]
  --     dsimp [HonestProver] at prover prover' ⊢
  --     dsimp [ProverInteractionType.cons_eq] at prover ⊢
  --     intro input

      -- sorry
      -- dsimp [ProverInteractionType] at prover


    -- (prover.1, fun input => do
    --   let (output, rest) ← prover.2 input
    --   let (output', rest') ← prover'.2 output rest
    --   return (output', rest'))

end Composition

section Example

def examplePSpec : ProtocolSpec := [(.P_to_V, Nat), (.V_to_P, Int)]

example : ProverInteractionType examplePSpec Id Rat = (Nat × (Int → Rat)) := by
  rfl

universe u₁ u₂ u₃ u₄ u₅

variable (m₁ : Type → Type 1) [Monad m₁]
variable (m₂ : Type 1 → Type 2) [Monad m₂]
variable (m₃ : Type 2 → Type 3) [Monad m₃]
variable (m₄ : Type 3 → Type 4) [Monad m₄]

#check StateM

#check OracleComp

variable (m : Type → Type) [Monad m] (StmtIn Message1 Challenge Message2 StmtOut : Type)

def ProverSigmaProtocol := StmtIn → m (Message1 × m (Challenge → m (Message2 × m (StmtOut))))

def ProverSigmaProtocol' :=
  StmtIn → m₄ (Message1 × m₃ (Challenge → m₂ (Message2 × m₁ (StmtOut))))

variable {PrvState : Fin 4 → Type}

-- Does this match the old type?

-- Old type would have:
-- input: Statement → PrvState 0
-- sendMessage1: PrvState 0 → m (Message1 × PrvState 1)
-- receiveChallenge: PrvState 1 → Challenge → m (Message2 × PrvState 2)
-- sendMessage2: PrvState 2 → m (Message2 × PrvState 3)
-- output: PrvState 3 → NewStatement

-- You would compose these together as follows
-- do
-- let st0 := input stmt
-- let (msg1, st1) ← sendMessage1 st0
-- (the other party generates a challenge)
-- let st2 := receiveChallenge st1 challenge
-- let (msg2, st3) ← sendMessage2 st2
-- let newStmt := output st3
-- return newStmt

-- de-sugaring do-notation, this would be:
-- (input is some `challenge`)
-- (pure input stmt) >>= fun st0 =>
-- sendMessage1 st0 >>= fun (msg1, st1) =>
-- (pure receiveChallenge st1 challenge) >>= fun st2 =>
-- sendMessage2 st2 >>= fun (msg2, st3) =>
-- (pure output st3)

def exampleProverSigmaProtocol
    (input : StmtIn → PrvState 0)
    (sendMessage1 : PrvState 0 → m (Message1 × PrvState 1))
    (receiveChallenge : PrvState 1 → Challenge → PrvState 2)
    (sendMessage2 : PrvState 2 → m (Message2 × PrvState 3))
    (output : PrvState 3 → StmtOut) :
    ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut :=
  fun stmt => (do
    let st0 := input stmt
    let (msg1, st1) ← sendMessage1 st0
    return (msg1, (do
      return (fun challenge => (do
        let st2 := receiveChallenge st1 challenge
        let (msg2, st3) ← sendMessage2 st2
        return (msg2, (do return output st3)))))))

def ProverSigmaProtocol.run
    (stmtIn : StmtIn) (challenge : Challenge)
    (prover : ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut) :
    m (Message1 × Message2 × StmtOut) := do
  let (msg1, rest) ← prover stmtIn
  let (msg2, stmtOut) ← (← rest) challenge
  return (msg1, msg2, ← stmtOut)

-- What about composition?
variable (StmtMid : Type)

def ProverFirstRound := StmtIn → m (Message1 × m (StmtMid))

def ProverRest := StmtMid → m (Challenge → m (Message2 × m (StmtOut)))

def composeProvers
    (proverFirst : ProverFirstRound m StmtIn Message1 StmtMid)
    (proverRest : ProverRest m Challenge Message2 StmtOut StmtMid) :
    ProverSigmaProtocol m StmtIn Message1 Challenge Message2 StmtOut :=
  fun stmt => do
    let (msg1, rest) ← proverFirst stmt
    let stmtMid ← rest
    let cont ← proverRest stmtMid
    return (msg1, (do return cont))

end Example


-- Potential hybrid approach / combination of the two

-- Have a number of functions where you decrement down the index of the continuation

namespace Hybrid

@[reducible]
def ProtocolSpec (n : ℕ) := Fin n → Direction × Type

def ProverCont (n : ℕ) (pSpec : ProtocolSpec n) (m : Type → Type) (Output : Type) : Type :=
  match n with
  | 0 => m Output
  | n + 1 => match (pSpec 0).1 with
    | .P_to_V => (pSpec 0).2 × ProverCont n (Fin.tail pSpec) m Output
    | .V_to_P => (pSpec 0).2 → ProverCont n (Fin.tail pSpec) m Output

example : ProverCont 2 ![(.P_to_V, Nat), (.V_to_P, Int)] Id Nat = (Nat × (Int → Nat)) := by
  rfl
  -- simp [ProverCont, Fin.tail]; rfl

end Hybrid
