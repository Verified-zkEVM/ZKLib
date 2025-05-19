/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Math.Fin
import Batteries.Data.Fin.Fold
import ArkLib.OracleReduction.Security.Basic

/-!
  # Sequential Composition of (Oracle) Reductions

  We define the composition of two or more interactive (oracle) reductions, where the output
  statement & witness types for one reduction is the same as the input statement & witness types for
  the next.

  This is defined in two steps:
  1. First, we define the concatenation of two reductions, one from R1 => R2 and the other from R2
     => R3.
  2. Then, we define the general composition of `m + 1` reductions, indexed by `i : Fin (m + 1)`, by
     iterating the concatenation of two reductions.

  We also prove that the composition of reductions preserve all completeness & soundness properties
  of the reductions being composed.
-/

section find_home

theorem cast_eq_cast_iff {α β γ : Sort _} {h : α = γ} {h' : β = γ} {a : α} {b : β} :
    cast h a = cast h' b ↔ a = cast (h'.trans h.symm) b := by subst h'; subst h; simp

theorem cast_symm {α β : Sort _} {h : α = β} {a : α} {b : β} :
    cast h a = b ↔ a = cast h.symm b := by
  subst h; simp

theorem congrArg₃ {α β γ δ : Sort*} {f : α → β → γ → δ} {a a' : α} {b b' : β} {c c' : γ}
    (h : a = a') (h' : b = b') (h'' : c = c') : f a b c = f a' b' c' := by
  subst h; subst h'; subst h''; rfl

theorem congrArg₄ {α β γ δ ε : Sort*} {f : α → β → γ → δ → ε} {a a' : α} {b b' : β} {c c' : γ}
    {d d' : δ} (h : a = a') (h' : b = b') (h'' : c = c') (h''' : d = d') :
      f a b c d = f a' b' c' d' := by
  subst h; subst h'; subst h''; subst h'''; rfl

namespace Fin

variable {m n : ℕ} {α : Sort*}

theorem append_left_injective (b : Fin n → α) : Function.Injective (@Fin.append m n α · b) := by
  intro a a' h
  simp only at h
  ext i
  have : append a b (castAdd n i) = append a' b (castAdd n i) := by rw [h]
  simp only [append_left] at this
  exact this

theorem append_right_injective (a : Fin m → α) : Function.Injective (@Fin.append m n α a) := by
  intro b b' h
  ext i
  have : append a b (natAdd m i) = append a b' (natAdd m i) := by rw [h]
  simp only [append_right] at this
  exact this

end Fin

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

open OracleComp

@[simp]
lemma evalDist_cast (h : α = β) [spec.FiniteRange] :
    evalDist (cast (congrArg (OracleComp spec) h) oa) =
      cast (congrArg (PMF ∘ Option) h) (evalDist oa) := by
  induction h; rfl

universe u v

theorem PMF.heq_iff {α β : Type u} {pa : PMF α} {pb : PMF β} (h : α = β) :
    HEq pa pb ↔ ∀ x, pa x = pb (cast h x) := by
  subst h; simp; constructor <;> intro h'
  · intro x; rw [h']
  · ext x; rw [h' x]

theorem Option.cast_eq_some_iff {α β : Type u} {x : Option α} {b : β} (h : α = β) :
    cast (congrArg Option h) x = some b ↔ x = some (cast h.symm b) := by
  subst h; simp only [cast_eq]

theorem PMF.uniformOfFintype_cast (α β : Type _) [ha : Fintype α] [Nonempty α]
    [hb : Fintype β] [Nonempty β] (h : α = β) :
      cast (congrArg PMF h) (PMF.uniformOfFintype α) = @PMF.uniformOfFintype β _ _ := by
  subst h
  ext x
  simp only [cast_eq, uniformOfFintype_apply, inv_inj, Nat.cast_inj]
  exact @Fintype.card_congr α α ha hb (Equiv.refl α)

theorem tsum_cast {α β : Type u} {f : α → ENNReal} {g : β → ENNReal}
    (h : α = β) (h' : ∀ a, f a = g (cast h a)) :
      (∑' (a : α), f a) = (∑' (b : β), g b) := by
  subst h; simp [h']

end find_home

namespace ProtocolSpec

/-! ### Restriction of Protocol Specifications & Transcripts -/

section Restrict

variable {n : ℕ}

abbrev take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) := Fin.take m h pSpec

abbrev rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) := Fin.rtake m h pSpec

abbrev FullTranscript.take {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.take m h) :=
  Fin.take m h transcript

abbrev FullTranscript.rtake {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rtake m h) :=
  Fin.rtake m h transcript

end Restrict

section Cast

def cast {n n' : ℕ} (h : n = n') (pSpec : ProtocolSpec n) : ProtocolSpec n' :=
  pSpec ∘ (Fin.cast h.symm)

@[simp]
theorem cast_refl {n : ℕ} {h : n = n} : cast h = id := rfl

@[simp]
theorem cast_eq_self {n : ℕ} {pSpec : ProtocolSpec n} : cast (refl n) pSpec = pSpec := by
  simp only [cast, Fin.cast_refl, CompTriple.comp_eq]

@[simp]
theorem cast_trans {n n' n'' : ℕ} {pSpec : ProtocolSpec n} (h : n = n') (h' : n' = n'') :
    cast h' (cast h pSpec) = cast (h.trans h') pSpec := by
  subst h; subst h'; simp only [cast, Fin.cast_refl, CompTriple.comp_eq]

theorem cast_eq_cast_iff {n m k : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m}
    (h : n = k) (h' : m = k) :
      cast h pSpec = cast h' pSpec' ↔ pSpec = cast (h'.trans h.symm) pSpec' := by
  subst h; subst h'; simp only [cast, Fin.cast_refl, CompTriple.comp_eq]

theorem cast_eq_root_cast {n m : ℕ} {pSpec : ProtocolSpec n} (h : n = m) :
    cast h pSpec = _root_.cast (by simp [h]) pSpec := by subst h; simp only [cast_eq_self, cast_eq]

end Cast

/-! ### Composition of Two Protocol Specifications -/

variable {m n : ℕ}

/-- Adding a round with direction `dir` and type `Message` to the beginning of a `ProtocolSpec` -/
abbrev cons (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) := Fin.cons ⟨dir, Message⟩ pSpec

/-- Adding a round with direction `dir` and type `Message` to the end of a `ProtocolSpec` -/
abbrev snoc (pSpec : ProtocolSpec n) (dir : Direction) (Message : Type) :
    ProtocolSpec (n + 1) := Fin.snoc pSpec ⟨dir, Message⟩

/-- Appending two `ProtocolSpec`s -/
abbrev append (pSpec : ProtocolSpec m) (pSpec' : ProtocolSpec n) : ProtocolSpec (m + n) :=
  Fin.append pSpec pSpec'

@[inline, reducible]
def mkSingle (dir : Direction) (Message : Type) : ProtocolSpec 1 := fun _ => ⟨dir, Message⟩

infixl : 65 " ++ₚ " => ProtocolSpec.append

@[simp]
theorem append_cast_left {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} (n' : ℕ)
    (h : n = n') : (pSpec.cast h) ++ₚ pSpec' = (pSpec ++ₚ pSpec').cast (by omega) := by
  simp only [append, cast, Fin.append_cast_left]

/-- Reverse of non-prime version, to facilitate rewrite from the other side -/
theorem append_cast_left' {n m : ℕ} {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m} (n' : ℕ)
    (h : n + m = n' + m) :
      (pSpec ++ₚ pSpec').cast h = (pSpec.cast (Nat.add_right_cancel h)) ++ₚ pSpec' := by
  simp only [append, cast, Fin.append_cast_left]

@[simp]
theorem append_cast_right {n m : ℕ} (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) (m' : ℕ)
    (h : m = m') : pSpec ++ₚ (pSpec'.cast h) = (pSpec ++ₚ pSpec').cast (by omega) := by
  simp only [append, cast, Fin.append_cast_right]

/-- Reverse of non-prime version, to facilitate rewrite from the other side -/
theorem append_cast_right' {n m : ℕ} (pSpec : ProtocolSpec n) (pSpec' : ProtocolSpec m) (m' : ℕ)
    (h : n + m = n + m') :
      (pSpec ++ₚ pSpec').cast h = pSpec ++ₚ (pSpec'.cast (Nat.add_left_cancel h)) := by
  simp only [append, cast, Fin.append_cast_right]

theorem append_left_injective {pSpec : ProtocolSpec n} :
    Function.Injective (@ProtocolSpec.append m n · pSpec) :=
  Fin.append_left_injective pSpec

theorem append_right_injective {pSpec : ProtocolSpec m} :
    Function.Injective (@ProtocolSpec.append m n pSpec) :=
  Fin.append_right_injective pSpec

@[simp]
theorem append_left_cancel_iff {pSpec : ProtocolSpec n} {p1 p2 : ProtocolSpec m} :
    p1 ++ₚ pSpec = p2 ++ₚ pSpec ↔ p1 = p2 :=
  ⟨fun h => append_left_injective h, fun h => by rw [h]⟩

@[simp]
theorem append_right_cancel_iff {pSpec : ProtocolSpec m} {p1 p2 : ProtocolSpec n} :
    pSpec ++ₚ p1 = pSpec ++ₚ p2 ↔ p1 = p2 :=
  ⟨fun h => append_right_injective h, fun h => by rw [h]⟩

@[simp]
theorem snoc_take {pSpec : ProtocolSpec n} (k : ℕ) (h : k < n) :
    (pSpec.take k (by omega) ++ₚ (fun (_ : Fin 1) => pSpec ⟨k, h⟩))
      = pSpec.take (k + 1) (by omega) := by
  simp only [append, take, Fin.append_right_eq_snoc, Fin.take_succ_eq_snoc]

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

@[simp]
theorem take_append_left :
    (pSpec₁ ++ₚ pSpec₂).take m (Nat.le_add_right m n) = pSpec₁ := by
  simp only [take, append]
  have {i : Fin m} : Fin.castLE (by omega) i = Fin.castAdd n i := by
    simp only [Fin.castLE, Fin.castAdd]
  ext i <;>
  simp only [Fin.take_apply, this, Fin.append_left]

namespace FullTranscript

/-- Appending two transcripts for two `ProtocolSpec`s -/
def append (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    FullTranscript (pSpec₁ ++ₚ pSpec₂) :=
  fun i => (Fin.append_comp' Prod.snd i).mp (Fin.addCases' T₁ T₂ i)

infixl : 65 " ++ₜ " => append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def snoc {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : FullTranscript pSpec) (dir : Direction) (msg : NextMessage) :
        FullTranscript (pSpec ++ₚ .mkSingle dir NextMessage) :=
  append T fun _ => msg

theorem take_append_left (T : FullTranscript pSpec₁) (T' : FullTranscript pSpec₂) :
    ((T ++ₜ T').take m (Nat.le_add_right m n)) =
      (@take_append_left _ _ pSpec₁ pSpec₂).symm ▸ T := by
  ext i
  simp [take, append, ProtocolSpec.append]
  simp [Fin.castLE, Fin.addCases', Fin.addCases]
  -- refine heq_of_eq_cast ?_ ?_
  sorry

def fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by
    simpa [ProtocolSpec.append, Fin.append_left] using T (Fin.castAdd n i)

def snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₂ :=
  fun i => by
    simpa [ProtocolSpec.append, Fin.append_right] using T (Fin.natAdd m i)

@[simp]
theorem append_fst (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).fst = T₁ := by
  funext i
  simp [fst, append, eqRec_eq_cast]

@[simp]
theorem append_snd (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    (T₁ ++ₜ T₂).snd = T₂ := by
  funext i
  simp [snd, append, eqRec_eq_cast]

end FullTranscript

def MessageIdx.inl (i : MessageIdx pSpec₁) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [Fin.append_left] using i.2⟩

def MessageIdx.inr (i : MessageIdx pSpec₂) : MessageIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [Fin.append_right] using i.2⟩

@[simps!]
def MessageIdx.sumEquiv :
    MessageIdx pSpec₁ ⊕ MessageIdx pSpec₂ ≃ MessageIdx (pSpec₁ ++ₚ pSpec₂) where
  toFun := Sum.elim (MessageIdx.inl) (MessageIdx.inr)
  invFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  left_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [MessageIdx.inl, MessageIdx.inr, h, isLt]
  right_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [MessageIdx.inl, MessageIdx.inr, hi]
    congr; omega

def ChallengeIdx.inl (i : ChallengeIdx pSpec₁) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.castAdd n i.1, by simpa only [Fin.append_left] using i.2⟩

def ChallengeIdx.inr (i : ChallengeIdx pSpec₂) : ChallengeIdx (pSpec₁ ++ₚ pSpec₂) :=
  ⟨Fin.natAdd m i.1, by simpa only [Fin.append_right] using i.2⟩

@[simps!]
def ChallengeIdx.sumEquiv :
    ChallengeIdx pSpec₁ ⊕ ChallengeIdx pSpec₂ ≃ ChallengeIdx (pSpec₁ ++ₚ pSpec₂) where
  toFun := Sum.elim (ChallengeIdx.inl) (ChallengeIdx.inr)
  invFun := fun ⟨i, h⟩ => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inl ⟨⟨i, hi⟩, h⟩
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, hi] at h
      exact Sum.inr ⟨⟨i - m, by omega⟩, h⟩
  left_inv := fun i => by
    rcases i with ⟨⟨i, isLt⟩, h⟩ | ⟨⟨i, isLt⟩, h⟩ <;>
    simp [ChallengeIdx.inl, ChallengeIdx.inr, h, isLt]
  right_inv := fun ⟨i, h⟩ => by
    by_cases hi : i < m <;>
    simp [ChallengeIdx.inl, ChallengeIdx.inr, hi]
    congr; omega

end ProtocolSpec

open ProtocolSpec

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} {ι : Type} [DecidableEq ι]
    {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}

section Instances

/-- If two protocols have sampleable challenges, then their concatenation also has sampleable
  challenges. -/
instance [h₁ : ∀ i, Sampleable (pSpec₁.Challenge i)] [h₂ : ∀ i, Sampleable (pSpec₂.Challenge i)] :
    ∀ i, Sampleable ((pSpec₁ ++ₚ pSpec₂).Challenge i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  by_cases h' : i < m <;> simp [h'] at h ⊢
  · exact h₁ ⟨⟨i, by omega⟩, h⟩
  · exact h₂ ⟨⟨i - m, by omega⟩, h⟩

/-- If two protocols' messages have oracle representations, then their concatenation's messages also
    have oracle representations. -/
instance [O₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
    [O₂ : ∀ i, OracleInterface (pSpec₂.Message i)] :
    ∀ i, OracleInterface ((pSpec₁ ++ₚ pSpec₂).Message i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.append, ProtocolSpec.getDir, Fin.append, Fin.addCases,
    Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  by_cases h' : i < m <;> simp [h'] at h ⊢
  · exact O₁ ⟨⟨i, by omega⟩, h⟩
  · exact O₂ ⟨⟨i - m, by omega⟩, h⟩

open OracleComp OracleSpec SubSpec

variable [∀ i, Sampleable (pSpec₁.Challenge i)] [∀ i, Sampleable (pSpec₂.Challenge i)]

instance instSubSpecOfProtocolSpecAppendChallenge :
    SubSpec ([pSpec₁.Challenge]ₒ ++ₒ [pSpec₂.Challenge]ₒ) ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => match i with
    | Sum.inl j => by
      simpa [OracleSpec.append, OracleSpec.range, OracleInterface.toOracleSpec, ChallengeIdx.inl,
        instChallengeOracleInterface] using
      query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) j.inl ()
    | Sum.inr j => by
      simpa [OracleSpec.append, OracleSpec.range, OracleInterface.toOracleSpec, ChallengeIdx.inr,
        instChallengeOracleInterface] using
      query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) j.inr ()
  -- evalDist_toFun' := fun i q => by
  --   cases i with
  --   | inl j =>
  --     simp only [eq_mp_eq_cast, id_eq]
  --     have : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.range j.inl =
  --       ([pSpec₁.Challenge]ₒ ++ₒ [pSpec₂.Challenge]ₒ).range (Sum.inl j) := by
  --       simp [OracleSpec.append, ChallengeIdx.inl, instChallengeOracleInterface]
  --     rw [evalDist_cast _ this, evalDist_query, evalDist_query]
  --     simp [OracleSpec.append, ChallengeIdx.inl, instChallengeOracleInterface]
  --     refine cast_eq_iff_heq.mpr ((PMF.heq_iff (by simp [this])).mpr ?_)
  --     intro x
  --     simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fin.append_left]
  --     refine tsum_cast (by simp) (fun a => ?_)
  --     congr <;> try { simp only [Fin.append_left] } <;> symm <;> simp only [cast_heq]
  --   | inr j =>
  --     simp only [eq_mp_eq_cast, id_eq]
  --     have : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.range j.inr =
  --       ([pSpec₁.Challenge]ₒ ++ₒ [pSpec₂.Challenge]ₒ).range (Sum.inr j) := by
  --       simp [OracleSpec.append, ChallengeIdx.inr, instChallengeOracleInterface]
  --     rw [evalDist_cast _ this, evalDist_query, evalDist_query]
  --     simp [OracleSpec.append, ChallengeIdx.inr, instChallengeOracleInterface]
  --     refine cast_eq_iff_heq.mpr ((PMF.heq_iff (by simp [this])).mpr ?_)
  --     intro x
  --     simp only [PMF.map_apply, PMF.uniformOfFintype_apply, Fin.append_right]
  --     refine tsum_cast (by simp) (fun a => ?_)
  --     congr <;> try { simp only [Fin.append_right] } <;> symm <;> simp only [cast_heq]

-- instance {ι₁ ι₂ ι₃ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
-- {spec₃ : OracleSpec ι₃}
--     [@SubSpec ι₁ ι₂ spec₁ spec₂] [@SubSpec ι₂ ι₃ spec₂ spec₃] :
-- @SubSpec ι₁ ι₃ spec₁ spec₃ := sorry

instance : SubSpec [pSpec₁.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inl i) t)

instance : SubSpec [pSpec₂.Challenge]ₒ ([(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) where
  monadLift | query i t => instSubSpecOfProtocolSpecAppendChallenge.monadLift (query (Sum.inr i) t)

end Instances

/--
Appending two provers corresponding to two reductions, where the output statement & witness type for
the first prover is equal to the input statement & witness type for the second prover. We also
require a verifier for the first protocol in order to derive the intermediate statement for the
second prover.

This is defined by combining the two provers' private states and functions, with the exception that
the last private state of the first prover is "merged" into the first private state of the second
prover (via outputting the new statement and witness, and then inputting these into the second
prover). -/
def Prover.append (P₁ : Prover pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (P₂ : Prover pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) :
      Prover (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ where

  /- The combined prover's states are the concatenation of the first prover's states, except the
  last one, and the second prover's states. -/
  PrvState := Fin.append (m := m) (Fin.init P₁.PrvState) P₂.PrvState ∘ Fin.cast (by omega)

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun stmt wit => by
    by_cases h : m > 0
    · simp [Fin.append, Fin.addCases, Fin.init, Fin.castLT, h]
      exact P₁.input stmt wit
    · simp [Fin.append, Fin.addCases, h, Fin.subNat]
      exact (
        letI state := P₁.input stmt wit
        haveI : 0 = Fin.last m := by aesop
        haveI state : P₁.PrvState (Fin.last m) := by simpa [this] using state
        P₂.input.uncurry (P₁.output state))

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m - 1`, then it sends the message & updates the state as the first prover
  - if `i = m - 1`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. It needs to
    provide a `stmt₂` for the second prover, which it derives from running the verifier on the first
    transcript. -/
  sendMessage := fun ⟨⟨i, hLt⟩, h⟩ state => by
    by_cases hi : i < m
    · dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
      by_cases hi' : i + 1 < m
      · simp [hi, hi'] at h state ⊢
        exact P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
      · haveI : i + 1 = m := by omega
        simp [hi, this] at h state ⊢
        exact (do
          let ⟨msg, state⟩ ← P₁.sendMessage ⟨⟨i, hi⟩, h⟩ state
          haveI state : P₁.PrvState (Fin.last m) := by
            simpa only [Fin.last, Fin.succ_mk, this] using state
          return ⟨msg, P₂.input.uncurry (P₁.output state)⟩)
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state ⊢
      exact (do
        let ⟨msg, newState⟩ ← P₂.sendMessage ⟨⟨i - m, by omega⟩, h⟩ state
        haveI newState : P₂.PrvState ⟨i + 1 - m, by omega⟩ := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa only [this, Fin.succ] using newState
        return ⟨msg, newState⟩)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨⟨i, hLt⟩, h⟩ state chal => by
    by_cases hi : i < m
    · simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state chal ⊢
      by_cases hi' : i + 1 < m
      · simp [hi']
        exact P₁.receiveChallenge ⟨⟨i, hi⟩, h⟩ state chal
      · haveI : i + 1 = m := by omega
        simp [this]
        exact (
          letI newState := P₁.receiveChallenge ⟨⟨i, hi⟩, h⟩ state chal
          haveI newState : P₁.PrvState (Fin.last m) := by
            simpa [Fin.last, this] using newState
          P₂.input.uncurry (P₁.output newState))
    · haveI : ¬ i + 1 < m := by omega
      simp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.init, hi, this,
        Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at h state chal ⊢
      exact (
        letI newState := P₂.receiveChallenge ⟨⟨i - m, by omega⟩, h⟩ state chal
        haveI newState := by
          haveI : i + 1 - m = i - m + 1 := by omega
          simpa [Fin.succ, this] using newState
        newState)

  /- The combined prover's output function is simply the second prover's output function. -/
  output := fun state => by
    simp [Fin.append, Fin.addCases, Fin.last] at state
    exact P₂.output state

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V₁ : Verifier pSpec₁ oSpec Stmt₁ Stmt₂)
    (V₂ : Verifier pSpec₂ oSpec Stmt₂ Stmt₃) :
      Verifier (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Stmt₃ where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Composition of reductions boils down to composing the provers and verifiers. -/
def Reduction.append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) :
      Reduction (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)] [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

open Function Embedding in
def OracleVerifier.append (V₁ : OracleVerifier pSpec₁ oSpec Stmt₁ Stmt₂ OStmt₁ OStmt₂)
    (V₂ : OracleVerifier pSpec₂ oSpec Stmt₂ Stmt₃ OStmt₂ OStmt₃) :
      OracleVerifier (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Stmt₃ OStmt₁ OStmt₃ where
  verify := fun stmt challenges => sorry

  embed := .trans V₂.embed <|
    .trans (.sumMap V₁.embed (.refl _)) <|
    .trans (Equiv.sumAssoc _ _ _).toEmbedding <|
    .sumMap (.refl _) MessageIdx.sumEquiv.toEmbedding

  hEq := fun i => by
    rcases h : V₂.embed i with j | j
    · rcases h' : V₁.embed j with k | k <;>
      simp [h, h', V₁.hEq j, V₂.hEq i, MessageIdx.inl]
    · simp [h, V₂.hEq i, MessageIdx.inr]

def OracleReduction.append (R₁ : OracleReduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ OStmt₁ OStmt₂)
    (R₂ : OracleReduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ OStmt₂ OStmt₃) :
      OracleReduction (pSpec₁ ++ₚ pSpec₂) oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ OStmt₁ OStmt₃ where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

section GeneralComposition

namespace ProtocolSpec

/-- Composition of a family of `ProtocolSpec`s, indexed by `i : Fin (m + 1)`. -/
def compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i)) :
    ProtocolSpec (∑ i, n i) := sorry
  -- cast (by rw [Finset.Iic_top])
  --   (Fin.dfoldl m (fun i => ProtocolSpec (∑ j ≤ i, n j))
  --     (fun i acc => cast (Fin.sum_Iic_succ i).symm (acc ++ₚ pSpec i.succ))
  --       (cast (Fin.sum_Iic_zero).symm (pSpec 0)))

@[simp]
theorem compose_zero {n : ℕ} {pSpec : ProtocolSpec n} :
    compose 0 (fun _ => n) (fun _ => pSpec) = pSpec := sorry

set_option maxHeartbeats 1000000
theorem compose_append {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)} (i : Fin m) :
    compose (i + 1) (Fin.take (i + 2) (by omega) n) (Fin.take (i + 2) (by omega) pSpec) =
      cast (by simp [Fin.sum_univ_castSucc]; congr)
        (compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec)
          ++ₚ pSpec i.succ) := by
  -- simp only [id_eq, Fin.take_apply, compose, cast_eq_self, Fin.dfoldl_succ_last, Fin.succ_last,
  --   Nat.succ_eq_add_one, Function.comp_apply, cast_trans, append_cast_left, cast_eq_cast_iff]
  -- unfold Function.comp Fin.castSucc Fin.castAdd Fin.castLE Fin.last Fin.succ
  -- simp only [Fin.val_zero, Fin.zero_eta]
  -- simp only [append_cast_left', append_left_cancel_iff]
  -- funext x
  -- unfold cast Fin.cast Function.comp ProtocolSpec
  -- simp only
  sorry
  -- unfold compose
  -- induction m with
  -- | zero => exact Fin.elim0 i
  -- | succ m ih =>
  --   induction i using Fin.induction with
  --   | zero => simp only [Fin.val_zero, Fin.dfoldl_zero, cast_eq_self]
  --   | succ i ih =>
  --     simp only [Fin.val_succ, Fin.dfoldl_succ_last, Fin.val_last, Function.comp_apply,
  --       Fin.coe_castSucc, cast_eq_self, cast_trans]
  --     simp only [Fin.coe_castSucc] at ih
  --     unfold Function.comp Fin.castSucc Fin.castAdd Fin.castLE Fin.last Fin.succ
  --     simp only [cast_trans, cast_eq_cast_iff, append_cast_left', append_left_cancel_iff]

/-- Composition of a family of `FullTranscript`s, indexed by `i : Fin (m + 1)`. -/
def FullTranscript.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (T : ∀ i, FullTranscript (pSpec i)) : FullTranscript (compose m n pSpec) := by
  simpa using Fin.dfoldl m
      (fun i => FullTranscript (ProtocolSpec.compose i
        (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec)))
      (fun i acc => by
        have := acc ++ₜ (T i.succ)
        unfold FullTranscript at this ⊢
        simp [Fin.castSucc] at this
        simp [compose_append]
        -- refine FullTranscript.cast ?_ this
        sorry)
    (by stop exact T 0)

section Instances

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

/-- If two protocols have sampleable challenges, then their concatenation also has sampleable
  challenges. -/
instance [h : ∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)] :
    ∀ j, Sampleable ((compose m n pSpec).Challenge j) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.compose, Fin.append, Fin.addCases, Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  sorry
  -- by_cases h' : i < m <;> simp [h'] at h ⊢
  -- · exact h₁ ⟨⟨i, by omega⟩, h⟩
  -- · exact h₂ ⟨⟨i - m, by omega⟩, h⟩

/-- If two protocols' messages have oracle representations, then their concatenation's messages also
    have oracle representations. -/
instance [O : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)] :
    ∀ i, OracleInterface ((compose m n pSpec).Message i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.compose, ProtocolSpec.getDir, Fin.append, Fin.addCases,
    Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  sorry
  -- by_cases h' : i < m <;> simp [h'] at h ⊢
  -- · exact O₁ ⟨⟨i, by omega⟩, h⟩
  -- · exact O₂ ⟨⟨i - m, by omega⟩, h⟩

-- open OracleComp OracleSpec SubSpec

-- variable [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]

-- instance : SubSpec (challengeOracle pSpec₁ ++ₒ challengeOracle pSpec₂)
--     (challengeOracle (compose m n pSpec)) := sorry

end Instances

end ProtocolSpec

def Prover.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    (P : ∀ i, Prover (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ)
      (Wit i.succ)) :
      Prover (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
        (Wit (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Prover
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ))
    (fun i acc => by
      convert Prover.append acc (P i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, ProtocolSpec.cast_eq_root_cast])
    (by stop simpa using P 0)

def Verifier.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type)
    (V : ∀ i, Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ)) :
      Verifier (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Stmt (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Verifier
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Stmt i.succ))
    (fun i acc => by
      convert Verifier.append acc (V i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, ProtocolSpec.cast_eq_root_cast])
    (by stop simpa using V 0)

def Reduction.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    (R : ∀ i, Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ)
      (Wit i.succ)) :
      Reduction (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
        (Wit (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Reduction
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ))
    (fun i acc => by
      convert Reduction.append acc (R i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, ProtocolSpec.cast_eq_root_cast])
    (by stop simpa using R 0)

end GeneralComposition

section Execution

open OracleComp OracleSpec SubSpec

variable [∀ i, Sampleable (pSpec₁.Challenge i)] [∀ i, Sampleable (pSpec₂.Challenge i)]
  [oSpec.DecidableEq]

theorem Prover.append_run (P₁ : Prover pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (P₂ : Prover pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃) (stmt : Stmt₁) (wit : Wit₁) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨stmt₂, wit₂, transcript₁⟩ ← liftM (P₁.run stmt wit)
        let ⟨stmt₃, wit₃, transcript₂⟩ ← liftM (P₂.run stmt₂ wit₂)
        -- TODO: should we refactor the prover to take in a running query log?
        return ⟨stmt₃, wit₃, transcript₁ ++ₜ transcript₂⟩) :=
  sorry

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Execution

section Security

open scoped NNReal

namespace Reduction

section Append

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n} [∀ i, Sampleable (pSpec₁.Challenge i)]
    [∀ i, Sampleable (pSpec₂.Challenge i)] {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {rel₁ : Stmt₁ → Wit₁ → Prop} {rel₂ : Stmt₂ → Wit₂ → Prop} {rel₃ : Stmt₃ → Wit₃ → Prop}
    [oSpec.DecidableEq] [oSpec.FiniteRange]

/-- If two reductions satisfy completeness with compatible relations, then their concatenation also
  satisfies completeness with the sum of the completeness errors. -/
theorem completeness_append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness rel₁ rel₃ (completenessError₁ + completenessError₂) := sorry

/-- If two reductions satisfy perfect completeness with compatible relations, then their
  concatenation also satisfies perfect completeness. -/
theorem perfectCompleteness_append (R₁ : Reduction pSpec₁ oSpec Stmt₁ Wit₁ Stmt₂ Wit₂)
    (R₂ : Reduction pSpec₂ oSpec Stmt₂ Wit₂ Stmt₃ Wit₃)
    (h₁ : R₁.perfectCompleteness rel₁ rel₂) (h₂ : R₂.perfectCompleteness rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness rel₁ rel₃ := by
  dsimp [perfectCompleteness] at h₁ h₂ ⊢
  convert Reduction.completeness_append R₁ R₂ h₁ h₂
  simp only [add_zero]

end Append

section GeneralComposition

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]
    {Stmt : Fin (m + 2) → Type} {Wit : Fin (m + 2) → Type} {rel : ∀ i, Stmt i → Wit i → Prop}
    [oSpec.DecidableEq] [oSpec.FiniteRange]

theorem completeness_compose
    (R : ∀ i, Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ))
    (completenessError : Fin (m + 1) → ℝ≥0)
    (h : ∀ i, (R i).completeness (rel i.castSucc) (rel i.succ) (completenessError i)) :
      (Reduction.compose m n pSpec Stmt Wit R).completeness (rel 0) (rel (Fin.last (m + 1)))
        (∑ i, completenessError i) := sorry


end GeneralComposition

end Reduction

end Security
