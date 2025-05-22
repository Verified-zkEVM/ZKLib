/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Basic
import Batteries.Data.Fin.Fold
import ArkLib.OracleReduction.Basic

/-! # Sequential Composition of Protocol Specifications

This file collects all definitions and theorems about sequentially composing `ProtocolSpec`s and
their associated data. -/

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

end find_home

namespace ProtocolSpec

/-! ### Restriction of Protocol Specifications & Transcripts -/

section Restrict

variable {n : ℕ}

/-- Take the first `m ≤ n` rounds of a `ProtocolSpec n` -/
abbrev take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) := Fin.take m h pSpec

/-- Take the last `m ≤ n` rounds of a `ProtocolSpec n` -/
abbrev rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) := Fin.rtake m h pSpec

/-- Take the first `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev FullTranscript.take {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.take m h) :=
  Fin.take m h transcript

/-- Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev FullTranscript.rtake {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rtake m h) :=
  Fin.rtake m h transcript

end Restrict

/-! ### Casting Protocol Specifications -/

section Cast

variable {n n' n'' m k : ℕ}

/-- Casting a `ProtocolSpec` across an equality of the number of rounds -/
def cast (h : n = n') (pSpec : ProtocolSpec n) : ProtocolSpec n' :=
  pSpec ∘ (Fin.cast h.symm)

@[simp]
theorem cast_refl {h : n = n} : cast h = id := rfl

@[simp]
theorem cast_eq_self {pSpec : ProtocolSpec n} : cast (refl n) pSpec = pSpec := by
  simp only [cast, Fin.cast_refl, CompTriple.comp_eq]

@[simp]
theorem cast_trans {pSpec : ProtocolSpec n} (h : n = n') (h' : n' = n'') :
    cast h' (cast h pSpec) = cast (h.trans h') pSpec := by
  subst h; subst h'; simp only [cast, Fin.cast_refl, CompTriple.comp_eq]

@[simp]
theorem cast_eq_cast_iff {pSpec : ProtocolSpec n} {pSpec' : ProtocolSpec m}
    (h : n = k) (h' : m = k) :
      cast h pSpec = cast h' pSpec' ↔ pSpec = cast (h'.trans h.symm) pSpec' := by
  subst h; subst h'; simp only [cast, Fin.cast_refl, CompTriple.comp_eq]

theorem cast_eq_root_cast {pSpec : ProtocolSpec n} (h : n = m) :
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
    (pSpec.take k (Nat.le_of_succ_le h) ++ₚ (fun (_ : Fin 1) => pSpec ⟨k, h⟩))
      = pSpec.take (k + 1) h := by
  simp only [append, take, Fin.append_right_eq_snoc, Fin.take_succ_eq_snoc]

variable {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

@[simp]
theorem take_append_left :
    (pSpec₁ ++ₚ pSpec₂).take m (Nat.le_add_right m n) = pSpec₁ := by
  simp only [take, append]
  ext i : 1
  have : Fin.castLE (by omega) i = Fin.castAdd n i := rfl
  simp [Fin.take_apply, Fin.append_left, this]

@[simp]
theorem rtake_append_right :
    (pSpec₁ ++ₚ pSpec₂).rtake n (Nat.le_add_left n m) = pSpec₂ := by
  simp only [rtake, append]
  ext i : 1
  simp [Fin.rtake_apply, Fin.append_right]

namespace FullTranscript

section Cast

/-- Casting a transcript across an equality of `ProtocolSpec`s -/
def cast (h : m = n) (hSpec : pSpec₁.cast h = pSpec₂) (T : FullTranscript pSpec₁) :
    FullTranscript pSpec₂ :=
  fun i => _root_.cast (congrFun (congrArg getType hSpec) i) (T (Fin.cast h.symm i))

variable {n m n' n'' k : ℕ} {pSpec pSpec₁ : ProtocolSpec n}
  {pSpec₂ : ProtocolSpec m} {pSpec₃ : ProtocolSpec k}

@[simp]
theorem cast_refl : cast rfl rfl = (id : pSpec.FullTranscript → _) := rfl

@[simp]
theorem cast_eq_self {T : FullTranscript pSpec} : cast rfl rfl T = T := rfl

@[simp]
theorem cast_trans (h : n = m) (h' : m = k) (hSpec : pSpec₁.cast h = pSpec₂)
    (hSpec' : pSpec₂.cast h' = pSpec₃) (T : FullTranscript pSpec₁) :
      cast h' hSpec' (cast h hSpec T) = cast (h.trans h') (by simp [← hSpec, ← hSpec']) T := by
  subst h; subst h'; subst hSpec; subst hSpec'; simp

@[simp]
theorem cast_eq_cast_iff (h : n = k) (h' : m = k) (hSpec : pSpec₁.cast h = pSpec₃)
    (hSpec' : pSpec₂.cast h' = pSpec₃) (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
      cast h hSpec T₁ = cast h' hSpec' T₂ ↔
        T₁ = cast (h'.trans h.symm)
          (by rw [← hSpec'] at hSpec; symm; exact (ProtocolSpec.cast_eq_cast_iff h h').mp hSpec)
          T₂ := by
  subst h; subst h'; subst hSpec; simp at hSpec'; subst hSpec'; simp

theorem cast_eq_root_cast (h : n = m) (hSpec : pSpec₁.cast h = pSpec₂) (T : FullTranscript pSpec₁) :
    cast h hSpec T = _root_.cast (by subst h; subst hSpec; simp) T := by
  subst h; subst hSpec; simp

end Cast

/-- Appending two transcripts for two `ProtocolSpec`s -/
def append (T₁ : FullTranscript pSpec₁) (T₂ : FullTranscript pSpec₂) :
    FullTranscript (pSpec₁ ++ₚ pSpec₂) :=
  fun i => (Fin.append_comp' Prod.snd i).mp (Fin.addCases' T₁ T₂ i)

@[inherit_doc]
infixl : 65 " ++ₜ " => append

/-- Adding a message with a given direction and type to the end of a `Transcript` -/
def snoc {pSpec : ProtocolSpec n} {NextMessage : Type}
    (T : FullTranscript pSpec) (dir : Direction) (msg : NextMessage) :
        FullTranscript (pSpec ++ₚ .mkSingle dir NextMessage) :=
  append T fun _ => msg

theorem take_append_left (T : FullTranscript pSpec₁) (T' : FullTranscript pSpec₂) :
    ((T ++ₜ T').take m (Nat.le_add_right m n)) =
      T.cast (by omega) (by simp [ProtocolSpec.append]) := by
  ext i
  simp [take, append, ProtocolSpec.append, Fin.castLE, Fin.addCases', Fin.addCases,
    FullTranscript.cast]

/-- The first half of a transcript for a concatenated protocol -/
def fst (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : FullTranscript pSpec₁ :=
  fun i => by
    simpa [ProtocolSpec.append, Fin.append_left] using T (Fin.castAdd n i)

/-- The second half of a transcript for a concatenated protocol -/
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
