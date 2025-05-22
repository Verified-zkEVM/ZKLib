/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Fin.Basic

/-! # Dependent casts

This file contains type classes for dependent or custom cast operations

This allows us to state theorems with more refined casts, without which we cannot make progress in
proving them -/

universe u v w

section Prelude

-- Some missing theorems about `cast` and `congrArg`

theorem cast_eq_cast_iff {α β γ : Sort u} {h : α = γ} {h' : β = γ} {a : α} {b : β} :
    cast h a = cast h' b ↔ a = cast (h'.trans h.symm) b := by subst h'; subst h; simp

theorem cast_symm {α β : Sort u} {h : α = β} {a : α} {b : β} :
    cast h a = b ↔ a = cast h.symm b := by
  subst h; simp

theorem congrArg₃ {α β γ δ : Sort*} {f : α → β → γ → δ} {a a' : α} {b b' : β} {c c' : γ}
    (h : a = a') (h' : b = b') (h'' : c = c') : f a b c = f a' b' c' := by
  subst h; subst h'; subst h''; rfl

theorem congrArg₄ {α β γ δ ε : Sort*} {f : α → β → γ → δ → ε} {a a' : α} {b b' : β} {c c' : γ}
    {d d' : δ} (h : a = a') (h' : b = b') (h'' : c = c') (h''' : d = d') :
      f a b c d = f a' b' c' d' := by
  subst h; subst h'; subst h''; subst h'''; rfl

end Prelude

/-- `DepCast` is a type class for custom cast operations on an indexed type family `β a`

We require the cast operation `dcast`, along with the property that `dcast` reduces to `id` under
reflexivity. -/
class DepCast (α : Sort*) (β : α → Sort*) where
  dcast : ∀ {a a' : α}, a = a' → β a → β a'
  dcast_id : ∀ {a : α}, dcast (Eq.refl a) = id

export DepCast (dcast dcast_id)
attribute [simp] dcast_id

section DepCast

variable {α : Sort*} {β : α → Sort*} [DepCast α β] {a a' a'' : α} {b : β a} {b' : β a'}

/-- The default instance for `DepCast` -/
instance (priority := low) : DepCast α β where
  dcast h := cast (congrArg β h)
  dcast_id := by intro a; funext b; simp only [cast_eq, id_eq]

@[simp]
theorem dcast_eq : dcast (Eq.refl a) b = b := by
  simp

theorem dcast_symm (ha : a = a') (hb : dcast ha b = b') : dcast (ha.symm) b' = b := by
  subst ha; subst hb; simp

@[simp]
theorem dcast_trans (h : a = a') (h' : a' = a'') :
    dcast h' (dcast h b) = dcast (h.trans h') b := by
  subst h; subst h'; simp

theorem dcast_eq_dcast_iff (h : a = a'') (h' : a' = a'') :
    dcast h b = dcast h' b' ↔ b = dcast (h'.trans h.symm) b' := by
  subst h; subst h'; simp

end DepCast

/-- `DepCast₂` is a type class for custom cast operations on a doubly-indexed type family `γ a b`,
  given an underlying dependent cast `DepCast α β`

We require the cast operation `dcast₂`, along with the property that `dcast₂` reduces to `id` under
reflexivity. -/
class DepCast₂ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*) [DepCast α β] where
  dcast₂ : ∀ {a a' : α} {b : β a} {b' : β a'},
    (ha : a = a') → (dcast ha b = b') → γ a b → γ a' b'
  dcast₂_id : ∀ {a : α} {b : β a}, dcast₂ (Eq.refl a) dcast_eq = (id : γ a b → γ a b)

export DepCast₂ (dcast₂ dcast₂_id)
attribute [simp] dcast₂_id

section DepCast₂

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*} [DepCast α β] [DepCast₂ α β γ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''} {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}

/-- Default instance for `DepCast₂` -/
instance (priority := low) : DepCast₂ α β γ where
  dcast₂ ha hb c := by
    refine cast ?_ c
    subst ha; simp at hb; subst hb; rfl
  dcast₂_id := by intros; rfl

@[simp]
theorem dcast₂_eq : dcast₂ (Eq.refl a) dcast_eq c = c := by
  simp

@[simp]
theorem dcast₂_eq' (h : a = a) (h' : dcast h b = b) : dcast₂ h h' c = c := by
  cases h; simp

theorem dcast₂_symm (ha : a = a') (hb : dcast ha b = b') (hc : dcast₂ ha hb c = c') :
    dcast₂ ha.symm (dcast_symm ha hb) c' = c := by
  cases ha; simp at hb; subst hb; simp at hc; subst hc; simp

@[simp]
theorem dcast₂_trans (ha : a = a') (ha' : a' = a'')
    (hb : dcast ha b = b') (hb' : dcast ha' b' = b'') :
      dcast₂ ha' hb' (dcast₂ ha hb c) = dcast₂ (ha.trans ha') (by simp [← hb', ← hb]) c := by
  cases ha; simp at hb; subst hb; subst hb'; simp

theorem dcast₂_eq_dcast₂_iff (ha : a = a'') (ha' : a' = a'')
    (hb : dcast ha b = b'') (hb' : dcast ha' b' = b'') :
    dcast₂ ha hb c = dcast₂ ha' hb' c' ↔
      c = dcast₂ (ha'.trans ha.symm)
        ((dcast_eq_dcast_iff ha ha').mp (hb.trans hb'.symm)).symm c' := by
  cases ha; cases ha'; simp at hb; subst hb; simp at hb'; subst hb'; simp

instance instDepCast₁₂ : DepCast (β a) (γ a) where
  dcast hb c := dcast₂ (Eq.refl a) (by simp [hb]) c
  dcast_id := by intros; ext c; exact dcast₂_eq

instance instDepCastPSigma : DepCast ((a : α) ×' β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (by subst hab; simp) (by subst hab; simp) c
  dcast_id := by intros; ext c; simp

instance instDepCastSigma {α : Type*} {β : α → Type*} {γ : (a : α) → β a → Type*}
    [DepCast α β] [DepCast₂ α β γ] : DepCast ((a : α) × β a) (fun a => γ a.1 a.2) where
  dcast hab c := dcast₂ (by subst hab; simp) (by subst hab; simp) c
  dcast_id := by intros; ext c; simp

end DepCast₂

/-- `DepCast₃` is a type class for custom cast operations on a triply-indexed type family `δ a b c`,
  given underlying dependent casts `DepCast α β` and `DepCast₂ α β γ`

We require the cast operation `dcast₃`, along with the property that `dcast₃` reduces to `id` under
reflexivity. -/
class DepCast₃ (α : Sort*) (β : α → Sort*) (γ : (a : α) → β a → Sort*)
    (δ : (a : α) → (b : β a) → γ a b → Sort*) [DepCast α β] [DepCast₂ α β γ] where
  dcast₃ : ∀ {a a' : α} {b : β a} {b' : β a'} {c : γ a b} {c' : γ a' b'},
    (ha : a = a') → (hb : dcast ha b = b') → (hc : dcast₂ ha hb c = c') → δ a b c → δ a' b' c'
  dcast₃_id : ∀ {a : α} {b : β a} {c : γ a b},
    dcast₃ (Eq.refl a) dcast_eq dcast₂_eq = (id : δ a b c → δ a b c)

export DepCast₃ (dcast₃ dcast₃_id)
attribute [simp] dcast₃_id

section DepCast₃

variable {α : Sort*} {β : α → Sort*} {γ : (a : α) → β a → Sort*}
  {δ : (a : α) → (b : β a) → γ a b → Sort*}
  [DepCast α β] [DepCast₂ α β γ] [DepCast₃ α β γ δ]
  {a a' a'' : α} {b : β a} {b' : β a'} {b'' : β a''}
  {c : γ a b} {c' : γ a' b'} {c'' : γ a'' b''}
  {d : δ a b c} {d' : δ a' b' c'} {d'' : δ a'' b'' c''}

/-- Default instance for `DepCast₃` -/
instance (priority := low) : DepCast₃ α β γ δ where
  dcast₃ ha hb hc d := by
    refine cast ?_ d
    subst ha; simp at hb; subst hb; simp at hc; subst hc; rfl
  dcast₃_id := by intros; rfl

@[simp]
theorem dcast₃_eq : dcast₃ (Eq.refl a) dcast_eq dcast₂_eq d = d := by
  simp

theorem dcast₃_symm (ha : a = a') (hb : dcast ha b = b') (hc : dcast₂ ha hb c = c')
    (hd : dcast₃ ha hb hc d = d') :
    dcast₃ ha.symm (dcast_symm ha hb) (dcast₂_symm ha hb hc) d' = d := by
  cases ha; simp at hb; subst hb; simp at hc; subst hc; simp at hd; subst hd; simp

-- @[simp]
-- theorem dcast₃_trans (ha : a = a') (ha' : a' = a'')
--     (hb : dcast ha b = b') (hb' : dcast ha' b' = b'')
--     (hc : dcast₂ ha hb c = c') (hc' : dcast₂ ha' hb' c' = c'') :
--     dcast₃ ha' hb' hc' (dcast₃ ha hb hc d) =
--     dcast₃ (ha.trans ha')
--            (Eq.trans (dcast_trans ha ha') (Eq.trans hb hb'))
--            (Eq.trans (dcast₂_trans ha ha' hb hb') (Eq.trans hc hc')) d := by
--   cases ha; simp at hb; subst hb; simp at hc; subst hc; simp at hd; subst hd; simp

theorem dcast₃_eq_dcast₃_iff (ha : a = a') (hb : dcast ha b = b') (hc : dcast₂ ha hb c = c') :
    dcast₃ ha hb hc d = d' ↔ d = dcast₃ ha.symm (dcast_symm ha hb) (dcast₂_symm ha hb hc) d' := by
  cases ha; simp at hb; subst hb; simp at hc; subst hc; simp

-- instance instDepCast₂₃ {a : α} : DepCast₂ (β a) (γ a) (δ a) where
--   dcast₂ ha hb c := dcast₃ (Eq.refl a) (by simp [ha]) (by simp [hb]) c
--   dcast₂_id := by intros; rfl

-- instance instDepCast₁₃ {a : α} {b : β a} : DepCast (γ a b) (δ a b) where
--   dcast hc d := dcast₃ (Eq.refl a) dcast_eq hc d
--   dcast_id := by intros; ext d; exact dcast₃_eq


end DepCast₃

namespace Fin

/-- `Fin.cast` as a `DepCast` (which should override the default instance). -/
instance instDepCast : DepCast Nat Fin where
  dcast h := Fin.cast h
  dcast_id := by simp only [Fin.cast_refl, implies_true]

theorem cast_eq_dcast {m n : ℕ} (h : m = n) (a : Fin m) :
    Fin.cast h a = dcast h a := by
  simp only [cast_eq_cast, dcast]

-- instance instDepCastForall {α : Sort*} : DepCast Nat (fun _ => α) where
--   dcast h := fun a => Fin.cast h a
--   dcast_id := by simp only [Fin.cast_refl, implies_true]

end Fin
