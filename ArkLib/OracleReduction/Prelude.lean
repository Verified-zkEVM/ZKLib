/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio

/-!
  # Prelude for Interactive (Oracle) Reductions

  This file contains preliminary definitions and instances that is used in defining I(O)Rs.
-/

open OracleComp

-- Figure out where to put this instance
instance instDecidableEqOption {α : Type*} [DecidableEq α] :
    DecidableEq (Option α) := inferInstance

/-- `VCVCompabible` is a type class for types that are finite, inhabited, and have decidable
  equality. These instances are needed when the type is used as the range of some `OracleSpec`. -/
class VCVCompatible (α : Type*) extends Fintype α, Inhabited α where
  [type_decidableEq' : DecidableEq α]

instance {α : Type*} [VCVCompatible α] : DecidableEq α := VCVCompatible.type_decidableEq'

instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Fin n → α) where

instance {α : Type*} {n : ℕ} [VCVCompatible α] : VCVCompatible (Vector α n) := sorry

/-- `Sampleable` extends `VCVCompabible` with `SelectableType` -/
class Sampleable (α : Type) extends VCVCompatible α, SelectableType α

instance {α : Type} [Sampleable α] : DecidableEq α := inferInstance

/-- Enum type for the direction of a round in a protocol specification -/
inductive Direction where
  | P_to_V  -- Message
  | V_to_P -- Challenge
deriving DecidableEq, Inhabited, Repr

/-- Equivalence between `Direction` and `Fin 2`, sending `V_to_P` to `0` and `P_to_V` to `1`
(the choice is essentially arbitrary). -/
def directionEquivFin2 : Direction ≃ Fin 2 where
  toFun := fun dir => match dir with | .V_to_P => ⟨0, by decide⟩ | .P_to_V => ⟨1, by decide⟩
  invFun := fun n => match n with | ⟨0, _⟩ => .V_to_P | ⟨1, _⟩ => .P_to_V
  left_inv := fun dir => match dir with | .P_to_V => rfl | .V_to_P => rfl
  right_inv := fun n => match n with | ⟨0, _⟩ => rfl | ⟨1, _⟩ => rfl

/-- This allows us to write `0` for `.V_to_P` and `1` for `.P_to_V`. -/
instance : Coe (Fin 2) Direction := ⟨directionEquivFin2.invFun⟩

section Relation

/-- The associated language `Set α` for a relation `α → β → Prop`. -/
def Function.language {α β} (rel : α → β → Prop) : Set α :=
  {stmt | ∃ wit, rel stmt wit}

/-- The trivial relation on Boolean statement and unit witness, which outputs the Boolean (i.e.
  accepts or rejects). -/
def acceptRejectRel : Bool → Unit → Prop := fun b _ => b

/-- The trivial relation on Boolean statement, no oracle statements, and unit witness. -/
def acceptRejectOracleRel : Bool × (∀ _ : Empty, Unit) → Unit → Prop := fun ⟨b, _⟩ _ => b

@[simp]
theorem acceptRejectRel_language : acceptRejectRel.language = { true } := by
  unfold Function.language acceptRejectRel; simp

@[simp]
theorem acceptRejectOracleRel_language :
    acceptRejectOracleRel.language = { ⟨true, isEmptyElim⟩ } := by
  unfold Function.language acceptRejectOracleRel; simp; ext; aesop

end Relation
