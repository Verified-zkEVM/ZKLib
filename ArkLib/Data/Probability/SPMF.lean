/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Std.Data.Rat.Basic
import Std.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Probability.Distributions.Uniform

/-- `SPMF` is a computable type representing sub-probability distributions with finite support. -/
def SPMF (α : Type) := α →₀ Rat


namespace SPMF

variable {α : Type}

def length (d : SPMF α) : Rat := d.support.card

def count (d : SPMF α) (a : α) : Rat := d a

def pure (a : α) := Finsupp.single a 1

def bind {α β : Type} (d : SPMF α) (f : α → SPMF β) : SPMF β :=
  List.bind d f

instance Monad : Monad SPMF := {
  pure := @pure,
  bind := @bind
}

def toFun {α : Type} [BEq α] (d : SPMF α) : α → Rat :=
  fun a => d.count a / d.length

def uniformOfFintype (α : Type) [Fintype α] [Nonempty α] : SPMF α := [] -- TODO implement

end SPMF
