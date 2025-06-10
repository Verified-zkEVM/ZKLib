/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši
-/

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.RelativeHammingDistance

open Classical

noncomputable section

/-!
Definition of an interleaved code `IC` of a linear code `LC` over a semiring.
Definition of distances for interleaved codes and statement for the relation between the minimal
distance of an interleaved code and its underlying linear code.-/

variable {F : Type*} [Semiring F]
         {ι : Type*} [Fintype ι]
         {κ : ℕ}
         {LC : LinearCode ι F}

namespace InterleavedCodes

abbrev MatrixSubmodule.{u, v} (κ : ℕ) (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] :
  Type (max u v) :=
    Submodule F (Matrix (Fin κ) ι F)

/--
The data needed to construct an interleaved code.
-/
structure InterleavedCode (κ : ℕ) (ι F : Type*) [Semiring F] [Fintype ι] where
  MF : MatrixSubmodule κ ι F
  LC : LinearCode ι F

/--
The condition making the InterleavedCode structure an interleaved code.
-/
def InterleavedCode.isInterleaved (κ : ℕ) (ι F : Type*) [Semiring F] [Fintype ι]
  (IC : InterleavedCode κ ι F) : Prop :=
  ∀ V ∈ IC.MF, ∀ i, V i ∈ IC.LC


def LawfulInterleavedCode.{u, v} (κ : ℕ) (ι : Type u) [Fintype ι] (F : Type v) [Semiring F] :
  Type (max u v) :=
  { IC : InterleavedCode κ ι F // InterleavedCode.isInterleaved κ ι F IC }


/--
The module of matrices whose rows belong to a linear code.
-/
def matrixSubmoduleOfLinearCode (κ : ℕ) (LC : LinearCode ι F) : MatrixSubmodule κ ι F :=
  Submodule.span F { V | ∀ i, V i ∈ LC }

def codeOfLinearCode (κ : ℕ) (LC : LinearCode ι F) : InterleavedCode κ ι F :=
  { MF := matrixSubmoduleOfLinearCode κ LC, LC := LC }

/--
The module of matrices whose rows belong to a linear code is in fact an interleaved code.
-/
lemma isInterleaved_codeOfLinearCode : (codeOfLinearCode κ LC).isInterleaved := by sorry

def lawfulInterleavedCodeOfLinearCode (κ : ℕ) (LC : LinearCode ι F) : LawfulInterleavedCode κ ι F :=
  ⟨codeOfLinearCode κ LC, isInterleaved_codeOfLinearCode⟩

/--
The set of indices of non-equal columns of two matrices.
-/
def neqCols [DecidableEq F] (U V : Matrix (Fin κ) ι F) : Finset ι :=
  {j | ∃ i : (Fin κ), V i j ≠ U i j}

/--
Distance between codewords of an interleaved code.
 -/
def distCodewords [DecidableEq F] (U V : Matrix (Fin κ) ι F) : ℕ :=
  (neqCols U V).card

/--
`Δ(U,V)` is the distance codewords `U` and `V` of a `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," V ")" => distCodewords U V

/--
The minimal distance of an interleaved code.
-/
def minDist (IC : MatrixSubmodule κ ι F) : ℕ :=
  sInf { d : ℕ | ∃ U ∈ IC, ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ IC` is the min distance of an interleaved code `IC`.
-/
notation "Δ" IC => minDist IC

/--
The distance from a matrix to the closest word in an interleaved code.
-/
def distToCode (U : Matrix (Fin κ) ι F) (IC : MatrixSubmodule κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ(U,C')` denotes distance between a `κ x ι` matrix `U` and `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," IC ")" => distToCode U IC

/--
Relative distance between codewords of an interleaved code.
 -/
def relDistCodewords [DecidableEq F] (U V : Matrix (Fin κ) ι F) : ℝ :=
  (neqCols U V).card / Fintype.card ι

/--Ball of radius `r` centered at U, with respect to relative Hamming distance.-/
def relHammingBallInterleavedCode (U : Matrix (Fin κ) ι F) (IC : MatrixSubmodule κ ι F) (r : ℝ) :=
  {V | V ∈ IC ∧ relDistCodewords U V < r}

notation "Λᵢ(" U "," IC "," r ")" => relHammingBallInterleavedCode U IC r

end InterleavedCodes
