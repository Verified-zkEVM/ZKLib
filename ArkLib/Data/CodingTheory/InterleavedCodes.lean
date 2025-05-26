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
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Distributions.Uniform
import ArkLib.Data.CodingTheory.LinearCodes
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Prelims


open Classical LinearCode

noncomputable section

/-!
Definition of an interleaved code `IC` of a linear code `LC` over a semiring.
Definition of distances for interleaved codes and statement for the relation between the minimal
distance of an interleaved code and its underlying linear code.
Statements of proximity results for Reed Solomon codes
(`Lemma 4.3`, `Lemma 4.4` and `Lemma 4.5` from Ligero) with proximity parameter less than
the minimal code distance divided by `3`.
-/

variable {F : Type*} [Semiring F]
         {κ ι: ℕ}
         {LC : LinearCode ι F}

namespace InterleavedCodes

abbrev MatrixSubmodule.{u} (κ ι : ℕ) (F : Type u) [Semiring F] : Type u :=
  Submodule F (Matrix (Fin κ) (Fin ι) F)

/--
The data needed to construct an interleaved code.
-/
structure InterleavedCode (κ ι : ℕ) (F : Type*) [Semiring F] where
  MF : MatrixSubmodule κ ι F
  LC : LinearCode ι F

/--
The condition making the InterleavedCode structure an interleaved code.
-/
def InterleavedCode.isInterleaved (IC : InterleavedCode κ ι F) :=
  ∀ V ∈ IC.MF, ∀ i, V i ∈ IC.LC

def LawfulInterleavedCode.{u} (κ ι : ℕ) (F : Type u) [Semiring F] :=
  { IC : InterleavedCode κ ι F // IC.isInterleaved }

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
Distance between codewords of an interleaved code.
 -/
def distCodewords (U V : Matrix (Fin κ) (Fin ι) F) : ℕ :=
  (Matrix.neqCols U V).card

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
def distToCode (U : Matrix (Fin κ) (Fin ι) F) (IC : MatrixSubmodule κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ(U,C')` denotes distance between a `κ x ι` matrix `U` and `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," IC ")" => distToCode U IC

/--
The minimal distance of an interleaved code is the same as
the minimal distance of its underlying linear code.
-/
lemma minDistL_eq_minDist {IC : LawfulInterleavedCode κ ι F} :
  LinearCode.minDist IC.1.LC = minDist IC.1.MF := by sorry

end InterleavedCodes
