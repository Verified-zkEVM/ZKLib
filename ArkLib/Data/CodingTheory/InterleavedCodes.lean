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


open Classical LinearCodes

noncomputable section

/-!
Definition of a `κ`-interleaved code `IC` of a linear code `LC` over a semiring `F`.
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
The data needed to construct an interleaved code
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

def matrixSubmoduleOfLinearCode (κ : ℕ) (LC : LinearCode ι F) : MatrixSubmodule κ ι F :=
  Submodule.span F { V | ∀ i, V i ∈ LC }

def codeOfLinearCode (κ : ℕ) (LC : LinearCode ι F) : InterleavedCode κ ι F :=
  { MF := matrixSubmoduleOfLinearCode κ LC, LC := LC }

lemma isInterleaved_codeOfLinearCode : (codeOfLinearCode κ LC).isInterleaved := by sorry

def lawfulInterleavedCodeOfLinearCode (κ : ℕ) (LC : LinearCode ι F) : LawfulInterleavedCode κ ι F :=
  ⟨codeOfLinearCode κ LC, isInterleaved_codeOfLinearCode⟩

/--
distance between codewords `U` and `V` in a `κ`-interleaved code.
 -/
def distCodewords (U V : Matrix (Fin κ) (Fin ι) F) : ℕ :=
  (Matrices.neqCols U V).card

/--
`Δ(U,V)` is the distance codewords `U` and `V` of a `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," V ")" => distCodewords U V

def minDist (IC : MatrixSubmodule κ ι F) : ℕ :=
  sInf { d : ℕ | ∃ U ∈ IC, ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ IC` is the min distance of an interleaved code `IC`.
-/
notation "Δ" IC => minDist IC

/--
The distance from a `κ x ι` matrix `U` to the closest word in a `κ`-interleaved code `IC`.
-/
def distToCode (U : Matrix (Fin κ) (Fin ι) F) (IC : MatrixSubmodule κ ι F) : ℕ :=
 sInf { d : ℕ | ∃ V ∈ IC, distCodewords U V = d }

/--
`Δ(U,C')` denotes distance between a `κ x ι` matrix `U` and `κ`-interleaved code `IC`.
-/
notation "Δ(" U "," IC ")" => distToCode U IC

lemma minDistL_eq_minDist {IC : LawfulInterleavedCode κ ι F} :
  LinearCodes.minDist IC.1.LC = minDist IC.1.MF := by sorry

end InterleavedCodes

noncomputable section

open InterleavedCodes

variable {F : Type*} [Field F] [Finite F]

local instance : Fintype F := Fintype.ofFinite F

/--
Lemma 4.3 Ligero
-/
lemma distInterleavedCodeToCodeLB
  {IC : LawfulInterleavedCode κ ι F} {U : Matrix (Fin κ) (Fin ι) F} {e : ℕ}
  (hF: Fintype.card F ≥ e)
  (he : (e : ℚ) ≤ (codeDist (IC.1.LC : Set (Fin ι → F)) / 3)) (hU : e < Δ(U,IC.1.MF)) :
  ∃ v ∈ Matrices.rowSpan U , e < distFromCode v IC.1.LC := sorry

namespace ProximityToRS

/--
The set of points on an affine line between `u` and `v`, which are within distance `e`
from an RS code of degree less than `deg` and and evaluation points `α`.
-/
def closePtsOnAffineLine (u v : Fin ι → F) (deg : ℕ) (α : Fin ι ↪ F) (e : ℕ) : Set (Fin ι → F) :=
  {x : Fin _ → F | x ∈ Affine.line u v ∧ distFromCode x (ReedSolomon.code α deg) ≤ e}

/--
The number of points on an affine line between `u` and `v`, which are within distance `e`
from an RS code of degree less than `deg` and and evaluation points `α`.
-/
def numberOfClosePts (u v : Fin ι → F) (deg : ℕ) (α : Fin ι ↪ F)
  (e : ℕ) : ℕ :=
  Fintype.card (closePtsOnAffineLine u v deg α e)

/--
Lemma 4.4 Ligero
Remark: Below, can use (ReedSolomonCode.minDist deg α) instead of ι - deg + 1 once proved
-/
lemma e_leq_dist_over_3 {deg : ℕ} {α : Fin ι ↪ F} {e : ℕ} {u v : Fin ι → F}
  (he : (e : ℚ) < (ι - deg + 1 / 3)) :
  ∀ x ∈ Affine.line u v, distFromCode x (ReedSolomon.code α deg) ≤ e
  ∨ (numberOfClosePts u v deg α e) ≤ ι - deg + 1 := by sorry

/--
Lemma 4.5 Ligero
-/
lemma probOfBadPts {deg : ℕ} {α : Fin ι ↪ F} {e : ℕ} {U : Matrix (Fin κ) (Fin ι) F}
  (he : (e : ℚ) < (ι - deg + 1 / 3))
  (hU : e < Δ(U, matrixSubmoduleOfLinearCode κ (ReedSolomon.code α deg))) :
  (PMF.uniformOfFintype (Matrices.rowSpan U)).toOuterMeasure
    { w | distFromCode (n := Fin ι) (R := F) w (ReedSolomon.code α deg) ≤ e }
  ≤ (ι - deg + 1)/(Fintype.card F) := by
  sorry

end ProximityToRS
end
