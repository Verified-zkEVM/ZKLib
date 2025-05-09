/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Data.Matrix.Rank
import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Submodule.Defs

/-!
  Definition of a linear code, minimal distance of a linear code, length, dimension and rate.
  Linear codes defined by a generator matrices and rephrase of dimension in this framework.
  Definition of the weight of a vector, statement and proof of the fact that the minimal
  distance of a linear code equals the minimal weight taken over the set of codewords.
-/

open Classical
open Finset

noncomputable section

variable {ι : ℕ}
         {F : Type*} [Semiring F]

abbrev LinearCode.{u} (ι : ℕ) (F : Type u) [Semiring F] : Type u := Submodule F (Fin ι → F)

def wt {F : Type*} [Semiring F] [Zero F] {ι : ℕ}
  (v : Fin ι → F) : ℕ := #{i | v i ≠ 0}

def LinearCode.minDist (LC : LinearCode ι F) : ℕ :=
  sInf { d | ∃ u ∈ LC, ∃ v ∈ LC, u ≠ v ∧ hammingDist u v = d }

end

namespace LinearCode

noncomputable section

variable {ι κ : ℕ}
         {F : Type*} [CommRing F]

/--
a linear code defined by left multiplication by its generator matrix.
-/
def mulByGenMat (G : Matrix (Fin ι) (Fin κ) F) : LinearCode ι F :=
  LinearMap.range G.mulVecLin

/--
A linear code defined by right multiplication by a generator matrix.
-/
def mulByGenMatTranspose (G : Matrix (Fin κ) (Fin ι) F) : LinearCode ι F :=
  LinearMap.range G.vecMulLinear


/--
Dimension of a linear code.
-/
def dim (LC : LinearCode ι F) : ℕ :=
  Module.finrank F LC

/--
The dimension of a linear code equals the rank of its associated generator matrix.
-/
lemma dimEqRankGenMat {G : Matrix (Fin κ) (Fin ι) F} :
  G.rank = dim (mulByGenMat G) := by
  rw[Matrix.rank, dim, mulByGenMat]

/--
Length of a linear code.
-/
def length (LC : LinearCode ι F) := Fintype.card (Fin ι)

/--
Rate of a linear code.
-/
def rate (LC : LinearCode ι F) : ℚ :=
  (dim LC : ℚ) / (length LC : ℚ)

/--
`ρ LC` is the rate of the linear code `LC`.
-/
notation "ρ" LC => rate LC

/--
The minimum taken over the weight of codewords in a linear code.
-/
def minWtCodewords (LC : LinearCode ι F) : ℕ :=
  sInf {w | ∃ c ∈ LC, c ≠ 0 ∧ wt c = w}

/--
The Hamming distance between codewords equals to the weight of their difference.
-/
lemma hammingDist_eq_wt_sub {u v : Fin ι → F} : hammingDist u v = wt (u - v) := by
  aesop (add simp [hammingDist, wt, sub_eq_zero])

/--
The min distance of a linear code equals to the minimum of the weights of non-zero codewords.
-/
lemma minDist_eq_minWtCodewords {LC : LinearCode ι F} : minDist LC = minWtCodewords LC := by
  unfold minDist minWtCodewords
  refine congrArg _ (Set.ext fun _ ↦ ⟨fun ⟨u, _, v, _⟩ ↦ ⟨u - v, ?p₁⟩, fun _ ↦ ⟨0, ?p₂⟩⟩) <;>
  aesop (add simp [hammingDist_eq_wt_sub, sub_eq_zero])

/--
Singleton Bound Theorem.
-/
theorem singletonBound (LC : LinearCode ι F) :
  dim LC ≤ length LC - minDist LC + 1 := by sorry

end
end LinearCode
