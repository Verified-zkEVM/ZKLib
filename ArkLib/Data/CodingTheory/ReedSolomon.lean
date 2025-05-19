/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.FinEnum

/-!
  # Reed-Solomon Codes

  TODO: define the Reed-Solomon code, and prove its properties.

  TODO: define the Berkelamp-Welch algorithm for unique decoding, and Guruswami-Sudan algorithm for
  list-decoding.
-/


namespace ReedSolomon

open Polynomial

variable (F : Type*) [Semiring F] (ι : Type*) (domain : ι ↪ F)

/-- The evaluation of a polynomial at a set of points specified by `domain : ι ↪ F`, as a linear
  map. -/
def evalOnPoints : F[X] →ₗ[F] (ι → F) where
  toFun := fun p => fun x => p.eval (domain x)
  map_add' := fun x y => by simp; congr
  map_smul' := fun m x => by simp; congr

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.
  -/
def code (deg : ℕ) : Submodule F (ι → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints F ι domain)

/-- The generator matrix of the Reed-Solomon code of degree `deg` and evaluation points `domain`. -/
def genMatrix (deg : ℕ) : Matrix (Fin deg) ι F :=
  .of (fun i j => domain j ^ (i : ℕ))

/-- The (parity)-check matrix of the Reed-Solomon code, assuming `ι` is finite. -/
def checkMatrix (deg : ℕ) [Fintype ι] : Matrix (Fin (Fintype.card ι - deg)) ι F :=
  sorry

-- theorem code_by_genMatrix (deg : ℕ) :
--     code deg = codeByGenMatrix (genMatrix deg) := by
--   simp [codeByGenMatrix, code]
--   rw [LinearMap.range_eq_map]
--   sorry

end ReedSolomon
