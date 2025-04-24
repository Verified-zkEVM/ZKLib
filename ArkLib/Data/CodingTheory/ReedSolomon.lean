/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
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

variable {F : Type*} [Field F] [Fintype F] {n : ℕ} (domain : Fin n ↪ F)

def evalOnPoints : F[X] →ₗ[F] (Fin n → F) where
  toFun := fun p => fun x => p.eval (domain x)
  map_add' := fun x y => by simp; congr
  map_smul' := fun m x => by simp; congr

/-- The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `points`.
  -/
def code (deg : ℕ) : Submodule F (Fin n → F) :=
  (Polynomial.degreeLT F deg).map (evalOnPoints domain)

/-- The generator matrix of the Reed-Solomon code of degree `deg` and evaluation points `points`. -/
def genMatrix (deg : ℕ) : Matrix (Fin deg) (Fin n) F :=
  .of (fun i j => domain j ^ (i : ℕ))

def checkMatrix (deg : ℕ) : Matrix (Fin (n - deg)) (Fin n) F :=
  sorry

-- theorem code_by_genMatrix (deg : ℕ) :
--     code deg = codeByGenMatrix (genMatrix deg) := by
--   simp [codeByGenMatrix, code]
--   rw [LinearMap.range_eq_map]
--   sorry

#check LinearMap.range_eq_map

#check Basis

#check Matrix.vandermonde

end ReedSolomon
