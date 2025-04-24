/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Matrix.Hadamard

/-!
# R1CS

This file defines the R1CS (Rank-1 Constraint System) relation. It also defines the sparse
representation of a matrix.

-/

namespace R1CS

open Matrix

variable (R : Type*) [CommSemiring R]

inductive MatrixIdx where | A | B | C deriving Inhabited, DecidableEq

structure Size where
  m : ℕ -- number of columns
  n_x : ℕ -- number of public variables
  n_w : ℕ -- number of witness variables

abbrev Size.n (sz : Size) : ℕ := sz.n_x + sz.n_w

def Statement (sz : Size) := Fin sz.n_x → R

def OracleStatement (sz : Size) := fun _ : MatrixIdx => Matrix (Fin sz.m) (Fin sz.n) R

def Witness (sz : Size) := Fin sz.n_w → R

-- The R1CS relation
def relation (sz : Size) :
    (Fin sz.n_x → R) → -- public input `x`
    (MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R) → -- matrices `A`, `B`, `C` as oracle inputs
    (Fin sz.n_w → R) → -- witness input `w`
    Prop :=
  fun stmt matrices wit =>
    let z : Fin (sz.n_x + sz.n_w) → R := Fin.append stmt wit
    (matrices .A *ᵥ z) * (matrices .B *ᵥ z) = (matrices .C *ᵥ z)

end R1CS

/-- The sparse representation of a matrix `m → n → α` consists of:
- The number of non-zero entries `k : ℕ`
- The row indices `row : Fin k → m`
- The column indices `col : Fin k → n`
- The values `val : Fin k → α`

This representation is **not** unique. In particular, we may have duplicate `(row, col)` pairs, and
some `val` may be zero.
-/
structure SparseMatrix (m n α : Type*) where
  numEntries : ℕ
  row : Fin numEntries → m
  col : Fin numEntries → n
  val : Fin numEntries → α
deriving Inhabited, DecidableEq

/-- Convert a sparse matrix to a regular (dense) matrix. For each entry `(i, j)` of the matrix, we
  simply sum over all `k` such that `(row k, col k) = (i, j)`.
-/
def SparseMatrix.toMatrix {m n α : Type*} [DecidableEq m] [DecidableEq n] [AddCommMonoid α]
    (A : SparseMatrix m n α) : Matrix m n α :=
  fun i j => ∑ k : Fin A.numEntries, if A.row k = i ∧ A.col k = j then A.val k else 0
