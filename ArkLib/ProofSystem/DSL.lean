import Mathlib.FieldTheory.Finite.Basic

/-!
  # Experimental development of a DSL for specifying vector / polynomial-based IORs
-/

#check Lean.Expr

namespace DSL

variable (F : Type*) [Field F] [Fintype F]

-- literals
inductive Lit where
  | scalar (val : F)
  -- perhaps it's enough to represent polynomials (we mostly care about either univariate or
  -- multilinear) by their vector of coefficients
  | vector (len : Nat) (v : Fin len → F)

-- arithmetic operations
inductive ScalarOp where | add | sub | mul | div

inductive ScalarVectorOp where | scale

inductive VectorOp where | dotProd

inductive Expr where
  | lit (a : Lit F)
  | var (name : String)
  | sOp (op : ScalarOp) (a : Lit F) (b : Lit F)
  | svOp (op : ScalarVectorOp) (a : Lit F) (v : Lit F)
  | vOp (op : VectorOp) (v1 : Lit F) (v2 : Lit F)

inductive Program where

-- inductive Ops where
--   | arith (op : Arith) {aVal : F} {bVal : F} (a : Lit.scalar aVal) (b : Lit.scalar bVal)
--   | scale (a : Lit.scalar) (v : Lit.vector)
--   | dotProd (v1 : Lit.vector n v₁) (v2 : Lit.vector n v₂)
-- example {a b : F} : Ops.arith .add a b = a := rfl

-- Important: what operations should we allow

-- ops on F
-- getting scalars out of a vector
-- scaling a vector by a scalar
-- taking inner product of vectors


end DSL
