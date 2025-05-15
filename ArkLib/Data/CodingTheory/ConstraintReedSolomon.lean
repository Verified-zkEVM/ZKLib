/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.SmoothReedSolomon

section ConstraintReedSolomon

open ReedSolomon SmoothIndex Finset

/-- The boolens `{0,1}` sitting inside any field `F`. -/
def boolF {F : Type*} [Field F] [DecidableEq F] : Finset F := {0, 1}

/-- The binary `m`‐dimensional cube `{0,1}^m` as a `Finset (Fin m → F)`. -/
def hypercube
  {F : Type*} [Field F] [DecidableEq F]
  {m : ℕ}: Finset (Fin m → F) := Fintype.piFinset fun _ => boolF

/-- Auxiliary function to assign values to the weight polynomial variables:
    index `0` ↦ `p.eval b`, index `j+1` ↦ `b j`. -/
private def toWeightAssignment
  {F : Type*} [Field F] [DecidableEq F]
  {m : ℕ}
  (p : MvPolynomial (Fin m) F)
  (b : Fin m → F) : Fin (m+1) → F
    | ⟨0, _⟩       => MvPolynomial.eval b p
    | ⟨j+1, hj⟩   => b ⟨j, by simpa using hj⟩

/-- constraint is true, if ∑_{b ∈ {0,1}^m} w(f(b),b) = σ for given
    m-variate polynomial `f`and (m+1)-variate polynomial `w`-/
def constraint
  {F : Type*} [Field F] [DecidableEq F]
  {m : ℕ}
  (f : MvPolynomial (Fin m) F)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F): Prop :=
    ∑ b ∈  hypercube , w.eval (toWeightAssignment f b) = σ

/-- All the RS‐codewords of degree `< deg` that satisfy the weight‐constraint `w, σ`. -/
def constraintCode
  (m : ℕ )
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Finset F) [Smooth ι m] [DecidableEq ι]
  (domain : ι ↪ F) [DecidableEq (ι ↪ F)]
  (deg : ℕ)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F) :=
    {c : code F ι domain deg // constraint  (mVdecode c) w σ}

namespace ConstraintCode

variable
         (m: ℕ)
         (F : Type*) [Field F] [DecidableEq F]
        (ι : Finset F) [Smooth ι m] [DecidableEq ι]
        (domain : ι ↪ F) [DecidableEq (ι ↪ F)]
        (deg : ℕ)
         (w : MvPolynomial (Fin (m+1)) F)
         (σ : F)

example (c : code F ι domain deg) : constraint (mVdecode c) w σ := sorry

#check constraintCode m F ι domain deg w σ

variable  (cw : constraintCode m F ι domain deg w σ)

end ConstraintCode

end ConstraintReedSolomon
