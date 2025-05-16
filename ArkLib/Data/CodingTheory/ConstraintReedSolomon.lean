/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.SmoothReedSolomon

namespace ReedSolomon


open ReedSolomon SmoothDomain Finset

-- TODO: There are hypercubes already in ArkLib. Use them

/-- The boolens `{0,1}` sitting inside any field `F`. -/
private def boolF {F : Type*} [Field F] [DecidableEq F] : Finset F := {0, 1}

/-- The binary `m`‐dimensional cube `{0,1}^m` as a `Finset (Fin m → F)`. -/
private def hypercube
  {F : Type*} [Field F] [DecidableEq F]
  {m : ℕ}: Finset (Fin m → F) := Fintype.piFinset fun _ => boolF

/-- Auxiliary function to assign values to the weight polynomial variables:
    index `0` ↦ `p.eval b`, index `j+1` ↦ `b j`. -/
private def toWeightAssignment
  {F : Type*} [Field F]
  {m : ℕ}
  (p : MvPolynomial (Fin m) F)
  (b : Fin m → F) : Fin (m+1) → F
    | ⟨0, _⟩       => MvPolynomial.eval b p
    | ⟨j+1, hj⟩   => b ⟨j, by simpa using hj⟩

/-- constraint is true, if ∑_{b ∈ {0,1}^m} w(f(b),b) = σ for given
    m-variate polynomial `f`and `(m+1)`-variate polynomial `w`-/
def weightConstraint
  {F : Type*} [Field F] [DecidableEq F]
  {m : ℕ}
  (f : MvPolynomial (Fin m) F)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F): Prop :=
    ∑ b ∈  hypercube , w.eval (toWeightAssignment f b) = σ

/-- Constraint Reed Solomon codes are smooth codes who's decoded m-variate
    polynomial satisfies the weight constraint for given `w` and `σ`. -/
def constraintCode
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Finset F) [DecidableEq ι]
  (domain : ι ↪ F)
  (k : ℕ) [Smooth domain k]
  (m : ℕ)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F):=
    {sc : smoothCode F ι domain k m | weightConstraint  (mVdecode sc) w σ}


section ConstraintReedSolomon

variable  {F : Type*} [Field F] [DecidableEq F]
          {ι : Finset F} [DecidableEq ι]
          {domain : ι ↪ F}
          {k : ℕ} [Smooth domain k]
          {m : ℕ}
          {w : MvPolynomial (Fin (m+1)) F}
          {σ : F}

/-- Forget the weight constrain. -/
noncomputable def toSmoothCode
  (cc : constraintCode F ι domain k m w σ) : smoothCode F ι domain k m :=
    cc.val

section --Test

variable  (F : Type*) [Field F] [DecidableEq F]
          (ι : Finset F) [DecidableEq ι]
          (domain : ι ↪ F)
          (k : ℕ) [Smooth domain k]
          (m : ℕ)
          (w : MvPolynomial (Fin (m+1)) F)
          (σ : F)
          (cc : constraintCode F ι domain k m w σ)

#check constraintCode F ι domain k m w σ
#check cc
#check mVdecode (toSmoothCode cc)

end

end ConstraintReedSolomon

end ReedSolomon
