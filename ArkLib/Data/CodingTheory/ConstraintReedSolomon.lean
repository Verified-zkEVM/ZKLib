/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.SmoothReedSolomon

namespace ReedSolomon


open ReedSolomon SmoothDomain Finset

/-- Auxiliary function to assign values to the weight polynomial variables:
    index `0` ↦ `p.eval b`, index `j+1` ↦ `b j`. -/
private def toWeightAssignment
  {F : Type*} [Field F]
  {m : ℕ}
  (p : MvPolynomial (Fin m) F)
  (b : Fin m → Fin 2) : Fin (m+1) → F :=
    let b' : Fin m → F := fun i => ↑(b i : ℕ)
    Fin.cases (MvPolynomial.eval b' p)
              (fun i => ↑(b i : ℕ))


/-- constraint is true, if ∑_{b ∈ {0,1}^m} w(f(b),b) = σ for given
    m-variate polynomial `f`and `(m+1)`-variate polynomial `w`-/
def weightConstraint
  {F : Type*} [Field F] [DecidableEq F]
  {m : ℕ}
  (f : MvPolynomial (Fin m) F)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F): Prop :=
    ∑ b : Fin m → Fin 2 , w.eval (toWeightAssignment f b) = σ

/-- Constraint Reed Solomon codes are smooth codes who's decoded m-variate
    polynomial satisfies the weight constraint for given `w` and `σ`.

    The following definition returns a subset of smooth ReedSolomon codes
    satisfying the weight constraint. This version can be used when we require
    the decoded multivariate polynomial from an underlying smooth codeword.-/

def constraintCodesetSC
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Type*) [Fintype ι] [DecidableEq ι]
  (domain : ι ↪ F)
  [Smooth domain]
  (m : ℕ)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F):=
    {sc : smoothCode F ι domain m | weightConstraint  (mVdecode sc) w σ}

/--Alternatively, the following definition returns a Set (ι -> F). -/

def constraintCode
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Type*) [Fintype ι] [DecidableEq ι]
  (domain : ι ↪ F)
  (m : ℕ) [Smooth domain]
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F)
  : Set (ι → F) :=
    { f | ∃ (h : f ∈ smoothCode F ι domain m),
      weightConstraint (mVdecode (⟨f, h⟩ : smoothCode F ι domain m)) w σ }


namespace ConstraintReedSolomon

variable  {F : Type*} [Field F] [DecidableEq F]
          {ι : Finset F} [DecidableEq ι]
          {domain : ι ↪ F}
          [Smooth domain]
          {m : ℕ}
          {w : MvPolynomial (Fin (m+1)) F}
          {σ : F}

/-- Forget the weight constrain. -/
noncomputable def toSmoothCode
  (cc : constraintCodesetSC F ι domain m w σ) : smoothCode F ι domain m :=
    cc.val

section --Test

variable  (F : Type*) [Field F] [DecidableEq F]
          (ι : Finset F) [DecidableEq ι]
          (domain : ι ↪ F)
          [Smooth domain]
          (m : ℕ)
          (w : MvPolynomial (Fin (m+1)) F)
          (σ : F)
          (cc : constraintCodesetSC F ι domain m w σ)


#check constraintCodesetSC F ι domain m w σ
#check cc
#check mVdecode (toSmoothCode cc)

end

end ConstraintReedSolomon


/-- Multi-constraint Reed Solomon codes are smooth codes who's decoded m-variate
    polynomial satisfies the `t` weight constraints for given `w₀,...,wₜ₋₁` and
    `σ₀,...,σₜ₋₁`.

    The following definition returns a subset of smooth ReedSolomon codes
    satisfying the weight constraint. This version can be used when we require
    the decoded multivariate polynomial from an underlying smooth codeword.-/
def multiConstraintCodesetSC
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Type*) [Fintype ι] [DecidableEq ι]
  (domain : ι ↪ F)
  [Smooth domain]
  (m : ℕ)
  (t : ℕ)
  (w : Fin t → MvPolynomial (Fin (m+1)) F)
  (σ : Fin t → F) :
  Set (smoothCode F ι domain m) :=
    { sc | ∀ i : Fin t, weightConstraint (mVdecode sc) (w i) (σ i) }

/--Alternatively, the following definition returns a Set (ι -> F). -/
def multiConstraintCode
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Type*) [Fintype ι] [DecidableEq ι]
  (domain : ι ↪ F)
  [Smooth domain]
  (m : ℕ)
  (t : ℕ)
  (w : Fin t → MvPolynomial (Fin (m+1)) F)
  (σ : Fin t → F) :
  Set (ι → F) :=
    { f |
      ∃ (h : f ∈ smoothCode F ι domain m),
        ∀ i : Fin t, weightConstraint (mVdecode (⟨f, h⟩ : smoothCode F ι domain m)) (w i) (σ i)}



namespace MultiConstraintReedSolomon

variable  {F : Type*} [Field F] [DecidableEq F]
          {ι : Type*} [Fintype ι] [DecidableEq ι]
          {domain : ι ↪ F}
          [Smooth domain]
          {m : ℕ}
          {t : ℕ}
          {w : Fin t → MvPolynomial (Fin (m+1)) F}
          {σ : Fin t → F}

/-- Forget all weight constraints. -/
noncomputable def toSmoothCode
  (cc : multiConstraintCodesetSC F ι domain m t w σ) : smoothCode F ι domain m :=
    cc.val

section

variable  (F : Type*) [Field F] [DecidableEq F]
          {ι : Type*} [Fintype ι] [DecidableEq ι]
          (domain : ι ↪ F)
          [Smooth domain]
          (m : ℕ)
          (t : ℕ)
          (w : Fin t → MvPolynomial (Fin (m+1)) F)
          (σ : Fin t → F)
          (mcc : multiConstraintCodesetSC F ι domain m t w σ)

#check multiConstraintCode F ι domain m t w σ
#check mcc
#check mVdecode (toSmoothCode mcc)

end

end MultiConstraintReedSolomon


end ReedSolomon
