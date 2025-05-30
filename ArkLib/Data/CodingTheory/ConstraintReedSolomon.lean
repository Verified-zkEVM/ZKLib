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
    polynomial satisfies the weight constraint for given `w` and `σ`.

    The following definition returns a subset of smooth ReedSolomon codes
    satisfying the weight constraint. This version can be used when we require
    the decoded multivariate polynomial from an underlying smooth codeword.-/

def constraintCodesetSC
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Finset F) [DecidableEq ι]
  (domain : ι ↪ F)
  (k : ℕ) [Smooth domain k]
  (m : ℕ)
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F):=
    {sc : smoothCode F ι domain k m | weightConstraint  (mVdecode sc) w σ}

/--Alternatively, the following definition returns a Set (ι -> F). -/

def constraintCode
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Finset F) [DecidableEq ι]
  (domain : ι ↪ F)
  (k m : ℕ) [Smooth domain k]
  (w : MvPolynomial (Fin (m+1)) F)
  (σ : F)
  : Set (ι → F) :=
    { f | ∃ (h : f ∈ smoothCode F ι domain k m),
      weightConstraint (mVdecode (⟨f, h⟩ : smoothCode F ι domain k m)) w σ }


namespace ConstraintReedSolomon

variable  {F : Type*} [Field F] [DecidableEq F]
          {ι : Finset F} [DecidableEq ι]
          {domain : ι ↪ F}
          {k : ℕ} [Smooth domain k]
          {m : ℕ}
          {w : MvPolynomial (Fin (m+1)) F}
          {σ : F}

/-- Forget the weight constrain. -/
noncomputable def toSmoothCode
  (cc : constraintCodesetSC F ι domain k m w σ) : smoothCode F ι domain k m :=
    cc.val

section --Test

variable  (F : Type*) [Field F] [DecidableEq F]
          (ι : Finset F) [DecidableEq ι]
          (domain : ι ↪ F)
          (k : ℕ) [Smooth domain k]
          (m : ℕ)
          (w : MvPolynomial (Fin (m+1)) F)
          (σ : F)
          (cc : constraintCodesetSC F ι domain k m w σ)


#check constraintCodesetSC F ι domain k m w σ
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
  (ι : Finset F) [DecidableEq ι]
  (domain : ι ↪ F)
  (k : ℕ) [Smooth domain k]
  (m : ℕ)
  (t : ℕ)
  (w : Fin t → MvPolynomial (Fin (m+1)) F)
  (σ : Fin t → F) :
  Set (smoothCode F ι domain k m) :=
    { sc | ∀ i : Fin t, weightConstraint (mVdecode sc) (w i) (σ i) }

/--Alternatively, the following definition returns a Set (ι -> F). -/
def multiConstraintCode
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Finset F) [DecidableEq ι]
  (domain : ι ↪ F)
  (k : ℕ) [Smooth domain k]
  (m : ℕ)
  (t : ℕ)
  (w : Fin t → MvPolynomial (Fin (m+1)) F)
  (σ : Fin t → F) :
  Set (ι → F) :=
    { f |
      ∃ (h : f ∈ smoothCode F ι domain k m),
        ∀ i : Fin t, weightConstraint (mVdecode (⟨f, h⟩ : smoothCode F ι domain k m)) (w i) (σ i)}



namespace MultiConstraintReedSolomon

variable  {F : Type*} [Field F] [DecidableEq F]
          {ι : Finset F} [DecidableEq ι]
          {domain : ι ↪ F}
          {k : ℕ} [Smooth domain k]
          {m : ℕ}
          {t : ℕ}
          {w : Fin t → MvPolynomial (Fin (m+1)) F}
          {σ : Fin t → F}

/-- Forget all weight constraints. -/
noncomputable def toSmoothCode
  (cc : multiConstraintCodesetSC F ι domain k m t w σ) : smoothCode F ι domain k m :=
    cc.val

section

variable  (F : Type*) [Field F] [DecidableEq F]
          (ι : Finset F) [DecidableEq ι]
          (domain : ι ↪ F)
          (k : ℕ) [Smooth domain k]
          (m : ℕ)
          (t : ℕ)
          (w : Fin t → MvPolynomial (Fin (m+1)) F)
          (σ : Fin t → F)
          (mcc : multiConstraintCodesetSC F ι domain k m t w σ)

#check multiConstraintCode F ι domain k m t w σ
#check mcc
#check mVdecode (toSmoothCode mcc)

end

end MultiConstraintReedSolomon


end ReedSolomon
