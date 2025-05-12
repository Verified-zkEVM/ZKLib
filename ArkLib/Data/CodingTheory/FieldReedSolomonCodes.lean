/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/
import ArkLib.Data.CodingTheory.ReedSolomon

section FieldRSC

open Polynomial Finset ReedSolomon LinearMap

variable {F : Type*} [Field F] {n : ℕ} {domain : Fin n ↪ F} {deg : ℕ}

/--  The linear map that maps F-valued vectors ( c(x₀),...,c(xₙ₋₁) ) to degree < n polynomials p,
    such that p(xᵢ) = c(xᵢ) for all i ∈ {0,..,n-1} -/
noncomputable def interpolate : (Fin n → F) →ₗ[F] F[X] :=
  Lagrange.interpolate univ domain

/-- The linear map that maps Reed Solomon Code words to their associated
   < deg degree polynomials -/
noncomputable def decode: (code domain deg) →ₗ[F] F[X] :=
    domRestrict (interpolate (domain := domain)) (code domain deg)

/-- the decoded degree < deg polynomial of a Reed Solomon code `c` -/
noncomputable def decoded
  (c : code domain deg) : F[X] :=
    decode.toFun c

-- Should be in SemiRing RSC
-- Could also use just deg / n
noncomputable def rate (_C : code domain deg) : ℝ := deg / (Fintype.card (Fin n) : ℝ)

-- Could also be in SemiRingRSC or in outOfDomainSampl.
/-- Complement of the domain in a finite field `F` i.e. `F\domain` as a Finset -/
def domainComplement [Fintype F] [DecidableEq F] (_C : code domain deg) : Finset F :=
  let domain_finset : Finset F := (univ : Finset (Fin n)).image domain
  Finset.univ \ domain_finset

end FieldRSC
