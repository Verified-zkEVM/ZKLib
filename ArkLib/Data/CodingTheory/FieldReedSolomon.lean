/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.RelativeHammingDistance

section FieldRSC

open Polynomial Finset ReedSolomon LinearMap

variable {F : Type*} [Field F]
         {ι : Type*}  [Fintype ι] [DecidableEq ι] -- actually ι is the domain
         {domain : ι ↪ F}  -- domain is the set of word, where codes are a subset
         {deg : ℕ}

/-- The linear map that maps functions `f: ι→ F` to degree < |ι| polynomials p,
    such that p(x) = f(x) for all x ∈ ι -/
private noncomputable def interpolate : (ι → F) →ₗ[F] F[X] :=
  Lagrange.interpolate univ domain

/-- The linear map that maps a Reed Solomon code to its associated polynomial -/
noncomputable def decode: (code F ι domain deg) →ₗ[F] F[X] :=
    domRestrict (interpolate (domain := domain)) (code F ι domain deg)

/- Reed Solomon codes are decoded into degree < deg polynomials-/
lemma decoded_polynomial_lt_deg (c : code F ι domain deg) :
  decode c ∈ (degreeLT F deg : Submodule F F[X]) := by sorry

/-- The linear map that maps a Reed Solomon code to its associated polynomial
    of degree < deg -/
noncomputable def decodeLT : (code F ι domain deg) →ₗ[F] (Polynomial.degreeLT F deg) :=
  LinearMap.codRestrict
    (Polynomial.degreeLT F deg)
    decode
    (fun c => decoded_polynomial_lt_deg c)

-- Should be in LinearCodes.lean
noncomputable def rate (_c : code F ι domain deg) : ℝ := deg / (Fintype.card ι)


-- TODO: This should be in ReedSolomon.lean
-- Nethermind provided conflicting definitions for LinarCodes
-- This is for the one in ArkLib.Data.CodingTheory.RelativeHammingDistance
def toLinearCode (_cw : code F ι domain deg) : LinearCode ι F :=
  code F ι domain deg


variable (cw : code F ι domain deg)
#check decode cw
#check decodeLT cw
#check rate cw
#check toLinearCode cw

end FieldRSC
