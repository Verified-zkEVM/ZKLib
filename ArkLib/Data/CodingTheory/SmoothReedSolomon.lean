/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/
import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.SmoothDomain
import ArkLib.Data.MvPolynomial.LinearMvExtension

section SmoothRSC

/-! Smooth Reed Solomon Codes are Reed Solomon Codes defined over Smooth Domains.
    Their decoded associated univariate polynomial can be translated into
    a degree wise linear multivariate polynomial -/

open ReedSolomon SmoothIndex LinearMvExtension

variable {F : Type*} [Field F]
         {m : ℕ} -- Smooth RSC deg = 2^m
         {ι : Finset F} [Smooth ι m] [DecidableEq ι] -- Actual Smooth domain
         {domain : ι ↪ F}  -- domain is the set of word, where codes are a subset

/-- The linear map that maps Smooth Reed Solomon Code words with domain size 2^m
    to their associated degree wise linear m-variate polynomial  -/
noncomputable def mVdecode: (code F ι domain (2^m)) →ₗ[F] MvPolynomial (Fin m) F :=
  linearMvExtension.comp decodeLT

-- Test
variable (cw : code F ι domain (2^m))
#check mVdecode cw

end SmoothRSC
