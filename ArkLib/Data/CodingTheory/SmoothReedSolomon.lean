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
    Their decodes associated associated univariate polynomial can be translated into
    a degree wise linear multivariate polynomial -/

open Polynomial Finset ReedSolomon LinearMap SmoothIndex

variable {F : Type*} [Field F]
         {k : ℕ }
         {ι : Finset F} [Smooth ι k]
         {domain : ι ↪ F}  -- domain is the set of word, where codes are a subset
         {deg : ℕ}

/-- The linear map that maps Smooth Reed Solomon Code words with domain size 2^m
    to their associated degree wise linear m-variate polynomial  -/
noncomputable def mVdecode: (code F ι domain deg) →ₗ[F] F[X] := sorry
  TODO: THIS IS LinearMvExtension.linearMvExtension Circ code.decode


end SmoothRSC
