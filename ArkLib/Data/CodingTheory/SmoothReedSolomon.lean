/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/
import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.CodingTheory.SmoothDomain
import ArkLib.Data.MvPolynomial.LinearMvExtension

namespace ReedSolomon

open ReedSolomon SmoothDomain LinearMvExtension

/-- Smooth Reed Solomon Codes are Reed Solomon Codes defined over Smooth Domains, such that
    their decoded univariate polynomials are of degree < 2ᵐ for some m ∈ ℕ. -/
def smoothCode
  (F : Type*) [Field F]
  (ι : Finset F) [DecidableEq ι]
  (domain : ι ↪ F)
  (k : ℕ) [Smooth domain k]
  (m : ℕ): Submodule F (ι → F) :=
    code F ι domain (2^m)

section SmoothRSC

variable {F : Type*} [Field F]
          {ι : Finset F} [DecidableEq ι]
          {domain : ι ↪ F}
          {k : ℕ} [Smooth domain k]
          {m : ℕ}

/-- The linear map that maps Smooth Reed Solomon Code words
    to their decoded degree wise linear `m`-variate polynomial  -/
noncomputable def mVdecode : (smoothCode F ι domain k m) →ₗ[F] MvPolynomial (Fin m) F :=
  linearMvExtension.comp decodeLT

section -- Test

variable (F : Type*) [Field F] (ι : Finset F) [DecidableEq ι]
         (domain : ι ↪ F) (k : ℕ) [Smooth domain k]
         (m : ℕ)
         (c : code F ι domain m)
         (sc : smoothCode F ι domain k m)

#check c
#check sc
#check mVdecode sc

end

end SmoothRSC

end ReedSolomon
