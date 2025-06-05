/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.FieldReedSolomon
import ArkLib.Data.MvPolynomial.LinearMvExtension

namespace SmoothDomain
variable {F: Type*} [Semiring F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- A domain `ι ↪ F` is `smooth`, if `ι ⊆ F`, `|ι| = 2^k` for some `k` and
    there exists a subgroup `H` in the group of units `Rˣ`
    and an invertible element `a ∈ R` such that `ι = a • H` -/
class Smooth
  [DecidableEq ι]
  (domain : ι ↪ F) where
    H           : Subgroup (Units F)
    a           : Units F
    h_coset     : Finset.image domain Finset.univ
                  = (fun h : Units F => (a : F) * (h : F)) '' (H : Set (Units F))
    h_card_pow2 : ∃ k : ℕ, Fintype.card ι = 2 ^ k

end SmoothDomain
namespace ReedSolomon

open LinearMvExtension ReedSolomon SmoothDomain
variable  {F : Type*} [Field F] [DecidableEq F]
          {ι : Type*} [Fintype ι] [DecidableEq ι]
          {domain : ι ↪ F} [Smooth domain]
          {m : ℕ}

/-- Smooth Reed Solomon Codes are Reed Solomon Codes defined over Smooth Domains, such that
    their decoded univariate polynomials are of degree < 2ᵐ for some m ∈ ℕ. -/
def smoothCode
  (F : Type*) [Field F] [DecidableEq F]
  (ι : Type*) [Fintype ι] [DecidableEq ι]
  (domain : ι ↪ F) [Smooth domain]
  (m : ℕ): Submodule F (ι → F) :=
    code F ι domain (2^m)

/-- The linear map that maps Smooth Reed Solomon Code words
    to their decoded degree wise linear `m`-variate polynomial  -/
noncomputable def mVdecode : (smoothCode F ι domain m) →ₗ[F] MvPolynomial (Fin m) F :=
  linearMvExtension.comp decodeLT

end ReedSolomon
