/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.ReedSolomon

namespace ReedSolomon

section FieldRSC

open Finset LinearMap Polynomial ReedSolomon

variable {F : Type*} [Field F]
         {ι : Type*}  [Fintype ι] [DecidableEq ι]
         {domain : ι ↪ F}
         {deg : ℕ}

/-- The linear map that maps a codeword `f : ι → F` to a degree < |ι| polynomial p,
    such that p(x) = f(x) for all x ∈ ι -/
private noncomputable def interpolate : (ι → F) →ₗ[F] F[X] :=
  Lagrange.interpolate univ domain

/-- The linear map that maps a ReedSolomon codeword to its associated polynomial -/
noncomputable def decode : (code domain deg) →ₗ[F] F[X] :=
  domRestrict
    (interpolate (domain := domain))
    (code domain deg)

/- ReedSolomon codewords are decoded into degree < deg polynomials-/
lemma decoded_polynomial_lt_deg (c : code domain deg) :
  decode c ∈ (degreeLT F deg : Submodule F F[X]) := by sorry

/-- The linear map that maps a Reed Solomon codeword to its associated polynomial
    of degree < deg -/
noncomputable def decodeLT : (code domain deg) →ₗ[F] (Polynomial.degreeLT F deg) :=
  codRestrict
    (Polynomial.degreeLT F deg)
    decode
    (fun c => decoded_polynomial_lt_deg c)

end FieldRSC

end ReedSolomon
