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

/-- The linear map that maps functions `f: ι→ F` to degree < n polynomials p,
    such that p(x) = f(x) for all x ∈ ι -/
noncomputable def interpolate: (ι→ F) →ₗ[F] F[X] :=
  Lagrange.interpolate univ domain

-- TODO: make this
--   (code F ι domain deg) →ₗ[F]  Polynomial.degreeLT F deg
/-- The linear map that maps Reed Solomon Code words to their associated
   < deg degree polynomials -/
noncomputable def decode: (code F ι domain deg) →ₗ[F] F[X] :=
    domRestrict (interpolate (domain := domain)) (code F ι domain deg)

/-- the decoded degree < deg polynomial of a Reed Solomon code `c` -/
noncomputable def decoded
  (c : code F ι domain deg) : F[X] :=
    decode.toFun c

-- Should be in LinearCodes.lean
noncomputable def rate (_C : code F ι domain deg) : ℝ := deg / (Fintype.card ι)


-- TODO: This should be in ReedSolomon.lean
-- Nethermind provided conflicting definitions for LinarCodes
-- This is for the one in ArkLib.Data.CodingTheory.RelativeHammingDistance
def toLinearCode : LinearCode ι F :=
  code F ι domain deg

end FieldRSC
