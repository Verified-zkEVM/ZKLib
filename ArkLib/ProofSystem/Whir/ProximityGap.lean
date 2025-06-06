/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.ProofSystem.Whir.ProximityGen
import ArkLib.Data.CodingTheory.SmoothReedSolomon
namespace RSGenerator

open ReedSolomon Generator SmoothDomain NNReal

/- Theorem 4.8 [BCIKS20] Proxmity Gap Theorem
  Smooth Reed Solomon codes C:= RSC[F,L,m] have proximity generators for any given `l : ℕ`
   with generator function Gen(l) : 𝔽 → 𝔽ˡ ; α → (1,α, α², …, αˡ⁻¹),
   Bstar(C,l):= √ρ
   err(C,l,δ) :=  (l-1)2ᵐ / ρ • |F| for δ in (0, (1-ρ)/ 2]
                  (l-1) • 2²ᵐ / (|F|(2 min{1-√ρ-δ, √ρ/20})⁷) for δ in ((1-ρ)/ 2, 1 - B(C,l)) -/
noncomputable def proximityGapTheorem
  {F : Type*} [Field F]  [Fintype F] [DecidableEq F]
  {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  (l : ℕ) (φ : ι ↪ F) [Smooth φ] (m : ℕ)
  : ProximityGenerator ι F :=
    let ρ : ℝ≥0 := (2^m : ℝ≥0) / (Fintype.card ι)
    { C      := smoothCode F ι φ m,
      l      := l,
      GenFun := fun r j => r ^ (j : ℕ),
      B  := fun _ _ => NNReal.sqrt ρ ,
      err    := fun _ _ δ => (
        if δ ≤ (1 - ρ) / 2 then
          ((l- 1) * 2^m) / (ρ  * Fintype.card F )
        else
          let min_val := min (1 - (NNReal.sqrt ρ) - δ ) ((NNReal.sqrt ρ) / 20)
          ((l - 1) * (2^(2 • m))) / ((Fintype.card F) • (2 • min_val)^7)
      ),
      proximity := by sorry
    }

end RSGenerator
