/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
  # Sequential Composition of Many Oracle Reductions

  This file defines the sequential composition of an arbitrary `m + 1` number of oracle reductions.
  This is defined by iterating the composition of two reductions, as defined in `Append.lean`.

  The security properties of the general sequential composition of reductions are then inherited
  from the case of composing two reductions.
-/

open ProtocolSpec

variable {ι : Type} [DecidableEq ι] {oSpec : OracleSpec ι}

section Instances

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

/-- If all protocols have sampleable challenges, then the challenges of their sequential
  composition also have sampleable challenges. -/
instance [h : ∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)] :
    ∀ j, Sampleable ((compose m n pSpec).Challenge j) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.compose, Fin.append, Fin.addCases, Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  sorry
  -- by_cases h' : i < m <;> simp [h'] at h ⊢
  -- · exact h₁ ⟨⟨i, by omega⟩, h⟩
  -- · exact h₂ ⟨⟨i - m, by omega⟩, h⟩

/-- If all protocols' messages have oracle interfaces, then the messages of their sequential
  composition also have oracle interfaces. -/
instance [O : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)] :
    ∀ i, OracleInterface ((compose m n pSpec).Message i) := fun ⟨⟨i, isLt⟩, h⟩ => by
  dsimp [ProtocolSpec.compose, ProtocolSpec.getDir, Fin.append, Fin.addCases,
    Fin.castLT, Fin.subNat, Fin.cast] at h ⊢
  sorry
  -- by_cases h' : i < m <;> simp [h'] at h ⊢
  -- · exact O₁ ⟨⟨i, by omega⟩, h⟩
  -- · exact O₂ ⟨⟨i - m, by omega⟩, h⟩

-- open OracleComp OracleSpec SubSpec

-- variable [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]

-- instance : SubSpec (challengeOracle pSpec₁ ++ₒ challengeOracle pSpec₂)
--     (challengeOracle (compose m n pSpec)) := sorry

end Instances

section Composition

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

def Prover.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    (P : (i : Fin (m + 1)) → Prover (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ)) :
      Prover (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
        (Wit (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Prover
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ))
    (fun i Pacc => by
      convert Prover.append Pacc (P i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using P 0)

def Verifier.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type)
    (V : (i : Fin (m + 1)) → Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ)) :
      Verifier (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Stmt (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Verifier
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Stmt i.succ))
    (fun i Vacc => by
      refine dcast₂ (self := instDepCast₂Verifier) ?_ ?_ (Vacc.append (V i.succ))
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using V 0)

def Reduction.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    (R : (i : Fin (m + 1)) → Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ)) :
      Reduction (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
        (Wit (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Reduction
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ))
    (fun i Racc => by
      convert Reduction.append Racc (R i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using R 0)

end Composition

section Security

open scoped NNReal

namespace Reduction

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]
    {Stmt : Fin (m + 2) → Type} {Wit : Fin (m + 2) → Type} {rel : ∀ i, Stmt i → Wit i → Prop}
    [oSpec.DecidableEq] [oSpec.FiniteRange]

theorem completeness_compose
    (R : ∀ i, Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ))
    (completenessError : Fin (m + 1) → ℝ≥0)
    (h : ∀ i, (R i).completeness (rel i.castSucc) (rel i.succ) (completenessError i)) :
      (Reduction.compose m n pSpec Stmt Wit R).completeness (rel 0) (rel (Fin.last (m + 1)))
        (∑ i, completenessError i) := by
  induction m with
  | zero =>
    simp_all; convert h 0; sorry
  | succ m ih =>
    sorry

end Reduction

end Security
