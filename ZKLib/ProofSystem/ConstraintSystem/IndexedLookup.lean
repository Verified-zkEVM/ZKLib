/-
Copyright (c) 2024 ZKLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ZKLib.CommitmentScheme.Basic

/-!
  # Lookup relations

  We define the basic lookup relation, plus the Lasso lookup relation with subtable decomposition.
-/

variable {R : Type}

-- def CommittedLookupRelation (cs : ListCommitmentScheme R) : Relation where
--   Statement := List cs.Datum × cs.Commitment
--   Witness := List cs.Datum × cs.Randomness
--   isValid := fun stmt wit => cs.commit (cs.hData ▸ wit.1) wit.2 = stmt.2 ∧ ∀ x ∈ wit.1, x ∈ stmt.1

-- def LookupRelation : Relation where
--   Statement := List R
--   Witness := List R
--   isValid := fun stmt wit => wit ⊆ stmt

-- def BatchedLookupRelation (n m : ℕ+) : Relation where
--   Statement := Fin n → List R
--   Witness := (Fin m → List R) × Matrix (Fin m) (Fin n) Bool
--   isValid := fun stmt wit =>
--     ∀ i : Fin m, ∀ j : Fin n,
--       if wit.2 i j then stmt j ⊆ wit.1 i else True

-- -- lookups where the lookup table is `decomposable` in some way (as in Lasso)
-- def DecomposableLookupRelation : Relation := sorry
