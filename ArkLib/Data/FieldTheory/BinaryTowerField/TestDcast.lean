import ArkLib.Data.Math.DepCast
import Mathlib.FieldTheory.Finite.GaloisField

example {k : ℕ} (h_pos : k > 0) (x : BitVec (2 ^ k)) :
  let h1 : 2 ^ k - 1 - 2 ^ (k - 1) + 1 = 2 ^ (k - 1) + 2 ^ (k - 1) - 1 - 2 ^ (k - 1) + 1 := by sorry
  let h2 : 2 ^ k = 2 ^ (k - 1) + 2 ^ (k - 1) := by sorry
  dcast h1 (BitVec.extractLsb (hi:=2 ^ k - 1) (lo:=2 ^ (k - 1)) x) = BitVec.extractLsb (hi:=2 ^ (k - 1) + 2 ^ (k - 1) - 1) (lo:=2 ^ (k - 1)) (dcast h2 x) := by
    -- How to subst/rw parameter hi of rhs from (2 ^ (k - 1) + 2 ^ (k - 1) - 1) to (2 ^ k - 1)?
  sorry
