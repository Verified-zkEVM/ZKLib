/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.BigOperators.Fin

#check finFunctionFinEquiv

def finUInt8Equiv : Fin (2 ^ 8) ≃ UInt8 where
  toFun := fun i => UInt8.mk i
  invFun := fun u => u.val
  left_inv := fun i => by simp
  right_inv := fun u => by simp

def finUInt16Equiv : Fin (2 ^ 16) ≃ UInt16 where
  toFun := fun i => UInt16.mk i
  invFun := fun u => u.val
  left_inv := fun i => by simp
  right_inv := fun u => by simp

def finUInt32Equiv : Fin (2 ^ 32) ≃ UInt32 where
  toFun := fun i => UInt32.mk i
  invFun := fun u => u.val
  left_inv := fun i => by simp
  right_inv := fun u => by simp

def finUInt64Equiv : Fin (2 ^ 64) ≃ UInt64 where
  toFun := fun i => UInt64.mk i
  invFun := fun u => u.val
  left_inv := fun i => by simp
  right_inv := fun u => by simp

def finBitVecEquiv {n : ℕ} : Fin (2 ^ n) ≃ BitVec n where
  toFun := fun i => BitVec.ofFin i
  invFun := fun u => u.toFin
  left_inv := fun i => by simp
  right_inv := fun u => by simp
