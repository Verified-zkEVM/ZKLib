/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Logic.Equiv.Defs

def finUInt8Equiv : Fin (2 ^ 8) ≃ UInt8 where
  toFun := fun i => UInt8.ofFin i
  invFun := fun u => u.toFin
  left_inv _ := rfl
  right_inv _ := rfl

def finUInt16Equiv : Fin (2 ^ 16) ≃ UInt16 where
  toFun := fun i => UInt16.ofFin i
  invFun := fun u => u.toFin
  left_inv _ := rfl
  right_inv _ := rfl

def finUInt32Equiv : Fin (2 ^ 32) ≃ UInt32 where
  toFun := fun i => UInt32.ofFin i
  invFun := fun u => u.toFin
  left_inv _ := rfl
  right_inv _ := rfl

def finUInt64Equiv : Fin (2 ^ 64) ≃ UInt64 where
  toFun := fun i => UInt64.ofFin i
  invFun := fun u => u.toFin
  left_inv _ := rfl
  right_inv _ := rfl

def finBitVecEquiv {n : ℕ} : Fin (2 ^ n) ≃ BitVec n where
  toFun := fun i => BitVec.ofFin i
  invFun := fun u => u.toFin
  left_inv _ := rfl
  right_inv _ := rfl
