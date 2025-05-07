/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
# Vector Interactive Oracle Reductions

We define vector interactive oracle reductions (V-IOR) and vector interactive oracle proofs
(V-IOPs), as special cases IORs/IOPs where all messages and oracle statements are vectors over some
alphabet. We also define their proximity versions, V-IORP and V-IOPP, which exhibit a gap between
the relation for completeness and the relation for soundness.

This is the original formulation of IOPs in [BCS16]. Many IOPs of interest in the literature are of
this form, and so we isolate this special case for ease of notation and reasoning.

We also define complexity measures for V-IORs, such as proof length and verifier's query complexity.

-/

namespace ProtocolSpec

/-- The protocol specification for a V-IOR, which consists of the direction of each message and its length.

(assumed to be working over a fixed alphabet) -/
def VectorSpec (n : ℕ) := Fin n → Direction × Nat

/-- The length of the `i`-th message in a `VectorSpec`. -/
def VectorSpec.length (vPSpec : VectorSpec n) (i : Fin n) : Nat := vPSpec i.2

/-- Convert a `VectorSpec` into a `ProtocolSpec` for a given alphabet type `A`.

The `i`-th message is a vector of length `vPSpec i.2` over `A`. -/
def VectorSpec.toProtocolSpec (A : Type) (vPSpec : VectorSpec n) : ProtocolSpec n :=
  fun i => ((vPSpec i).1, Fin (vPSpec i.2) → A)

instance {A : Type} {vPSpec : VectorSpec n} : OracleInterfaces (VectorSpec.toProtocolSpec vPSpec A) where
  oracleInterfaces := fun _ => instOracleInterfaceForallFin

end ProtocolSpec

/-- Vector Interactive Oracle Proofs of Proximity -/

This is a bundled structure where we define both the protocol and the guarantees of the protocol -/
structure VectorIOPP (n : ℕ) (vPSpec : ProtocolSpec.VectorSpec n) (oSpec : OracleSpec n) where
