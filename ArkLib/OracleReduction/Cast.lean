/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.Basic

/-!
  # Casting for structures of oracle reductions

  We define custom dependent casts (registered as `DepCast` instances) for the following structures:
  - `ProtocolSpec`
  - `(Full)Transcript`
  - `(Oracle)Prover`
  - `(Oracle)Verifier`
  - `(Oracle)Reduction`
-/
