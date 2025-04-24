/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic

/-!
  # Trivial Commitment Schemes

  We describe the simplest (oracle) commitment schemes, where the prover sends the data directly,
  and the verifier enforces any necessary checks on the data (e.g. degree bounds).
-/

/- The trivial PCS for bounded-degree univariate polynomials where the prover sends the
  polynomial directly, and the verifier checks the degree bound. -/
