/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative

noncomputable section

variable {F : Type*} [Semiring F]
variable {κ ι : ℕ}

namespace Affine

/--
Affine line between two vectors with coefficients in a semiring.
-/
def line [Ring F] (u v : Fin ι → F) : Set (Fin ι → F) :=
  {x | ∃ γ : F, x = γ • u + (1 - γ) • v}

end Affine

namespace Matrix

/--
The module spanned by the rows of a matrix.
-/
def rowSpan (U : Matrix (Fin κ) (Fin ι) F) : Submodule F (Fin ι → F) :=
  Submodule.span F {U i | i : Fin κ}

/--
The set of indices of non-equal columns of two matrices.
-/
def neqCols [DecidableEq F] (U V : Matrix (Fin κ) (Fin ι) F) : Finset (Fin ι) :=
  {j | ∃ i : (Fin κ), V i j ≠ U i j}

end Matrix
