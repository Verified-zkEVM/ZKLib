/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši
-/

import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.RowCol
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Lie.OfAssociative

open Classical

noncomputable section

variable {F : Type*} [Semiring F]
variable {κ ι : ℕ}

namespace Affine

/--
affine line between vectors `u` and `v`.
-/
def line [Ring F] (u v : Fin ι → F) : Set (Fin ι → F) :=
  {x | ∃ γ : F, x = γ • u + (1 - γ) • v}

end Affine

namespace Matrices

/--
the submodule spanned by the rows of an `κ x ι` matrix `U`.
-/
def rowSpan (U : Matrix (Fin κ) (Fin ι) F) : Submodule F (Fin ι → F) :=
  Submodule.span F {U i | i : Fin κ}

/--
the set of indices of columns where matrices `U` and `V` differ.
-/
def neqCols (U V : Matrix (Fin κ) (Fin ι) F) : Finset (Fin ι) :=
  {j | ∃ i : (Fin κ), V i j ≠ U i j}

end Matrices
