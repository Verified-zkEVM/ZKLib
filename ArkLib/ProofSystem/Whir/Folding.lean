/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Least Authority
-/

import ArkLib.Data.CodingTheory.SmoothDomain
import ArkLib.Data.CodingTheory.SmoothReedSolomon

namespace Fold

open SmoothDomain

noncomputable def Fold
  {F : Type*} [Field F] [DecidableEq F]
  {ι : Finset F} [DecidableEq ι]
  (f : ι → F) (α : F) : indexPow ι 2 → F := sorry

/-
Blueprint:

\begin{definition}[4.14]
Let $f\colon \mathcal{L}\to F$ be a function and $\alpha\in F$.  We define
\[
  \Fold(f,\alpha)\colon \mathcal{L}^{(2)}\to F
  \quad\text{by}\quad
  \forall x\in \mathcal{L},\;
  \Fold(f,\alpha)(x^2)
  := \frac{f(x)+f(-x)}{2}
     + \alpha \,\frac{f(x)-f(-x)}{2\,x}.
\]
\end{definition}

-/

end Fold
