/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Projective Seminorm Multiplicativity — Basic Setup

Common imports, notation, and variable declarations for the projective seminorm
multiplicativity project. All other files in `ProjSeminorm/` import this module.
-/

open scoped TensorProduct BigOperators

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

end ProjSeminorm
