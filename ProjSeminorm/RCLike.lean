/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import ProjSeminorm.WithBidual
import Mathlib.Analysis.RCLike.Basic

/-!
# Unconditional Projective Seminorm Multiplicativity over ℝ and ℂ

For `RCLike` fields (ℝ, ℂ), the projective seminorm is unconditionally multiplicative
on pure tensors. The `h_bidual` hypothesis from `projectiveSeminorm_tprod_of_bidual_iso`
is discharged automatically because the Hahn-Banach theorem guarantees isometric bidual
embedding (via `inclusionInDoubleDualLi`).

## Main statements

- `projectiveSeminorm_tprod`: `π(⨂ₜ m_i) = ∏ ‖m_i‖` unconditionally over ℝ/ℂ.

## Implementation notes

The `NormedAddCommGroup` constraint (rather than `SeminormedAddCommGroup`) is required
because `inclusionInDoubleDualLi` is only available for normed spaces.
-/

open scoped TensorProduct BigOperators
open PiTensorProduct NormedSpace

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- Over ℝ or ℂ, the projective seminorm is unconditionally multiplicative on pure tensors. -/
theorem projectiveSeminorm_tprod (m : Π i, E i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_of_bidual_iso m
    (fun i => (inclusionInDoubleDualLi 𝕜).norm_map (m i))

end ProjSeminorm
