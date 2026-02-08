import ProjSeminorm.WithBidual
import Mathlib.Analysis.RCLike.Basic

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
