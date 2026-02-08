import Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
import Mathlib.Topology.Order.IsLUB

/-!
# Norming Sequences for Operator Norms

Infrastructure for constructing sequences that achieve the operator norm.
These results are needed for the lower bound in the projective seminorm
multiplicativity proof. They are added by mathlib PR #33969 but not yet
in mainline mathlib.
-/

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The operator norm is the LUB of `‖f x‖ / ‖x‖`. -/
theorem isLUB_opNorm (f : E →L[𝕜] F) :
    IsLUB (Set.range fun x => ‖f x‖ / ‖x‖) ‖f‖ := by
  sorry

/-- There exists a sequence of elements whose norm ratios converge to the operator norm. -/
theorem exists_norming_sequence (f : E →L[𝕜] F) :
    ∃ u : ℕ → E, Tendsto (fun n => ‖f (u n)‖ / ‖u n‖) atTop (nhds ‖f‖) := by
  sorry

end ContinuousLinearMap
