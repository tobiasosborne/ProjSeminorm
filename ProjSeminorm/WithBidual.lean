import ProjSeminorm.DualDistribL

/-!
# Projective Seminorm Multiplicativity with Bidual Hypothesis

The main theorem: the projective seminorm is multiplicative on pure tensors,
assuming each factor embeds isometrically into its bidual. This is Step 4
of the proof plan.

## Strategy

For the lower bound `∏ i, ‖m i‖ ≤ projectiveSeminorm (⨂ₜ[𝕜] i, m i)`:

1. For each `i`, use `h_bidual` to get `‖inclusionInDoubleDual (m i)‖ = ‖m i‖`,
   which means `sup_{‖f‖≤1} |f(m i)| = ‖m i‖`.
2. For any `f : Π i, StrongDual 𝕜 (E i)` with `‖f i‖ ≤ 1`:
   `|∏ i, f i (m i)| = |dualDistribL(⨂ f i)(⨂ m i)| ≤ ‖dualDistribL(⨂ f i)‖ · projSeminorm(⨂ m i)`
   and `‖dualDistribL(⨂ f i)‖ ≤ ∏ ‖f i‖ ≤ 1`.
3. So `∏ |f i (m i)| ≤ projSeminorm(⨂ m i)`.
4. Taking sup over `f i` with `‖f i‖ ≤ 1` gives `∏ ‖inclusionInDoubleDual(m i)‖ ≤ projSeminorm`.
5. By `h_bidual`, the left side equals `∏ ‖m i‖`.
-/

open scoped TensorProduct BigOperators
open PiTensorProduct NormedSpace Filter Topology

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- The projective seminorm is multiplicative on pure tensors, assuming bidual isometry. -/
theorem projectiveSeminorm_tprod_of_bidual_iso
    (m : Π i, E i)
    (h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  apply le_antisymm (projectiveSeminorm_tprod_le m)
  -- Lower bound: use dualDistribL + h_bidual
  -- For any representation ⨂ₜ m i = ∑ ⨂ₜ v_j, we need ∏ ‖m i‖ ≤ ∑ ∏ ‖v_j i‖.
  -- By duality: for f with ‖f i‖ ≤ 1, |∏ f i (m i)| ≤ projectiveSeminorm (⨂ₜ m i).
  -- Taking sup and using h_bidual gives the result.
  sorry

end ProjSeminorm
