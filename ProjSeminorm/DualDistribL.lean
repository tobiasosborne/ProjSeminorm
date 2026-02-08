import ProjSeminorm.Basic
import ProjSeminorm.NormingSeq

/-!
# Continuous Dual Distribution Map

The algebraic `dualDistrib` is promoted to a continuous linear map `dualDistribL`,
using the projective-to-injective seminorm comparison. This is Step 3 of the
projective seminorm multiplicativity proof.
-/

open PiTensorProduct

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- The projective seminorm on `⨂[𝕜] i, 𝕜` equals `∏ i, ‖c i‖`. -/
theorem projectiveSeminorm_field_tprod (c : ι → 𝕜) :
    projectiveSeminorm (⨂ₜ[𝕜] i, c i) = ∏ i, ‖c i‖ := by
  apply le_antisymm (projectiveSeminorm_tprod_le c)
  -- Lower bound: evaluate mkPiAlgebra (= multiplication) on the tensor
  have h1 := norm_eval_le_projectiveSeminorm (⨂ₜ[𝕜] i, c i) 𝕜
    (ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝕜)
  simp [PiTensorProduct.lift.tprod, ContinuousMultilinearMap.mkPiAlgebra_apply,
    ContinuousMultilinearMap.norm_mkPiAlgebra, norm_prod] at h1
  linarith

/-- `dualDistrib` as a continuous linear map. -/
noncomputable def dualDistribL :
    (⨂[𝕜] i, StrongDual 𝕜 (E i)) →L[𝕜]
    StrongDual 𝕜 (⨂[𝕜] i, E i) := by
  sorry

theorem dualDistribL_tprod_apply
    (f : Π i, StrongDual 𝕜 (E i)) (m : Π i, E i) :
    dualDistribL (⨂ₜ[𝕜] i, f i) (⨂ₜ[𝕜] i, m i) = ∏ i, f i (m i) := by
  sorry

theorem norm_dualDistribL_tprod_le (f : Π i, StrongDual 𝕜 (E i)) :
    ‖dualDistribL (⨂ₜ[𝕜] i, f i)‖ ≤ ∏ i, ‖f i‖ := by
  sorry

end ProjSeminorm
