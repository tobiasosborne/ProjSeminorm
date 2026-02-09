/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
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
  constructor
  · rintro _ ⟨x, rfl⟩
    exact div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _) (f.le_opNorm x)
  · intro M hM
    apply f.opNorm_le_bound
    · exact le_trans (div_nonneg (norm_nonneg _) (norm_nonneg _)) (hM ⟨0, rfl⟩)
    · intro x
      have hMx := hM ⟨x, rfl⟩
      by_cases hx : ‖x‖ = 0
      · rw [hx, mul_zero]
        calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
          _ = 0 := by rw [hx, mul_zero]
      · rwa [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))] at hMx

/-- There exists a sequence of elements whose norm ratios converge to the operator norm. -/
theorem exists_norming_sequence (f : E →L[𝕜] F) :
    ∃ u : ℕ → E, Tendsto (fun n => ‖f (u n)‖ / ‖u n‖) atTop (nhds ‖f‖) := by
  obtain ⟨seq, -, -, htend, hmem⟩ :=
    (isLUB_opNorm f).exists_seq_monotone_tendsto (Set.range_nonempty _)
  choose w hw using hmem
  exact ⟨w, htend.congr fun n => (hw n).symm⟩

end ContinuousLinearMap
