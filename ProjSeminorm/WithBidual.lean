/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import ProjSeminorm.DualDistribL

/-!
# Projective Seminorm Multiplicativity with Bidual Hypothesis

The main theorem: the projective seminorm is multiplicative on pure tensors,
assuming each factor embeds isometrically into its bidual.

## Main statements

- `projectiveSeminorm_tprod_of_bidual_iso`: `π(⨂ₜ m_i) = ∏ ‖m_i‖` given `h_bidual`.

## Proof structure

1. For each index `i`, construct a norming sequence for `inclusionInDoubleDual(m_i)`
   via `exists_norming_sequence`.
2. The product of the norming ratios converges to `∏ ‖m_i‖` (using `h_bidual` to
   rewrite the limit target).
3. Each product term is bounded above by `projectiveSeminorm(⨂ₜ m_i)` via the
   duality argument: evaluate `dualDistribL(⨂ₜ g_i)` on the tensor, then bound
   using `le_opNorm` and `injectiveSeminorm_le_projectiveSeminorm`.
4. Pass to the limit via `le_of_tendsto'`.
-/

open scoped TensorProduct BigOperators
open PiTensorProduct NormedSpace Filter Topology

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- The projective seminorm is multiplicative on pure tensors,
assuming bidual isometry. -/
theorem projectiveSeminorm_tprod_of_bidual_iso
    (m : Π i, E i)
    (h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  apply le_antisymm (projectiveSeminorm_tprod_le m)
  -- For each i, get a norming sequence for inclusionInDoubleDual(m i)
  choose u hu using fun i =>
    ContinuousLinearMap.exists_norming_sequence
      ((inclusionInDoubleDual 𝕜 (E i)) (m i))
  -- Rewrite limit target using h_bidual
  simp_rw [h_bidual] at hu
  -- Product of convergent sequences converges to product of limits
  have hprod : Tendsto
      (fun n => ∏ i : ι,
        ‖(inclusionInDoubleDual 𝕜 (E i) (m i)) (u i n)‖ / ‖u i n‖)
      atTop (nhds (∏ i : ι, ‖m i‖)) :=
    tendsto_finset_prod _ (fun i _ => hu i)
  -- Each term ≤ projectiveSeminorm (see docstring for proof sketch)
  have hle : ∀ n, ∏ i : ι,
      ‖(inclusionInDoubleDual 𝕜 (E i) (m i)) (u i n)‖ / ‖u i n‖ ≤
      projectiveSeminorm (⨂ₜ[𝕜] i, m i) := by
    intro n
    by_cases h : ∃ i, u i n = 0
    · -- Zero case: factor is 0/0 = 0, product is 0
      obtain ⟨i₀, hi₀⟩ := h
      have : (fun i => ‖((inclusionInDoubleDual 𝕜 (E i)) (m i))
          (u i n)‖ / ‖u i n‖) i₀ = 0 := by simp [hi₀]
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀) this]
      exact apply_nonneg _ _
    · -- Nonzero case: duality argument
      push_neg at h
      -- dual_def : inclusionInDoubleDual 𝕜 E x f = f x (rfl)
      simp only [NormedSpace.dual_def]
      have hpos : 0 < ∏ i : ι, ‖u i n‖ := by
        apply Finset.prod_pos; intro i _
        rcases eq_or_lt_of_le (ContinuousLinearMap.opNorm_nonneg (u i n)) with h0 | h0
        · exfalso; apply h i; ext x
          have := (u i n).le_opNorm x
          simp only [← h0, zero_mul] at this
          exact norm_le_zero_iff.mp this
        · exact h0
      simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib,
        Finset.prod_inv_distrib]
      rw [mul_inv_le_iff₀ hpos]
      calc ∏ i : ι, ‖(u i n) (m i)‖
          = ‖∏ i : ι, (u i n) (m i)‖ := (norm_prod Finset.univ _).symm
        _ = ‖dualDistribL (⨂ₜ[𝕜] i, u i n) (⨂ₜ[𝕜] i, m i)‖ := by
            rw [dualDistribL_tprod_apply]
        _ ≤ ‖dualDistribL (⨂ₜ[𝕜] i, u i n)‖ *
            ‖(⨂ₜ[𝕜] i, m i)‖ :=
            (dualDistribL (⨂ₜ[𝕜] i, u i n)).le_opNorm _
        _ ≤ ‖dualDistribL (⨂ₜ[𝕜] i, u i n)‖ *
            projectiveSeminorm (⨂ₜ[𝕜] i, m i) := by
            gcongr
            exact injectiveSeminorm_le_projectiveSeminorm _
        _ ≤ (∏ i, ‖u i n‖) *
            projectiveSeminorm (⨂ₜ[𝕜] i, m i) := by
            gcongr
            exact norm_dualDistribL_tprod_le _
        _ = projectiveSeminorm (⨂ₜ[𝕜] i, m i) *
            ∏ i, ‖u i n‖ := mul_comm _ _
  -- Pass to the limit
  exact le_of_tendsto' hprod hle

end ProjSeminorm
