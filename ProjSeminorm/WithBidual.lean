import ProjSeminorm.DualDistribL

/-!
# Projective Seminorm Multiplicativity with Bidual Hypothesis

The main theorem: the projective seminorm is multiplicative on pure tensors,
assuming each factor embeds isometrically into its bidual. This is Step 4
of the proof plan.

## Proof structure (compiles, sorry in `hle`)

The outer framework works:
1. Norming sequences from `exists_norming_sequence` (Step 2)
2. Product convergence via `tendsto_finset_prod`
3. Limit passage via `le_of_tendsto'`

The sorry is in `hle`: showing each product term ≤ projectiveSeminorm.

## Learnings for filling the sorry

The `hle` proof splits into two cases:

**Zero case** (`∃ i, u i n = 0`): Product has a zero factor, so it's 0.
- `Finset.prod_eq_zero` works for the product = 0 step
- Need `projectiveSeminorm.nonneg'` or `apply_nonneg` (NOT `map_nonneg`,
  which needs `OrderHomClass`; NOT `Seminorm.nonneg`, which doesn't exist)

**Nonzero case** (`∀ i, u i n ≠ 0`): The duality calc chain.
- `norm_pos_iff` for `StrongDual` needs explicit type annotation — the norm
  instance is `ContinuousLinearMap.hasOpNorm`, not `NormedAddGroup.toNorm`.
  Fix: use `(norm_pos_iff (α := StrongDual 𝕜 (E i))).mpr` or
  `ContinuousLinearMap.norm_pos_iff.mpr`.
- `Finset.prod_div_distrib` requires `CommGroup` — `ℝ` is NOT a `CommGroup`.
  Instead use: `simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib,
  Finset.prod_inv_distrib]` then `mul_inv_le_iff₀`.
- The calc chain `∏ ‖g(m)‖ ≤ (∏ ‖g‖) * projSem` via:
  `norm_prod` → `dualDistribL_tprod_apply` → `le_opNorm` →
  `injectiveSeminorm_le_projectiveSeminorm` → `norm_dualDistribL_tprod_le`
- `inclusionInDoubleDual_apply` exists and simplifies `incl(m)(f) = f(m)`.
- `gcongr` works for the monotonicity steps.
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
