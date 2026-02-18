/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import ProjSeminorm.Basic
import ProjSeminorm.CancellationTrick
import Mathlib.Algebra.BigOperators.Fin

/-!
# Cross Property for l^1-Type Norms

If each factor `E i` has a basis `b i` where
`‖v‖ = ∑ j, ‖(b i).coord j v‖ * ‖(b i) j‖` (the l^1 decomposition property),
then `projectiveSeminorm (⨂ₜ m_i) = ∏ ‖m_i‖`.

No h_bidual, no ultrametric, no RCLike hypothesis is needed.

## Main results

* `l1_representation_cost_ge` — every representation has cost ≥ `∏ ‖m_i‖`
* `projectiveSeminorm_tprod_l1` — `projectiveSeminorm (⨂ₜ m_i) = ∏ ‖m_i‖`
-/

open scoped TensorProduct BigOperators
open PiTensorProduct

noncomputable section

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

section L1CrossProperty

variable {σ : ι → Type*} [∀ i, Fintype (σ i)]
  (b : Π i, Module.Basis (σ i) 𝕜 (E i))

omit [∀ i, Fintype (σ i)] in
/-- Coordinate extraction for scaled pi tensor representations. -/
lemma coord_piTensor_eq_scaled
    (m : Π i, E i) {n : ℕ} (c : Fin n → 𝕜) (ms : Fin n → Π i, E i)
    (h : (⨂ₜ[𝕜] i, m i) = ∑ j, c j • (⨂ₜ[𝕜] i, ms j i))
    (idx : Π i, σ i) :
    ∏ i, (b i).coord (idx i) (m i) =
      ∑ j, c j * ∏ i, (b i).coord (idx i) (ms j i) := by
  set φ : Module.Dual 𝕜 (⨂[𝕜] i, E i) :=
    PiTensorProduct.dualDistrib (R := 𝕜) (M := E)
      (⨂ₜ[𝕜] i, (b i).coord (idx i))
  have hφ : ∀ x : Π i, E i,
      φ (⨂ₜ[𝕜] i, x i) = ∏ i, (b i).coord (idx i) (x i) :=
    fun x => PiTensorProduct.dualDistrib_apply _ x
  rw [← hφ m, h, map_sum]
  simp only [map_smul, hφ, smul_eq_mul]

omit [∀ i, Fintype (σ i)] in
/-- Per-tuple inequality: for each index tuple, the product of
coordinate-times-basis norms is bounded by a sum over the representation. -/
lemma per_tuple_ineq
    (m : Π i, E i) {n : ℕ} (c : Fin n → 𝕜) (ms : Fin n → Π i, E i)
    (h : (⨂ₜ[𝕜] i, m i) = ∑ j, c j • (⨂ₜ[𝕜] i, ms j i))
    (idx : Π i, σ i) :
    ∏ i, (‖(b i).coord (idx i) (m i)‖ * ‖(b i) (idx i)‖) ≤
      ∑ j, ‖c j‖ * ∏ i, (‖(b i).coord (idx i) (ms j i)‖ * ‖(b i) (idx i)‖) := by
  have hcoord := coord_piTensor_eq_scaled b m c ms h idx
  calc ∏ i, (‖(b i).coord (idx i) (m i)‖ * ‖(b i) (idx i)‖)
      = (∏ i, ‖(b i).coord (idx i) (m i)‖) * ∏ i, ‖(b i) (idx i)‖ :=
        Finset.prod_mul_distrib
    _ = ‖∏ i, (b i).coord (idx i) (m i)‖ * ∏ i, ‖(b i) (idx i)‖ := by
        rw [norm_prod]
    _ = ‖∑ j, c j * ∏ i, (b i).coord (idx i) (ms j i)‖ *
          ∏ i, ‖(b i) (idx i)‖ := by rw [hcoord]
    _ ≤ (∑ j, ‖c j * ∏ i, (b i).coord (idx i) (ms j i)‖) *
          ∏ i, ‖(b i) (idx i)‖ := by
        gcongr; exact norm_sum_le ..
    _ = (∑ j, ‖c j‖ * ∏ i, ‖(b i).coord (idx i) (ms j i)‖) *
          ∏ i, ‖(b i) (idx i)‖ := by
        simp_rw [norm_mul, norm_prod]
    _ = ∑ j, ‖c j‖ * ((∏ i, ‖(b i).coord (idx i) (ms j i)‖) *
          ∏ i, ‖(b i) (idx i)‖) := by
        rw [Finset.sum_mul]; congr 1; ext j; ring
    _ = ∑ j, ‖c j‖ * ∏ i, (‖(b i).coord (idx i) (ms j i)‖ *
          ‖(b i) (idx i)‖) := by
        congr 1; ext j; congr 1; rw [← Finset.prod_mul_distrib]

/-- Every scaled representation of a pure tensor in l^1-normed spaces
has cost at least `∏ ‖m i‖`. -/
theorem l1_representation_cost_ge
    (hl1 : ∀ i (v : E i), ‖v‖ = ∑ j, ‖(b i).coord j v‖ * ‖(b i) j‖)
    (m : Π i, E i) {n : ℕ} (c : Fin n → 𝕜) (ms : Fin n → Π i, E i)
    (h : (⨂ₜ[𝕜] i, m i) = ∑ j, c j • (⨂ₜ[𝕜] i, ms j i)) :
    ∏ i, ‖m i‖ ≤ ∑ j, ‖c j‖ * ∏ i, ‖ms j i‖ := by
  classical
  -- Rewrite norms using l^1 property
  have hlhs : ∏ i, ‖m i‖ = ∏ i, ∑ k, ‖(b i).coord k (m i)‖ * ‖(b i) k‖ :=
    Finset.prod_congr rfl (fun i _ => hl1 i (m i))
  have hrhs : ∀ j, ∏ i, ‖ms j i‖ = ∏ i, ∑ k, ‖(b i).coord k (ms j i)‖ * ‖(b i) k‖ :=
    fun j => Finset.prod_congr rfl (fun i _ => hl1 i (ms j i))
  rw [hlhs]; simp_rw [hrhs]
  -- Apply Fintype.prod_sum: ∏_i ∑_k f(i,k) = ∑_σ ∏_i f(i, σ i)
  rw [Fintype.prod_sum]; simp_rw [Fintype.prod_sum]
  -- Distribute ‖c j‖ * into the inner sum
  simp_rw [Finset.mul_sum]
  -- Swap sums on RHS: ∑_j ∑_σ ... = ∑_σ ∑_j ...
  rw [Finset.sum_comm]
  -- Apply per-tuple inequality
  exact Finset.sum_le_sum (fun σ _ => per_tuple_ineq b m c ms h σ)

end L1CrossProperty

/-- The projective seminorm of a pure tensor equals the product of norms
when each factor has an l^1-type norm with respect to some basis. -/
theorem projectiveSeminorm_tprod_l1
    {σ : ι → Type*} [∀ i, Fintype (σ i)]
    (b : Π i, Module.Basis (σ i) 𝕜 (E i))
    (hl1 : ∀ i (v : E i), ‖v‖ = ∑ j, ‖(b i).coord j v‖ * ‖(b i) j‖)
    (m : Π i, E i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ := by
  classical
  apply le_antisymm (projectiveSeminorm_tprod_le m)
  rw [projectiveSeminorm_apply]
  haveI : Nonempty (lifts (⨂ₜ[𝕜] i, m i)) :=
    nonempty_subtype.mpr (nonempty_lifts _)
  apply le_ciInf
  intro ⟨p, hp⟩
  rw [mem_lifts_iff] at hp
  -- Convert projectiveSeminormAux to Fin-indexed sum
  have haux : projectiveSeminormAux p =
      ∑ j : Fin p.toList.length, ‖p.toList[↑j].1‖ * ∏ i, ‖p.toList[↑j].2 i‖ := by
    simp [projectiveSeminormAux, ← Fin.sum_univ_fun_getElem]
  rw [haux]
  -- Convert the representation identity to Fin-indexed form
  exact l1_representation_cost_ge b hl1 m _ _
    (hp.symm.trans (Fin.sum_univ_fun_getElem p.toList
      (fun x => x.1 • (⨂ₜ[𝕜] i, x.2 i))).symm)

end ProjSeminorm
