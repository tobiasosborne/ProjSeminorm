/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-!
# Cancellation Trick for Collinear Tensor Representations

We prove that for a binary tensor product `E ⊗[𝕜] F` over a nontrivially normed field,
the **cross property** holds for all representations where the second-factor vectors
are collinear (scalar multiples of a single vector `w₁`). This result requires
**no Hahn-Banach hypothesis** (`h_bidual`).

## The Cancellation Trick

Given `v ⊗ₜ w = ∑ⱼ vⱼ ⊗ₜ (αⱼ • w₁)`:

1. **Bilinearity collapse**: The sum equals `(∑ αⱼ • vⱼ) ⊗ₜ w₁`.
2. **Triangle inequality** (correct direction!): `∑ |αⱼ| • ‖vⱼ‖ ≥ ‖∑ αⱼ • vⱼ‖`.
3. **Norm invariance**: From `v ⊗ₜ w = u ⊗ₜ w₁`, we get `‖u‖ • ‖w₁‖ = ‖v‖ • ‖w‖`.

The key insight is that the tensor constraint forces residual cancellation,
making the triangle inequality go in the correct direction.

## Main results

* `ProjSeminorm.collinear_cost_ge`: The main theorem — the cost of any collinear
  representation is at least `‖v‖ * ‖w‖`.
-/

open scoped TensorProduct

namespace ProjSeminorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-! ### Algebraic lemmas -/

/-- Over a field, `a ⊗ₜ b = 0` implies `a = 0` or `b = 0`.
This uses that modules over a `DivisionRing` are free (hence flat). -/
lemma tmul_eq_zero_of_field {a : E} {b : F} (h : a ⊗ₜ[𝕜] b = 0) :
    a = 0 ∨ b = 0 := by
  by_contra hab
  push_neg at hab
  obtain ⟨ha, hb⟩ := hab
  haveI : Module.Free 𝕜 E := Module.Free.of_divisionRing 𝕜 E
  have hinj : Function.Injective (LinearMap.toSpanSingleton 𝕜 F b) := by
    intro c d hcd
    simp only [LinearMap.toSpanSingleton_apply] at hcd
    exact smul_left_injective 𝕜 hb hcd
  have hlTinj := Module.Flat.lTensor_preserves_injective_linearMap
    (LinearMap.toSpanSingleton 𝕜 F b) hinj (M := E)
  have hmapped : LinearMap.lTensor E (LinearMap.toSpanSingleton 𝕜 F b)
      (a ⊗ₜ[𝕜] (1 : 𝕜)) = a ⊗ₜ[𝕜] b := by
    simp [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply]
  have h1 : a ⊗ₜ[𝕜] (1 : 𝕜) = 0 := hlTinj (by rw [hmapped, h, map_zero])
  apply ha
  have h2 := congr_arg (TensorProduct.rid 𝕜 E) h1
  simp only [map_zero] at h2
  simpa using h2

/-- Over a field, if `a ⊗ₜ b = 0` and `b ≠ 0`, then `a = 0`. -/
lemma left_eq_zero_of_tmul_eq_zero {a : E} {b : F} (h : a ⊗ₜ[𝕜] b = 0) (hb : b ≠ 0) :
    a = 0 := by
  exact (tmul_eq_zero_of_field h).resolve_right hb

/-! ### Algebraic dual functional -/

/-- For `v ≠ 0` in a vector space over a nontrivially normed field,
there exists a linear functional `g` with `g v = 1`. -/
lemma exists_dual_eq_one (𝕜' : Type*) [NontriviallyNormedField 𝕜']
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜' V]
    {v : V} (hv : v ≠ 0) : ∃ g : V →ₗ[𝕜'] 𝕜', g v = 1 := by
  haveI : Module.Free 𝕜' V := Module.Free.of_divisionRing 𝕜' V
  let B := Module.Free.chooseBasis 𝕜' V
  have hBv : B.repr v ≠ 0 :=
    fun h => hv (B.repr.injective (by rw [h, map_zero]))
  have : ∃ i, B.repr v i ≠ 0 := by
    by_contra h; push_neg at h
    exact hBv (Finsupp.ext (fun i => by simp [h i]))
  obtain ⟨i, hi⟩ := this
  exact ⟨(B.repr v i)⁻¹ • B.coord i, by simp [hi]⟩

/-! ### Norm invariance for rank-1 tensors -/

/-- If `v ⊗ₜ w = u ⊗ₜ w₁` in a tensor product over a field, then
`‖v‖ * ‖w‖ = ‖u‖ * ‖w₁‖`. Uses an algebraic functional to extract
the scalar relating the two representations. -/
theorem tmul_norm_product_eq {v u : E} {w w₁ : F}
    (h : v ⊗ₜ[𝕜] w = u ⊗ₜ[𝕜] w₁) :
    ‖v‖ * ‖w‖ = ‖u‖ * ‖w₁‖ := by
  by_cases hv : v = 0
  · subst hv; simp only [TensorProduct.zero_tmul] at h
    rcases tmul_eq_zero_of_field h.symm with rfl | rfl <;> simp
  by_cases hw₁ : w₁ = 0
  · subst hw₁; simp only [TensorProduct.tmul_zero] at h
    rcases tmul_eq_zero_of_field h with rfl | rfl <;> simp
  -- v ≠ 0, w₁ ≠ 0. Get g : E →ₗ 𝕜 with g(v) = 1.
  obtain ⟨g, hgv⟩ := exists_dual_eq_one 𝕜 hv
  -- Apply (g ⊗ id) then lid: g(v)•w = g(u)•w₁ in F
  have hlift : g v • w = g u • w₁ := by
    have hm := congr_arg ((TensorProduct.lid 𝕜 F).toLinearMap ∘ₗ
      TensorProduct.map g (LinearMap.id : F →ₗ[𝕜] F)) h
    simpa [TensorProduct.map_tmul, TensorProduct.lid_tmul] using hm
  rw [hgv, one_smul] at hlift
  -- hlift : w = g u • w₁. Set c := g u.
  set c := g u
  -- (u - c • v) ⊗ₜ w₁ = 0, hence u = c • v
  have hsub : (u - c • v) ⊗ₜ[𝕜] w₁ = (0 : E ⊗[𝕜] F) := by
    rw [TensorProduct.sub_tmul, TensorProduct.smul_tmul, ← hlift]
    simp [h]
  have hu_eq : u = c • v :=
    sub_eq_zero.mp (left_eq_zero_of_tmul_eq_zero hsub hw₁)
  -- ‖u‖*‖w₁‖ = ‖c•v‖*‖w₁‖ = |c|*‖v‖*‖w₁‖ = ‖v‖*‖c•w₁‖ = ‖v‖*‖w‖
  rw [hu_eq, hlift, norm_smul, norm_smul]; ring

/-! ### The cancellation trick: main theorem -/

/-- **Cancellation trick**: If `v ⊗ₜ w = ∑ⱼ vⱼ ⊗ₜ (αⱼ • w₁)` (collinear second factors),
then the representation cost satisfies `∑ ‖vⱼ‖ * ‖αⱼ • w₁‖ ≥ ‖v‖ * ‖w‖`.

This is proved **without** any Hahn-Banach or bidual embedding hypothesis.
The key: bilinearity collapses the sum to `(∑ αⱼ • vⱼ) ⊗ₜ w₁`, the triangle
inequality applies in the correct direction, and norm invariance closes the proof. -/
theorem collinear_cost_ge {ι : Type*} [Fintype ι]
    {v : E} {w : F} {v' : ι → E} {α : ι → 𝕜} {w₁ : F}
    (h : v ⊗ₜ[𝕜] w = ∑ j : ι, v' j ⊗ₜ[𝕜] (α j • w₁)) :
    ‖v‖ * ‖w‖ ≤ ∑ j : ι, ‖v' j‖ * ‖α j • w₁‖ := by
  -- Step 1: Bilinearity collapse
  -- ∑ v'ⱼ ⊗ₜ (αⱼ • w₁) = ∑ (αⱼ • v'ⱼ) ⊗ₜ w₁ = (∑ αⱼ • v'ⱼ) ⊗ₜ w₁
  have hcollapse : v ⊗ₜ[𝕜] w = (∑ j, α j • v' j) ⊗ₜ[𝕜] w₁ := by
    rw [h]
    simp_rw [← TensorProduct.smul_tmul]
    rw [← TensorProduct.sum_tmul]
  -- Step 2: Norm invariance — ‖∑ αⱼ • v'ⱼ‖ * ‖w₁‖ = ‖v‖ * ‖w‖
  have hnorm_eq := tmul_norm_product_eq hcollapse
  -- Step 3: Triangle inequality + norm_smul
  -- ∑ ‖v'ⱼ‖ * ‖αⱼ • w₁‖ = ∑ ‖v'ⱼ‖ * (‖αⱼ‖ * ‖w₁‖) = ‖w₁‖ * ∑ ‖αⱼ‖ * ‖v'ⱼ‖
  -- ≥ ‖w₁‖ * ‖∑ αⱼ • v'ⱼ‖ = ‖v‖ * ‖w‖
  calc ∑ j : ι, ‖v' j‖ * ‖α j • w₁‖
      = ∑ j, ‖v' j‖ * (‖α j‖ * ‖w₁‖) := by simp_rw [norm_smul]
    _ = ∑ j, ‖α j‖ * ‖v' j‖ * ‖w₁‖ := by congr 1; ext j; ring
    _ = (∑ j, ‖α j‖ * ‖v' j‖) * ‖w₁‖ := (Finset.sum_mul ..).symm
    _ ≥ ‖∑ j, α j • v' j‖ * ‖w₁‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        calc ‖∑ j, α j • v' j‖
            ≤ ∑ j, ‖α j • v' j‖ := norm_sum_le ..
          _ = ∑ j, ‖α j‖ * ‖v' j‖ := by simp_rw [norm_smul]
    _ = ‖v‖ * ‖w‖ := hnorm_eq.symm

end ProjSeminorm
