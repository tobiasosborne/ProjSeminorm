/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import ProjSeminorm.Basic

/-!
# Direct Algebraic Approach to Projective Seminorm Multiplicativity

This file documents a direct algebraic attempt to prove
`projectiveSeminorm (v ⊗ w) ≥ ‖v‖ * ‖w‖` without using duality (and hence without `h_bidual`).

## The Approach

For a binary tensor product E ⊗ F, given a pure tensor `v ⊗ w = ∑_j v_j ⊗ w_j`:

1. **Reduce to independent case**: Choose a maximal linearly independent subset of `{w_j}`,
   say `w_1, ..., w_s`. The dependent vectors satisfy `w_j = ∑_k a_{jk} w_k` for `j > s`.

2. **Combine terms**: `∑ v_j ⊗ w_j = ∑_k u_k ⊗ w_k` where `u_k = v_k + ∑_{j>s} a_{jk} v_j`.

3. **Use linear independence**: Since `w_1, ..., w_s` are linearly independent in the tensor
   product and `v ⊗ w = ∑_k u_k ⊗ w_k`, we get `w = ∑_k c_k w_k` and `u_k = c_k v`.

4. **Reduced cost bound**: `∑_k ‖u_k‖ · ‖w_k‖ = ‖v‖ · ∑_k |c_k| · ‖w_k‖ ≥ ‖v‖ · ‖w‖`
   (by the triangle inequality on `w = ∑ c_k w_k`).

## The Obstruction

Step 4 proves the lower bound for the **reduced** representation. But the original
representation has cost `∑_j ‖v_j‖ · ‖w_j‖`, and we need:

  `∑_j ‖v_j‖ · ‖w_j‖ ≥ ∑_k ‖u_k‖ · ‖w_k‖`

This does NOT hold in general! The reduction step changes the cost:

- `u_k = v_k + ∑_{j>s} a_{jk} v_j` gives `‖u_k‖ ≤ ‖v_k‖ + ∑_{j>s} |a_{jk}| · ‖v_j‖`
  (correct direction for bounding `u_k` above, but we need `u_k` below)

- The chain: `‖v‖ · ‖w‖ ≤ ‖v‖ · ∑_k |c_k| · ‖w_k‖`   (triangle on w)
            `= ∑_k ‖u_k‖ · ‖w_k‖`                       (from u_k = c_k v)
            `≤ ∑_k (∑_j |a_{jk}| ‖v_j‖) · ‖w_k‖`        (triangle on u_k)
            `= ∑_j ‖v_j‖ · (∑_k |a_{jk}| ‖w_k‖)`        (swap sums)

  We need this last line ≤ `∑_j ‖v_j‖ · ‖w_j‖`, i.e.,
  `∑_k |a_{jk}| · ‖w_k‖ ≤ ‖w_j‖` for each `j`. But:

  `‖w_j‖ = ‖∑_k a_{jk} w_k‖ ≤ ∑_k |a_{jk}| · ‖w_k‖`

  This is the WRONG direction! The triangle inequality gives `≤`, but we need `≥`.

## Special Cases

- **Ultrametric fields**: The non-archimedean triangle inequality is nearly tight for
  d-orthogonal bases (defect ≤ 1/d), so both inequalities become approximate equalities
  and the proof closes by taking d → 1.

- **Archimedean fields** (ℝ, ℂ): The triangle inequality can be arbitrarily lossy,
  so this approach is fundamentally stuck. However, for ℝ/ℂ the duality approach works
  unconditionally (Hahn-Banach gives isometric bidual embedding).

## Conclusion

The direct algebraic approach fails because reducing a tensor representation to one with
linearly independent components can change the cost in an uncontrollable way. This explains
why the duality-based proof (using `h_bidual`) is the natural route.
-/

open scoped TensorProduct BigOperators

namespace ProjSeminorm.DirectApproach

/-! ### The key algebraic fact

In `E ⊗ F`, if `∑ e_j ⊗ f_j = 0` and `f_j` are linearly independent (or form a basis),
then `e_j = 0` for all `j`. This is the fact that makes the reduced representation
well-determined.

Mathlib provides `TensorProduct.sum_tmul_basis_right_eq_zero` for the basis version.
-/

-- The key algebraic fact is already in mathlib:
-- TensorProduct.sum_tmul_basis_right_eq_zero:
--   ∀ (𝒞 : Basis κ R N) (b : κ →₀ M),
--     b.sum (fun i m => m ⊗ₜ 𝒞 i) = 0 → b = 0

/-! ### The proof attempt for the reduced case

When `w_1, ..., w_s` are linearly independent and `v ⊗ w = ∑_k u_k ⊗ w_k`,
the coefficients `u_k` are uniquely determined: `u_k = c_k · v` where `w = ∑_k c_k w_k`.

For this REDUCED representation, the lower bound holds:
  `∑_k ‖u_k‖ · ‖w_k‖ = ‖v‖ · ∑_k |c_k| · ‖w_k‖ ≥ ‖v‖ · ‖w‖`

This is a straightforward application of the triangle inequality (correct direction). -/

/-- For an independent representation `v ⊗ w = ∑_k (c_k • v) ⊗ w_k` with
`w = ∑_k c_k • w_k`, the cost is at least `‖v‖ * ‖w‖`.

This is the step that DOES work. The obstruction is that arbitrary representations
cannot be reduced to this form without potentially increasing cost. -/
theorem reduced_representation_cost_ge
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ} (v : E) (c : Fin n → 𝕜) (w : Fin n → F)
    (w' : F) (hw : ∑ k, c k • w k = w') :
    ‖v‖ * ‖w'‖ ≤ ‖v‖ * ∑ k : Fin n, ‖c k‖ * ‖w k‖ := by
  gcongr
  calc ‖w'‖ = ‖∑ k, c k • w k‖ := by rw [hw]
    _ ≤ ∑ k, ‖c k • w k‖ := norm_sum_le ..
    _ = ∑ k, ‖c k‖ * ‖w k‖ := by simp_rw [norm_smul]

/-! ### The obstruction

The above theorem shows `‖v‖ * ‖w‖ ≤ ‖v‖ * ∑_k |c_k| * ‖w_k‖ = ∑_k ‖u_k‖ * ‖w_k‖`
for the REDUCED representation with independent `w_k`.

However, the projective seminorm is the infimum over ALL representations, not just
independent ones. To use the reduced-representation bound, we would need:

  `∑_j ‖v_j‖ * ‖w_j‖ ≥ ∑_k ‖u_k‖ * ‖w_k‖`  (original cost ≥ reduced cost)

This fails because the reduction `u_k = v_k + ∑_{j>s} a_{jk} v_j` can have
`‖u_k‖ > ‖v_k‖`, and we lose the cost contributions from the removed terms `j > s`
without compensating for the increased cost of the remaining terms.

The following shows the wrong-direction inequality explicitly. -/

/-- The triangle inequality goes the wrong way for the reduction step.
Given `w_j = ∑_k a_{jk} w_k` (expressing dependent vectors in terms of independent ones),
we have `∑_k |a_{jk}| * ‖w_k‖ ≥ ‖w_j‖`, NOT `≤`. So the swap-of-sums argument
produces a quantity LARGER than both `‖v‖ * ‖w‖` and `∑_j ‖v_j‖ * ‖w_j‖`. -/
theorem triangle_wrong_direction
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    {n : ℕ} (a : Fin n → 𝕜) (w : Fin n → F) :
    ‖∑ k, a k • w k‖ ≤ ∑ k, ‖a k‖ * ‖w k‖ := by
  calc ‖∑ k, a k • w k‖ ≤ ∑ k, ‖a k • w k‖ := norm_sum_le ..
    _ = ∑ k, ‖a k‖ * ‖w k‖ := by simp_rw [norm_smul]

-- The above gives `‖w_j‖ ≤ ∑_k |a_{jk}| * ‖w_k‖` — correct, but useless.
-- We NEED `‖w_j‖ ≥ ∑_k |a_{jk}| * ‖w_k‖` to close the proof, which is false in general.

end ProjSeminorm.DirectApproach
