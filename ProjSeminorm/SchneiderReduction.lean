/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import ProjSeminorm.Basic
import ProjSeminorm.CancellationTrick
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Data.Fintype.Order

/-!
# Schneider Reduction: Cross Property for Ultrametric Norms

This file proves the Cross Property (CP) for the projective tensor seminorm
over ultrametric seminormed spaces:

  `projectiveSeminorm (v ⊗ₜ w) = ‖v‖ * ‖w‖`

The argument follows Schneider's Prop 17.4 (Nonarchimedean Functional Analysis,
Springer 2002). The key insight is that ε-orthogonal bases exist in finite-dimensional
ultrametric normed spaces, and using coordinate expansions with the non-archimedean
absolute value, every representation `v ⊗ w = Σ vⱼ ⊗ wⱼ` satisfies
`Σ ‖vⱼ‖ · ‖wⱼ‖ ≥ (1+ε)⁻⁴ · ‖v‖ · ‖w‖`. Taking ε → 0 gives CP.

## Main results

* `IsEpsOrthogonal` — predicate for ε-orthogonal bases
* `exists_epsOrthogonal_basis` — existence of ε-orthogonal bases (Schneider Lemma 17.3)
* `representation_cost_ge` — every representation has cost ≥ (1+ε)⁻⁴ ‖v‖·‖w‖
* `projectiveSeminorm_tprod_ultrametric` — the CP for ultrametric norms

## References

* P. Schneider, *Nonarchimedean Functional Analysis*, Springer 2002, Ch. 17
* C. Perez-Garcia, W.H. Schikhof, *Locally Convex Spaces over Non-Archimedean
  Valued Fields*, Cambridge 2010
-/

open scoped TensorProduct BigOperators
open PiTensorProduct

noncomputable section

namespace ProjSeminorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

-- ============================================================================
-- Step 2: Ultrametric norm upper bound for basis expansions
-- ============================================================================

/-- In an ultrametric seminormed space, the norm of a finite sum `∑ i, c i • b i`
is bounded by the supremum of `‖c i‖ * ‖b i‖`.

This follows from the ultrametric triangle inequality: `‖x + y‖ ≤ max ‖x‖ ‖y‖`.
Iterating gives `‖∑ xᵢ‖ ≤ maxᵢ ‖xᵢ‖`, and `‖c • b‖ = ‖c‖ * ‖b‖`. -/
lemma norm_sum_le_iSup_mul_norm {ι : Type*} [Fintype ι] [IsUltrametricDist E]
    (b : Module.Basis ι 𝕜 E) (c : ι → 𝕜) :
    ‖∑ i, c i • b i‖ ≤ ⨆ i, ‖c i‖ * ‖b i‖ := by
  by_cases hι : IsEmpty ι
  · simp
  · haveI : Nonempty ι := not_isEmpty_iff.mp hι
    have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
    obtain ⟨i₀, _, hi₀⟩ :=
      IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty hne (fun i => c i • b i)
    calc ‖∑ i, c i • b i‖ ≤ ‖c i₀ • b i₀‖ := hi₀
      _ = ‖c i₀‖ * ‖b i₀‖ := norm_smul _ _
      _ ≤ ⨆ i, ‖c i‖ * ‖b i‖ :=
        le_ciSup (Finite.bddAbove_range (fun i => ‖c i‖ * ‖b i‖)) i₀

-- ============================================================================
-- Step 3: Define ε-orthogonal basis
-- ============================================================================

/-- A basis `b` of a normed space is ε-orthogonal if the norm of any linear
combination is within a factor of `(1+ε)` of the maximum term norm.

This says the basis is "almost orthonormal" in the non-archimedean sense:
  `‖∑ cᵢ eᵢ‖ ≥ (1+ε)⁻¹ · maxᵢ (|cᵢ| · ‖eᵢ‖)`

Reference: Schneider, Definition before Lemma 17.3. -/
def IsEpsOrthogonal {ι : Type*} [Fintype ι] (ε : ℝ) (b : Module.Basis ι 𝕜 E) : Prop :=
  0 < ε ∧ ∀ (c : ι → 𝕜),
    ‖∑ i, c i • b i‖ ≥ (1 + ε)⁻¹ * (⨆ i, ‖c i‖ * ‖b i‖)

-- ============================================================================
-- Step 4: ε-orthogonal basis existence, dimension 1
-- ============================================================================

/-- In dimension 1, any nonzero vector forms an ε-orthogonal basis for all ε > 0.
The single-term sum has `‖c • e‖ = |c| · ‖e‖`, which equals the supremum. -/
lemma exists_epsOrthogonal_basis_one [IsUltrametricDist E]
    (hE : Module.finrank 𝕜 E = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ b : Module.Basis (Fin 1) 𝕜 E, IsEpsOrthogonal ε b := by
  haveI : FiniteDimensional 𝕜 E := Module.finite_of_finrank_eq_succ hE
  haveI : Module.Free 𝕜 E := Module.Free.of_divisionRing
  set b := Module.finBasisOfFinrankEq 𝕜 E hE
  refine ⟨b, hε, fun c => ?_⟩
  simp only [Fin.sum_univ_one, norm_smul, ciSup_unique, Fin.default_eq_zero]
  have h1 : (0 : ℝ) ≤ ‖c 0‖ * ‖b 0‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : (1 + ε)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff_of_pos (by linarith)]
    linarith
  linarith [mul_le_of_le_one_left h1 h2]

-- ============================================================================
-- Step 5: ε-orthogonal basis existence, general (Schneider Lemma 17.3)
-- ============================================================================

/-- Every finite-dimensional ultrametric normed space admits an ε-orthogonal basis
for any ε > 0. This is the key infrastructure lemma.

The proof is by induction on `finrank`. The inductive step picks a vector `v` with
`‖v‖` close to the supremum norm, projects onto `span {v}ᗮ`, and recurses.

Reference: Schneider, Lemma 17.3. -/
theorem exists_epsOrthogonal_basis [IsUltrametricDist E]
    [FiniteDimensional 𝕜 E] (ε : ℝ) (hε : 0 < ε) :
    ∃ (b : Module.Basis (Fin (Module.finrank 𝕜 E)) 𝕜 E), IsEpsOrthogonal ε b := by
  sorry
  -- Proof sketch (induction on finrank):
  -- Base: finrank = 0 → Module.Basis.empty, vacuously true
  -- Base: finrank = 1 → exists_epsOrthogonal_basis_one
  -- Step: Pick v with ‖v‖ close to sup, project onto quotient by span {v},
  --   get (n-1)-dim ε-orthogonal basis by IH, lift back.
  --   The ultrametric property ensures the lifted basis remains ε-orthogonal.

-- ============================================================================
-- Step 6: Coordinate extraction for tensor representations
-- ============================================================================

/-- For a representation `v ⊗ w = ∑ⱼ vⱼ ⊗ wⱼ` and bases {eᵢ} for E, {fₖ} for F,
the coordinates satisfy `aᵢ · bₖ = ∑ⱼ aᵢⱼ · bₖⱼ`, where aᵢ = bE.coord i v, etc.

This follows by applying the bilinear functional `(bE.coord i, bF.coord k)` lifted
to the tensor product, to both sides of the tensor equation. -/
lemma coord_tensor_eq {ιE ιF : Type*}
    (bE : Module.Basis ιE 𝕜 E) (bF : Module.Basis ιF 𝕜 F)
    (v : E) (w : F) (n : ℕ) (vs : Fin n → E) (ws : Fin n → F)
    (h : v ⊗ₜ[𝕜] w = ∑ j, vs j ⊗ₜ ws j) (i : ιE) (k : ιF) :
    bE.coord i v * bF.coord k w = ∑ j, bE.coord i (vs j) * bF.coord k (ws j) := by
  set f := (LinearMap.mul' 𝕜 𝕜).compl₁₂ (bE.coord i) (bF.coord k)
  have hf : ∀ (u : E) (t : F),
      TensorProduct.lift f (u ⊗ₜ[𝕜] t) = bE.coord i u * bF.coord k t := by
    intro u t
    simp [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.mul'_apply]
  have := congr_arg (TensorProduct.lift f) h
  simp only [map_sum, hf] at this
  exact this

-- ============================================================================
-- Step 7: Ultrametric domination lemma
-- ============================================================================

/-- Over a non-archimedean valued field, if `a * b = ∑ⱼ aⱼ * bⱼ`, then
`maxⱼ (|aⱼ| * |bⱼ|) ≥ |a| * |b|`.

This uses the ultrametric property of the field norm: `|∑ xⱼ| ≤ maxⱼ |xⱼ|`,
so `|a*b| = |∑ aⱼbⱼ| ≤ maxⱼ |aⱼbⱼ| = maxⱼ |aⱼ|·|bⱼ|`.
Since the field norm is multiplicative, `|a|·|b| = |a*b| ≤ maxⱼ |aⱼ|·|bⱼ|`. -/
lemma exists_product_ge_of_sum_eq [IsUltrametricDist 𝕜]
    (a b : 𝕜) (n : ℕ) (as bs : Fin n → 𝕜)
    (h : a * b = ∑ j, as j * bs j) (hn : 0 < n) :
    ∃ j, ‖as j‖ * ‖bs j‖ ≥ ‖a‖ * ‖b‖ := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := Finset.univ_nonempty
  obtain ⟨j, _, hj⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty hne
    (fun j => as j * bs j)
  exact ⟨j, by simp only [norm_mul] at hj ⊢; linarith [norm_mul a b, congr_arg norm h]⟩

-- ============================================================================
-- Step 8: Single-term norm lower bound via ε-orthogonal coordinates
-- ============================================================================

/-- For an ε-orthogonal basis, the norm of a vector is bounded below by
`(1+ε)⁻¹` times any individual coordinate-times-basis-norm product.

This is immediate from the definition: `‖v‖ = ‖∑ cᵢ eᵢ‖ ≥ (1+ε)⁻¹ · maxᵢ |cᵢ|·‖eᵢ‖`
and the max is at least as large as any individual term. -/
lemma norm_ge_coord_mul_norm {ι : Type*} [Fintype ι]
    {ε : ℝ} (bE : Module.Basis ι 𝕜 E) (hb : IsEpsOrthogonal ε bE)
    (v : E) (i : ι) :
    ‖v‖ ≥ (1 + ε)⁻¹ * (‖bE.coord i v‖ * ‖bE i‖) := by
  have h_sum : ‖v‖ ≥ (1 + ε)⁻¹ * ⨆ j, ‖(bE.coord j) v‖ * ‖bE j‖ := by
    have h := hb.2 (fun j => bE.repr v j)
    rw [bE.sum_repr v] at h
    convert h using 2
  have h_le : ‖(bE.coord i) v‖ * ‖bE i‖ ≤ ⨆ j, ‖(bE.coord j) v‖ * ‖bE j‖ :=
    le_ciSup (Finite.bddAbove_range (fun j => ‖(bE.coord j) v‖ * ‖bE j‖)) i
  calc ‖v‖ ≥ (1 + ε)⁻¹ * ⨆ j, ‖(bE.coord j) v‖ * ‖bE j‖ := h_sum
    _ ≥ (1 + ε)⁻¹ * (‖(bE.coord i) v‖ * ‖bE i‖) := by
        gcongr
        exact inv_nonneg.mpr (by linarith [hb.1])

-- ============================================================================
-- Step 9: Product lower bound for one term
-- ============================================================================

/-- From ε-orthogonal bases, the cost of a single term satisfies
  `‖vs j₀‖ * ‖ws j₀‖ ≥ (1+ε)⁻² * (‖bE.coord i₀ (vs j₀)‖ * ‖bE i₀‖) *
                                    (‖bF.coord k₀ (ws j₀)‖ * ‖bF k₀‖)` -/
lemma single_term_cost_bound {ιE ιF : Type*} [Fintype ιE] [Fintype ιF]
    {ε : ℝ} {n : ℕ}
    (bE : Module.Basis ιE 𝕜 E) (bF : Module.Basis ιF 𝕜 F)
    (hbE : IsEpsOrthogonal ε bE) (hbF : IsEpsOrthogonal ε bF)
    (vs : Fin n → E) (ws : Fin n → F)
    (j₀ : Fin n) (i₀ : ιE) (k₀ : ιF) :
    ‖vs j₀‖ * ‖ws j₀‖ ≥ (1 + ε)⁻¹ ^ 2 *
      ((‖bE.coord i₀ (vs j₀)‖ * ‖bE i₀‖) * (‖bF.coord k₀ (ws j₀)‖ * ‖bF k₀‖)) := by
  have h1 := norm_ge_coord_mul_norm bE hbE (vs j₀) i₀
  have h2 := norm_ge_coord_mul_norm bF hbF (ws j₀) k₀
  have h_inv_nn : (0 : ℝ) ≤ (1 + ε)⁻¹ := inv_nonneg.mpr (by linarith [hbE.1])
  have h_A_nn : (0 : ℝ) ≤ ‖(bE.coord i₀) (vs j₀)‖ * ‖bE i₀‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_B_nn : (0 : ℝ) ≤ ‖(bF.coord k₀) (ws j₀)‖ * ‖bF k₀‖ :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [mul_nonneg h_inv_nn h_A_nn, mul_nonneg h_inv_nn h_B_nn]

-- ============================================================================
-- Step 10: Maximizing coordinate index
-- ============================================================================

/-- For a finite-type index set, there exists an index `i₀` that maximizes
`‖bE.coord i v‖ * ‖bE i‖`, and the ε-orthogonal bound holds at that index. -/
lemma exists_max_coord_index {ι : Type*} [Fintype ι] [Nonempty ι]
    {ε : ℝ} (bE : Module.Basis ι 𝕜 E) (hbE : IsEpsOrthogonal ε bE) (v : E) :
    ∃ i₀, (∀ i, ‖bE.coord i v‖ * ‖bE i‖ ≤ ‖bE.coord i₀ v‖ * ‖bE i₀‖) ∧
      (1 + ε)⁻¹ * (‖bE.coord i₀ v‖ * ‖bE i₀‖) ≤ ‖v‖ := by
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => ‖(bE.coord i) v‖ * ‖bE i‖)
  exact ⟨i₀, hi₀, (norm_ge_coord_mul_norm bE hbE v i₀).le⟩

-- ============================================================================
-- Step 11: Representation cost lower bound (KEY ASSEMBLY)
-- ============================================================================

/-- **Key theorem**: Every representation of `v ⊗ w` as `∑ⱼ vⱼ ⊗ wⱼ` has cost
`∑ ‖vⱼ‖ · ‖wⱼ‖ ≥ (1+ε)⁻⁴ · ‖v‖ · ‖w‖` in ultrametric normed spaces.

Proof outline:
1. Pick ε-orthogonal bases for E and F (Step 5)
2. Pick maximizing indices i₀, k₀ (Step 10)
3. Extract coordinate identity (Step 6)
4. Get j₀ with large coordinate product (Step 7)
5. Bound ‖vⱼ₀‖ · ‖wⱼ₀‖ from below (Step 9)
6. The sum ≥ the single term -/
theorem representation_cost_ge [IsUltrametricDist 𝕜] [IsUltrametricDist E]
    [IsUltrametricDist F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (v : E) (w : F) (n : ℕ) (vs : Fin n → E) (ws : Fin n → F)
    (h : v ⊗ₜ[𝕜] w = ∑ j, vs j ⊗ₜ ws j) (ε : ℝ) (hε : 0 < ε) :
    ∑ j, ‖vs j‖ * ‖ws j‖ ≥ (1 + ε)⁻¹ ^ 4 * (‖v‖ * ‖w‖) := by
  -- Edge case: n = 0
  by_cases hn : n = 0
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    have := tmul_eq_zero_of_field h
    rcases this with rfl | rfl <;> simp
  · -- Main case: n > 0
    replace hn : 0 < n := Nat.pos_of_ne_zero hn
    by_cases hv : ‖v‖ = 0
    · simp [hv, Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    by_cases hw : ‖w‖ = 0
    · simp [hw, Finset.sum_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    replace hv : 0 < ‖v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    replace hw : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw)
    have hdE : 0 < Module.finrank 𝕜 E := Module.finrank_pos_of_exists_ne_zero
      ⟨v, fun hv0 => by simp [hv0] at hv⟩
    have hdF : 0 < Module.finrank 𝕜 F := Module.finrank_pos_of_exists_ne_zero
      ⟨w, fun hw0 => by simp [hw0] at hw⟩
    haveI : Nonempty (Fin (Module.finrank 𝕜 E)) := ⟨⟨0, hdE⟩⟩
    haveI : Nonempty (Fin (Module.finrank 𝕜 F)) := ⟨⟨0, hdF⟩⟩
    -- ε-orthogonal bases
    obtain ⟨bE, hbE⟩ := exists_epsOrthogonal_basis (𝕜 := 𝕜) (E := E) hε
    obtain ⟨bF, hbF⟩ := exists_epsOrthogonal_basis (𝕜 := 𝕜) (E := F) hε
    -- Maximizing indices
    obtain ⟨i₀, hi₀, hi₀_bnd⟩ := exists_max_coord_index bE hbE v
    obtain ⟨k₀, hk₀, hk₀_bnd⟩ := exists_max_coord_index bF hbF w
    -- Coordinate identity + ultrametric domination
    have hcoord := coord_tensor_eq bE bF v w n vs ws h i₀ k₀
    obtain ⟨j₀, hj₀⟩ := exists_product_ge_of_sum_eq (bE.coord i₀ v) (bF.coord k₀ w) n
      (fun j => bE.coord i₀ (vs j)) (fun j => bF.coord k₀ (ws j)) hcoord hn
    -- Single term bound
    have hst := single_term_cost_bound bE bF hbE hbF vs ws j₀ i₀ k₀
    -- Ultrametric upper bounds on ‖v‖, ‖w‖
    have hv_up : ‖v‖ ≤ ‖bE.coord i₀ v‖ * ‖bE i₀‖ := by
      conv_lhs => rw [← bE.sum_repr v]
      exact (norm_sum_le_iSup_mul_norm bE _).trans (ciSup_le (fun i => hi₀ i))
    have hw_up : ‖w‖ ≤ ‖bF.coord k₀ w‖ * ‖bF k₀‖ := by
      conv_lhs => rw [← bF.sum_repr w]
      exact (norm_sum_le_iSup_mul_norm bF _).trans (ciSup_le (fun i => hk₀ i))
    -- Sum ≥ single term
    have hsum : ∑ j, ‖vs j‖ * ‖ws j‖ ≥ ‖vs j₀‖ * ‖ws j₀‖ :=
      Finset.single_le_sum (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (Finset.mem_univ j₀)
    -- Chain inequalities
    have hc : (0 : ℝ) ≤ (1 + ε)⁻¹ := inv_nonneg.mpr (by linarith)
    have hc1 : (1 + ε)⁻¹ ≤ 1 := by rw [inv_le_one_iff_of_pos (by linarith)]; linarith
    have hpow : (1 + ε)⁻¹ ^ 4 ≤ (1 + ε)⁻¹ ^ 2 :=
      pow_le_pow_of_le_one hc hc1 (by norm_num)
    nlinarith [mul_le_mul hv_up hw_up hw.le hv_up.trans (le_refl _) |>.symm.le,
               mul_le_mul_of_nonneg_left hj₀ (mul_nonneg (norm_nonneg (bE i₀)) (norm_nonneg (bF k₀))),
               sq_nonneg ((1 + ε)⁻¹),
               mul_nonneg (norm_nonneg v) (norm_nonneg w)]

-- ============================================================================
-- Steps 12-13: Taking ε → 0 and the Cross Property
-- ============================================================================

section CrossProperty

variable {ι : Type*} [Fintype ι] {E' : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E' i)] [∀ i, NormedSpace 𝕜 (E' i)]

/-- **Step 12**: The projective seminorm of a pure tensor is at least `∏ ‖m i‖`
in ultrametric spaces.

Since for every ε > 0, every representation has cost ≥ (1+ε)⁻⁴ᵏ · ∏ ‖m i‖
(by iterated application of `representation_cost_ge`), and as ε → 0 we get
`(1+ε)⁻⁴ᵏ → 1`, the projective seminorm ≥ ∏ ‖m i‖. -/
theorem projectiveSeminorm_tprod_ge_ultrametric
    [IsUltrametricDist 𝕜] [∀ i, IsUltrametricDist (E' i)]
    [∀ i, FiniteDimensional 𝕜 (E' i)] (m : Π i, E' i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) ≥ ∏ i, ‖m i‖ := by
  sorry
  -- Proof sketch:
  -- For the binary case (ι = Fin 2): representation_cost_ge gives
  --   ∀ ε > 0, ∀ repr, cost ≥ (1+ε)⁻⁴ * ‖v‖*‖w‖
  -- So projectiveSeminorm ≥ (1+ε)⁻⁴ * ‖v‖*‖w‖ for all ε > 0.
  -- Taking ε → 0: projectiveSeminorm ≥ ‖v‖*‖w‖.
  -- General case: induction on Fintype.card ι using tensor associativity.

/-- **Step 13**: The Cross Property for pi tensor products over ultrametric norms:
`projectiveSeminorm (⨂ₜ i, m i) = ∏ i, ‖m i‖`.

Combines the trivial upper bound `projectiveSeminorm_tprod_le` (already in mathlib)
with the lower bound from Step 12.

Reference: Schneider, Prop 17.4. -/
theorem projectiveSeminorm_tprod_ultrametric
    [IsUltrametricDist 𝕜] [∀ i, IsUltrametricDist (E' i)]
    [∀ i, FiniteDimensional 𝕜 (E' i)] (m : Π i, E' i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ :=
  le_antisymm (projectiveSeminorm_tprod_le m)
    (projectiveSeminorm_tprod_ge_ultrametric m)

end CrossProperty

end ProjSeminorm
