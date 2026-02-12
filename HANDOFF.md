# HANDOFF: Projective Seminorm Multiplicativity on Pure Tensors

## The Problem

**Source**: Email from David Gross (see `dgemail.txt` in this directory)

**PR**: https://github.com/leanprover-community/mathlib4/pull/33969

**Question**: Can the `h_bidual` hypothesis be removed from this theorem?

```lean
theorem projectiveSeminorm_tprod_of_bidual_iso
    (m : Π i, E i)
    (h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖) :
    ‖⨂ₜ[𝕜] i, m i‖ = ∏ i, ‖m i‖
```

In words: is the projective tensor seminorm always multiplicative on pure tensors,
or does it require that each factor embeds isometrically into its bidual?

**Stakes**: If proved unconditionally, David & Davood Haji Taghi Tehrani will clean it up and PR to mathlib.
If a counterexample is found, that's equally valuable.

---

## Mathematical Background

### The Projective Seminorm

For a finite family of seminormed spaces `{E_i}` over a nontrivially normed field `𝕜`,
the projective seminorm on `⨂[𝕜] i, E i` is:

```
π(x) = inf { ∑_j ∏_i ‖m_j(i)‖ : x = ∑_j ⨂_i m_j(i) }
```

The infimum is over ALL representations of `x` as a sum of pure tensors.

### What's Known

**Upper bound** (trivial, already in mathlib):
```
π(⨂ m_i) ≤ ∏ ‖m_i‖
```
Proof: take the 1-term representation.

**Lower bound with h_bidual** (PR #33969):
```
h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖
⊢ π(⨂ m_i) ≥ ∏ ‖m_i‖
```
Proof sketch: For each `i`, use norming sequences `g_i^(n)` in `E_i*` with
`‖g_i^(n)(m_i)‖ / ‖g_i^(n)‖ → ‖m_i‖` (guaranteed by `h_bidual`).
Evaluate `dualDistrib(⨂ g_i^(n))` on any representation of the tensor.
The multilinear evaluation gives a lower bound. Take limits.

**Over ℝ/ℂ**: `h_bidual` is automatic because Hahn-Banach gives isometric bidual embedding
(`inclusionInDoubleDualLi` is a `LinearIsometry` for `RCLike` fields).

**Over non-archimedean fields**: Schneider's Prop 17.4 proves multiplicativity for the
ultrametric "max" projective norm (different definition!), using d-orthogonal bases.

### The Open Question

Over a general `NontriviallyNormedField` (which includes non-archimedean fields like `ℚ_p`),
is `π(⨂ m_i) = ∏ ‖m_i‖` true WITHOUT `h_bidual`?

---

## Detailed Mathematical Analysis

### Why the Direct Algebraic Approach Almost Works (But Doesn't)

**Binary case**: `E ⊗ F`, pure tensor `v ⊗ w = ∑_j v_j ⊗ w_j`.

**Step 1**: Choose a maximal linearly independent subset of `{w_j}`.
Say `w_1,...,w_s` are independent. The dependent ones can be written
`w_j = ∑_k a_{jk} w_k` for `j > s`.

**Step 2**: Combine terms:
```
∑_j v_j ⊗ w_j = ∑_{k=1}^s (v_k + ∑_{j>s} a_{jk} v_j) ⊗ w_k
```

**Step 3**: Since `w_1,...,w_s` are linearly independent in the tensor product,
and `v ⊗ w = ∑_k u_k ⊗ w_k` with `u_k = v_k + ∑_{j>s} a_{jk} v_j`:
- `w ∈ span(w_1,...,w_s)`, say `w = ∑_k c_k w_k`
- `u_k = c_k v` for each `k`

(This uses the standard algebraic fact: in `E ⊗_K F`, if `∑ e_j ⊗ f_j = 0`
and `f_j` are linearly independent, then `e_j = 0` for all `j`.)

**Step 4**: Now `v_k + ∑_{j>s} a_{jk} v_j = c_k v`, so:
```
‖c_k v‖ = ‖v_k + ∑_{j>s} a_{jk} v_j‖ ≤ ‖v_k‖ + ∑_{j>s} |a_{jk}| ‖v_j‖
```

This gives `|c_k| · ‖v‖ ≤ ∑_j |a_{jk}| · ‖v_j‖` (where `a_{jk} = δ_{jk}` for `j ≤ s`).

**Step 5**: Chain of inequalities:
```
‖v‖ · ‖w‖ = ‖v‖ · ‖∑_k c_k w_k‖
           ≤ ‖v‖ · ∑_k |c_k| · ‖w_k‖           [triangle inequality on w]
           ≤ ∑_k (∑_j |a_{jk}| · ‖v_j‖) · ‖w_k‖ [from Step 4]
           = ∑_j ‖v_j‖ · (∑_k |a_{jk}| · ‖w_k‖) [swap sums]
           ≥ ∑_j ‖v_j‖ · ‖∑_k a_{jk} w_k‖       [triangle inequality — WRONG DIRECTION!]
           = ∑_j ‖v_j‖ · ‖w_j‖
```

**THE PROBLEM**: The last step goes the wrong way! We have:
```
∑_j ‖v_j‖ · (∑_k |a_{jk}| · ‖w_k‖)  ≥  ∑_j ‖v_j‖ · ‖w_j‖
```
(since `∑_k |a_{jk}| · ‖w_k‖ ≥ ‖∑_k a_{jk} w_k‖ = ‖w_j‖`)

But we proved `‖v‖ · ‖w‖ ≤ ∑_j ‖v_j‖ · (∑_k |a_{jk}| · ‖w_k‖)`, and we WANT
`‖v‖ · ‖w‖ ≤ ∑_j ‖v_j‖ · ‖w_j‖`. The intermediate quantity is BIGGER than both,
so no conclusion follows.

**In ultrametric spaces**: The triangle inequality `‖∑ a_k w_k‖ ≤ max |a_k| ‖w_k‖`
is nearly tight (with d-orthogonal bases, the defect is at most `1/d`), so both
inequalities become approximate equalities and the proof closes by taking `d → 1`.

**In archimedean spaces**: The triangle inequality can be arbitrarily lossy.

### Why the Duality Approach Needs h_bidual

For any `f_i ∈ E_i*` with `‖f_i‖ ≤ 1`:
```
|∏_i f_i(m_i)| = |dualDistrib(⨂ f_i)(⨂ m_i)| ≤ ‖dualDistrib(⨂ f_i)‖ · π(⨂ m_i)
```
and `‖dualDistrib(⨂ f_i)‖ ≤ ∏ ‖f_i‖ ≤ 1`, so:
```
∏_i |f_i(m_i)| ≤ π(⨂ m_i)
```
Taking sup over `f_i` with `‖f_i‖ ≤ 1`:
```
∏_i sup_{‖f_i‖≤1} |f_i(m_i)| ≤ π(⨂ m_i)
```
But `sup_{‖f‖≤1} |f(x)| = ‖inclusionInDoubleDual(x)‖`, which equals `‖x‖` only when
the bidual embedding is isometric. So we get:
```
∏_i ‖inclusionInDoubleDual(m_i)‖ ≤ π(⨂ m_i) ≤ ∏_i ‖m_i‖
```

The left side equals `∏ ‖m_i‖` iff `h_bidual` holds.

### A Slightly Better Duality Bound

By "projecting out" one factor at a time: for each `i₀`, apply functionals at all
indices `i ≠ i₀` and use the norm directly at `i₀`:
```
π(⨂ m_i) ≥ ‖m_{i₀}‖ · ∏_{i≠i₀} ‖m_i‖_bidual
```
This is better than `∏ ‖m_i‖_bidual` but still needs bidual isometry at all-but-one indices.

### Counterexample Candidates

**For non-archimedean fields**: There exist Banach spaces over `ℚ_p` with trivial dual
(e.g., certain `ℓ^p` spaces with `0 < p < 1` over non-archimedean fields, or pathological
completions). If `E* = {0}`, then `‖x‖_bidual = 0` for all `x`, and the duality lower
bound is `0`. Whether the projective norm can actually be strictly less than the product
norm in such cases is the key question.

**Note**: For finite-dimensional spaces over any field, the bidual embedding IS isometric
(Hahn-Banach holds in finite dimensions). So a counterexample must be infinite-dimensional.

**Specific candidate**: Let `K = ℚ_p`. Let `E` be the completion of `c_{00}(ℕ, K)` under
the norm `‖(a_n)‖ = (∑_n |a_n|_p^{1/2})^2`. This space has very few continuous linear
functionals. If we can find `v, w ∈ E` and a representation `v ⊗ w = ∑ v_j ⊗ w_j` with
`∑ ‖v_j‖ · ‖w_j‖ < ‖v‖ · ‖w‖`, that's our counterexample.

---

## Existing Mathlib API (as of v4.x, before PR #33969)

### PiTensorProduct.ProjectiveSeminorm.lean
```lean
-- Definitions
def projectiveSeminormAux : FreeAddMonoid (𝕜 × Π i, E i) → ℝ
noncomputable def projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i)

-- Key theorems
theorem projectiveSeminorm_apply (x) :
    projectiveSeminorm x = iInf (fun (p : lifts x) ↦ projectiveSeminormAux p.1)
theorem projectiveSeminorm_tprod_le (m : Π i, E i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖
theorem norm_eval_le_projectiveSeminorm (x) (G) (f : ContinuousMultilinearMap 𝕜 E G) :
    ‖lift f.toMultilinearMap x‖ ≤ projectiveSeminorm x * ‖f‖
```

### PiTensorProduct.InjectiveSeminorm.lean
```lean
-- The norm instance on ⨂[𝕜] i, E i uses injectiveSeminorm (NOT projectiveSeminorm!)
-- So ‖x‖ for x : ⨂[𝕜] i, E i is injectiveSeminorm x

-- Key definitions
noncomputable def injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i)
instance : SeminormedAddCommGroup (⨂[𝕜] i, E i)  -- uses injectiveSeminorm
noncomputable def liftEquiv : ContinuousMultilinearMap 𝕜 E F ≃ₗ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F
noncomputable def liftIsometry : ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F
noncomputable def tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i)
noncomputable def mapL (f : Π i, E i →L[𝕜] E' i) : (⨂[𝕜] i, E i) →L[𝕜] (⨂[𝕜] i, E' i)

-- Key theorems
theorem injectiveSeminorm_le_projectiveSeminorm :
    injectiveSeminorm ≤ projectiveSeminorm (𝕜 := 𝕜) (E := E)
theorem norm_eval_le_injectiveSeminorm (x) (f : ContinuousMultilinearMap 𝕜 E F) :
    ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * injectiveSeminorm x
theorem injectiveSeminorm_tprod_le (m : Π i, E i) :
    injectiveSeminorm (⨂ₜ[𝕜] i, m i) ≤ ∏ i, ‖m i‖
```

**CRITICAL**: In current mathlib, `‖x‖` for `x : ⨂[𝕜] i, E i` is `injectiveSeminorm x`.
PR #33969 proves `injectiveSeminorm = projectiveSeminorm` and switches the instance.
Until then, you MUST use `projectiveSeminorm x` explicitly.

### PiTensorProduct.Dual.lean (algebraic)
```lean
noncomputable def dualDistrib [Finite ι] :
    (⨂[R] i, Dual R (M i)) →ₗ[R] Dual R (⨂[R] i, M i)

@[simp] theorem dualDistrib_apply [Fintype ι]
    (f : Π i, Dual R (M i)) (m : Π i, M i) :
    dualDistrib (⨂ₜ[R] i, f i) (⨂ₜ[R] i, m i) = ∏ i, (f i) (m i)

-- Also: constantBaseRingEquiv, dualDistribEquiv (for free finite modules)
```

### NormedSpace.Dual.lean
```lean
def inclusionInDoubleDual : E →L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)
-- inclusionInDoubleDual 𝕜 E x f = f x

theorem inclusionInDoubleDual_norm_le : ‖inclusionInDoubleDual 𝕜 E‖ ≤ 1
theorem double_dual_bound (x : E) : ‖(inclusionInDoubleDual 𝕜 E) x‖ ≤ ‖x‖

-- For RCLike fields only:
def inclusionInDoubleDualLi : E →ₗᵢ[𝕜] StrongDual 𝕜 (StrongDual 𝕜 E)
-- This is a LinearIsometry, so ‖inclusionInDoubleDualLi x‖ = ‖x‖
```

### HahnBanach.lean (RCLike only)
```lean
-- exists_dual_vector : for nonzero x, ∃ g with ‖g‖ = 1 and g x = ‖x‖
-- exists_extension_norm_eq : norm-preserving extension from subspaces
```

---

## Step-by-Step Implementation Plan

### Prerequisites: New Lean 4 Project Setup

```bash
# Create a new Lean 4 project
lake init ProjSeminorm math
cd ProjSeminorm

# Edit lakefile to use the correct mathlib version
# (Match whatever mathlib version has the APIs listed above)
lake update
lake exe cache get  # Get pre-built mathlib oleans
```

### Step 1: Basic Setup (10 LOC)

Create `ProjSeminorm/Basic.lean`:

```lean
import Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.LinearAlgebra.PiTensorProduct.Dual
import Mathlib.Topology.Algebra.InfiniteSum.Order

open scoped TensorProduct BigOperators

namespace ProjSeminorm

-- Universe variables matching mathlib conventions
universe uι u𝕜 uE

variable {ι : Type uι} [Fintype ι]
variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : ι → Type uE} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

end ProjSeminorm
```

**Verify**: `lake build ProjSeminorm`

### Step 2: `isLUB_opNorm` and `exists_norming_sequence` (40 LOC)

These are needed to construct the norming sequences used in the lower bound proof.
They are NOT in current mathlib but are added by PR #33969.

```lean
-- In ProjSeminorm/NormingSeq.lean

import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Order.Monotone

open Filter Topology

namespace ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The operator norm is the LUB of ‖f x‖ / ‖x‖. -/
theorem isLUB_opNorm (f : E →L[𝕜] F) :
    IsLUB (Set.range fun x => ‖f x‖ / ‖x‖) ‖f‖ := by
  constructor
  · -- Upper bound: from ratio_le_opNorm
    rintro _ ⟨x, rfl⟩
    exact div_le_of_le_mul₀ (norm_nonneg _) (norm_nonneg _)
      (f.le_opNorm x) -- or use ratio_le_opNorm
  · -- Least upper bound: from opNorm_le_bound'
    intro M hM
    apply opNorm_le_bound' f
    · exact le_csInf ⟨0, ⟨0, by simp⟩⟩ (fun _ ⟨x, hx⟩ => hx ▸ div_nonneg (norm_nonneg _) (norm_nonneg _))
    · intro x hx
      have := hM ⟨x, rfl⟩  -- M ≥ ‖f x‖ / ‖x‖
      rwa [div_le_iff₀ (norm_pos_iff.mpr hx)] at this
    sorry -- may need adjustment based on exact API

/-- There exists a sequence achieving the operator norm. -/
theorem exists_norming_sequence (f : E →L[𝕜] F) :
    ∃ u : ℕ → E, Tendsto (fun n => ‖f (u n)‖ / ‖u n‖) atTop (nhds ‖f‖) := by
  -- Use IsLUB.exists_seq_monotone_tendsto from Mathlib
  obtain ⟨seq, _, hseq⟩ := (isLUB_opNorm f).exists_seq_monotone_tendsto
  -- seq : ℕ → ℝ with Tendsto seq atTop (nhds ‖f‖)
  -- Need to lift back to actual elements of E
  sorry -- The lifting from ℝ values back to E elements needs care

end ContinuousLinearMap
```

**Note**: The exact proof will need tuning. Key mathlib lemmas to search for:
- `IsLUB.exists_seq_monotone_tendsto`
- `ContinuousLinearMap.opNorm_le_bound'`
- `ContinuousLinearMap.ratio_le_opNorm`
- `Real.iSup_eq` or `csInf` characterizations

The lifting from the sequence of reals back to actual elements is the tricky part.
You might need `exists_seq_tendsto_sSup` or construct the sequence via `choose`.

### Step 3: Continuous `dualDistribL` (40 LOC)

The algebraic `dualDistrib` needs to be made continuous and normed.

```lean
-- In ProjSeminorm/DualDistribL.lean

import ProjSeminorm.Basic
import ProjSeminorm.NormingSeq

open PiTensorProduct

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- The projective seminorm on ⨂[𝕜] i, 𝕜 equals the absolute value via constantBaseRingEquiv.
    Specifically, ‖⨂ₜ c_i‖_proj = ∏ |c_i|. -/
theorem projectiveSeminorm_field_tprod (c : ι → 𝕜) :
    projectiveSeminorm (⨂ₜ[𝕜] i, c i) = ∏ i, ‖c i‖ := by
  -- Upper bound from projectiveSeminorm_tprod_le
  -- Lower bound: use constantBaseRingEquiv and the fact that ⨂[𝕜] i, 𝕜 ≅ 𝕜
  sorry

/-- dualDistrib as a continuous linear map, using the projective-to-injective norm comparison. -/
noncomputable def dualDistribL :
    (⨂[𝕜] i, NormedSpace.StrongDual 𝕜 (E i)) →L[𝕜]
    NormedSpace.StrongDual 𝕜 (⨂[𝕜] i, E i) := by
  -- Use mapL to get continuity, compose with constantBaseRingEquiv
  sorry

theorem dualDistribL_tprod_apply
    (f : Π i, NormedSpace.StrongDual 𝕜 (E i)) (m : Π i, E i) :
    dualDistribL (⨂ₜ[𝕜] i, f i) (⨂ₜ[𝕜] i, m i) = ∏ i, f i (m i) := by
  sorry

theorem norm_dualDistribL_tprod_le (f : Π i, NormedSpace.StrongDual 𝕜 (E i)) :
    ‖dualDistribL (⨂ₜ[𝕜] i, f i)‖ ≤ ∏ i, ‖f i‖ := by
  sorry

end ProjSeminorm
```

### Step 4: The Main Theorem with h_bidual (30 LOC)

```lean
-- In ProjSeminorm/WithBidual.lean

import ProjSeminorm.DualDistribL

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
  -- Lower bound:
  -- For each i, get norming sequence g_i^(n) with ‖g_i^(n)(m_i)‖/‖g_i^(n)‖ → ‖m_i‖
  -- (here h_bidual is used: it ensures the norming sequences achieve ‖m_i‖, not just ‖m_i‖_bidual)
  -- Then ∏_i ‖g_i^(n)(m_i)‖/‖g_i^(n)‖ → ∏_i ‖m_i‖
  -- And ∏_i ‖g_i^(n)(m_i)‖/‖g_i^(n)‖ ≤ projectiveSeminorm(⨂ m_i) for each n
  -- (by dualDistribL evaluation + norm estimate on each representation)
  sorry

end ProjSeminorm
```

### Step 5: RCLike Corollary (15 LOC)

```lean
-- In ProjSeminorm/RCLike.lean

import ProjSeminorm.WithBidual
import Mathlib.Analysis.RCLike.Basic

open PiTensorProduct NormedSpace

namespace ProjSeminorm

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : ι → Type*} [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]

/-- Over ℝ or ℂ, the projective seminorm is unconditionally multiplicative on pure tensors. -/
theorem projectiveSeminorm_tprod (m : Π i, E i) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖ :=
  projectiveSeminorm_tprod_of_bidual_iso m
    (fun i => (inclusionInDoubleDualLi 𝕜 (E i)).norm_map (m i))

end ProjSeminorm
```

### Step 6: Direct Algebraic Attempt (50 LOC)

```lean
-- In ProjSeminorm/DirectApproach.lean

import ProjSeminorm.Basic

open PiTensorProduct

namespace ProjSeminorm

-- Key algebraic fact: in E ⊗ F, if ∑ e_j ⊗ f_j = 0 and f_j are linearly independent,
-- then e_j = 0 for all j.
-- In mathlib: look for `TensorProduct.eq_zero_of_linearIndependent` or similar

-- For the binary tensor product case:
-- If v ⊗ w = ∑ v_j ⊗ w_j and we choose a basis of span(w_j),
-- then coefficients of v are determined.

-- The attempt:
theorem projectiveSeminorm_tprod_ge_attempt
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
    (v : E) (w : F) :
    -- Using PiTensorProduct with ι = Fin 2 to match the general framework
    -- Or use TensorProduct directly
    True := by  -- placeholder
  -- The algebraic decomposition works:
  -- Given v ⊗ w = ∑ v_j ⊗ w_j with w_j linearly independent:
  --   w = ∑ c_k w_k and v_j = c_j v
  -- So ∑ ‖v_j‖·‖w_j‖ = ‖v‖ · ∑ |c_j|·‖w_j‖ ≥ ‖v‖·‖∑ c_j w_j‖ = ‖v‖·‖w‖
  --
  -- BUT: for linearly DEPENDENT w_j, reducing to independent form changes cost.
  -- The reduction ∑ v_j ⊗ w_j → ∑ u_k ⊗ w_k (fewer terms, w_k independent) satisfies
  -- u_k = v_k + ∑_{j>s} a_{jk} v_j, so ‖u_k‖ ≤ ‖v_k‖ + ∑|a_{jk}|‖v_j‖
  -- The cost of the reduced representation:
  --   ∑_k ‖u_k‖·‖w_k‖ ≤ ∑_k (‖v_k‖ + ∑_{j>s} |a_{jk}|‖v_j‖)·‖w_k‖
  -- This is NOT necessarily ≤ the original cost ∑_j ‖v_j‖·‖w_j‖
  -- because the dependent w_j's had their own cost contributions.
  --
  -- OBSTRUCTION: We cannot reduce to the independent case without potentially
  -- increasing the cost. The proof is stuck here.
  trivial

end ProjSeminorm
```

### Step 7: Counterexample Investigation (50 LOC)

```lean
-- In ProjSeminorm/Counterexample.lean

import ProjSeminorm.Basic

/-!
# Counterexample Investigation

## Question
Over a non-archimedean nontrivially normed field 𝕜, can we find
seminormed spaces E, F and elements v ∈ E, w ∈ F such that
π(v ⊗ w) < ‖v‖ · ‖w‖?

## Analysis

### Finite-dimensional case
In finite dimensions, the bidual embedding IS isometric even over
non-archimedean fields (Hahn-Banach holds for finite-dimensional subspaces).
So no counterexample in finite dimensions.

### Infinite-dimensional case
Over ℚ_p, there exist Banach spaces with trivial (zero) continuous dual.
Example: Complete ℓ^p(ℕ, ℚ_p) for certain 0 < p < 1.

If E* = {0}, then:
- dualDistrib gives no lower bound (all evaluations are 0)
- But the projective norm is defined via infimum over representations,
  which is a purely metric-algebraic quantity
- The question becomes: can "spreading out" a pure tensor into a sum
  reduce the cost when the triangle inequality is very lossy?

### Key Insight
For the "sum" projective norm (∑ ‖v_j‖·‖w_j‖), having a poor dual
doesn't directly help — the infimum is taken over ALL representations,
not just those visible to the dual.

For the binary case with E = F and v = w = e₁ (a unit vector):
  e₁ ⊗ e₁ = (e₁ + εe₂) ⊗ e₁ - εe₂ ⊗ e₁  [cost = (1+ε)·1 + ε·1 = 1+2ε > 1]
  e₁ ⊗ e₁ = ½(e₁+e₂) ⊗ (e₁+e₂) + ½(e₁-e₂) ⊗ (e₁-e₂) - e₂ ⊗ e₂
    [in ℓ²: cost = ½√2·√2 + ½√2·√2 + 1·1 = 1+1+1 = 3 > 1]

These naive attempts all INCREASE cost. A counterexample (if it exists)
would need a very clever representation in a very specific space.

## Formalization Idea
Rather than constructing a counterexample in Lean 4 (which would require
formalizing non-archimedean Banach spaces), it may be more productive to:
1. Prove the result unconditionally (if possible), or
2. Prove impossibility of certain proof strategies, or
3. Settle the question computationally (e.g., Python script searching for
   counterexamples in finite-dimensional approximations)
-/

-- Placeholder for any formal counterexample work
-- This file may remain as documentation only
```

### Step 8: Summary and Report

After completing Steps 1-7, write a summary:

1. **What compiles**: Steps 1, 5 (assuming 2-4 work), and documentation
2. **What has sorries**: Steps 2-4 (the core proof), Step 6 (direct approach obstruction)
3. **Mathematical conclusion**: `h_bidual` is likely necessary for general fields,
   but we don't have a formal counterexample. For ℝ/ℂ it's unconditional.
4. **Recommendation to David**: The RCLike version (Step 5) is the "clean" result
   for mathlib. The general version with `h_bidual` is the right abstraction level.

---

## Build Commands

```bash
lake build ProjSeminorm 2>&1 | tail -40    # Build whole project
lake env lean ProjSeminorm/Basic.lean 2>&1  # Check single file
```

## Search Commands for Lean LSP

When stuck on a proof, use these searches:

```
lean_loogle: "projectiveSeminorm"
lean_loogle: "_ ⊗ _"   →  ‖ _ ‖
lean_leansearch: "projective tensor norm multiplicative on elementary tensors"
lean_leansearch: "operator norm is supremum of ratios"
lean_local_search: "projectiveSeminorm"
lean_local_search: "inclusionInDoubleDual"
lean_local_search: "dualDistrib"
lean_local_search: "exists_norming_sequence"
```

## References

1. **PR #33969**: https://github.com/leanprover-community/mathlib4/pull/33969
2. **Schneider's notes**: https://ivv5hpp.uni-muenster.de/u/pschnei/publ/lectnotes/nfa.pdf
   - Lemma 17.3: d-orthogonal basis technique for lower bound
   - Prop 17.4: Multiplicativity of ultrametric projective norm
3. **Current mathlib file**: `Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean`
4. **The TBD item**: Lines 32-34 of the above file

---

## Session Log

### Session 1 (2026-02-08): Project scaffolding & issue tracking

**What was done:**
- Initialized `bd` (beads) issue tracker for the project
- Created epic `ProjSeminorm-dtv` with 22 sub-issues covering all 8 steps at high granularity
- Full dependency chain established: Steps 1→2→3→4→5 (critical path), then 6 & 7 branch in parallel, Step 8 merges all
- Installed `lean-lsp-mcp` (Lean 4 MCP server) for LSP integration in Claude Code — config in `.mcp.json`
- Removed GitHub Actions CI workflows (lean_action_ci, update, create-release) to stop email spam

**Current state:**
- `ProjSeminorm/Basic.lean` exists but is still the `lake init` placeholder (`def hello := "world"`)
- No implementation work started yet — all 22 issues are `open`
- First actionable issue: `ProjSeminorm-dtv.1` (create Basic.lean with proper imports/variables)

**Next session should:**
1. `bd ready` to see available work
2. Start with `ProjSeminorm-dtv.3`: create NormingSeq.lean
3. Proceed through the dependency chain (Steps 2→3→4→5)
4. Restart Claude Code first to activate the lean-lsp MCP server

### Session 2 (2026-02-08): Step 1 complete

**What was done:**
- Replaced `Basic.lean` placeholder with proper imports and variable declarations
- All 4 imports, namespace, universe variables (uι, u𝕜, uE), standard variable block
- Build verified: clean (2312 jobs, 0 errors)
- Closed `ProjSeminorm-dtv.1` and `ProjSeminorm-dtv.2`

**Current state:**
- Step 1 complete. 2 of 22 issues closed.
- Next actionable: `ProjSeminorm-dtv.3` (create NormingSeq.lean with imports/variables)

**Next session should:**
1. `bd ready` to see available work
2. Start with `ProjSeminorm-dtv.4`: prove `isLUB_opNorm`
3. Then `ProjSeminorm-dtv.5`: prove `exists_norming_sequence`

### Session 3 (2026-02-08): Step 2 scaffold — NormingSeq.lean

**What was done:**
- Created `ProjSeminorm/NormingSeq.lean` with imports, variables, and sorry'd stubs
- Two theorems scaffolded: `isLUB_opNorm` and `exists_norming_sequence`
- Imports: `InjectiveSeminorm` (transitive CLM norm API) + `Topology.Order.IsLUB`
- Build verified: clean (2312 jobs, 0 errors, 2 sorry warnings only)
- Closed `ProjSeminorm-dtv.3`

**Current state:**
- Steps 1-2 scaffolded. 3 of 22 issues closed.
- Next actionable: `ProjSeminorm-dtv.4` (prove `isLUB_opNorm`)

**Next session should:**
1. `bd ready` to see available work
2. Start with `ProjSeminorm-dtv.5`: prove `exists_norming_sequence`

### Session 4 (2026-02-08): Prove isLUB_opNorm

**What was done:**
- Proved `isLUB_opNorm` fully (no sorry) in `NormingSeq.lean`
- Proof structure:
  - Upper bound: `div_le_of_le_mul₀` + `le_opNorm`
  - Least bound: `opNorm_le_bound` + case split on `‖x‖ = 0` (calc chain) vs `‖x‖ ≠ 0` (`div_le_iff₀`)
- Build verified: clean (0 errors, 1 sorry warning for `exists_norming_sequence`)
- Closed `ProjSeminorm-dtv.4`

**Current state:**
- 4 of 22 issues closed. `isLUB_opNorm` fully proven.
- Next actionable: `ProjSeminorm-dtv.5` (prove `exists_norming_sequence`)

**Next session should:**
1. `bd ready` to see available work
2. Start with `ProjSeminorm-dtv.7`: create DualDistribL.lean (Step 3)

### Session 5 (2026-02-08): Step 2 complete — NormingSeq.lean sorry-free

**What was done:**
- Proved `exists_norming_sequence` fully (no sorry) in `NormingSeq.lean`
- Proof: `IsLUB.exists_seq_monotone_tendsto` + `choose` to lift real-valued witnesses back to E
- NormingSeq.lean is now completely sorry-free (0 errors, 0 warnings)
- Closed `ProjSeminorm-dtv.5` and `ProjSeminorm-dtv.6`

**Current state:**
- Step 2 fully complete. 6 of 22 issues closed.
- Next actionable: `ProjSeminorm-dtv.7` (create DualDistribL.lean — Step 3)

**Next session should:**
1. `bd ready` to see available work
2. Start with `ProjSeminorm-dtv.8`: prove `projectiveSeminorm_field_tprod`

### Session 6 (2026-02-08): Step 3 scaffold — DualDistribL.lean

**What was done:**
- Created `ProjSeminorm/DualDistribL.lean` with imports and 4 sorry'd declarations:
  - `projectiveSeminorm_field_tprod` (scalar tensor norm = product of absolute values)
  - `dualDistribL` (continuous version of algebraic `dualDistrib`)
  - `dualDistribL_tprod_apply` (evaluation on pure tensors)
  - `norm_dualDistribL_tprod_le` (norm bound)
- Uses `StrongDual 𝕜 (E i)` for continuous duals (not `NormedSpace.Dual`)
- Build verified: clean
- Closed `ProjSeminorm-dtv.7`

**Current state:**
- Step 3 scaffolded. 7 of 22 issues closed.
- Next actionable: `ProjSeminorm-dtv.8` (prove `projectiveSeminorm_field_tprod`)

**Next session should:**
1. `bd ready` to see available work
2. Prove `projectiveSeminorm_field_tprod` using `constantBaseRingEquiv`

### Session 7 (2026-02-08): Prove projectiveSeminorm_field_tprod

**What was done:**
- Proved `projectiveSeminorm_field_tprod` (no sorry) in `DualDistribL.lean`
- Proof: `le_antisymm` with upper bound from `projectiveSeminorm_tprod_le` and lower bound via `norm_eval_le_projectiveSeminorm` applied to `ContinuousMultilinearMap.mkPiAlgebra 𝕜 ι 𝕜` (multiplication), then `simp` with `lift.tprod`, `mkPiAlgebra_apply`, `norm_mkPiAlgebra`, `norm_prod` + `linarith`
- Build verified: clean (2312 jobs, 0 errors)
- Closed `ProjSeminorm-dtv.8`

**Current state:**
- 8 of 22 issues closed. `projectiveSeminorm_field_tprod` fully proven.
- Next actionable: `ProjSeminorm-dtv.9` (define `dualDistribL` as continuous linear map)

**Next session should:**
1. `bd ready` to see available work
2. Define `dualDistribL` — the continuous version of algebraic `dualDistrib`

### Session 8 (2026-02-08): Step 3 complete — DualDistribL.lean sorry-free

**What was done:**
- Defined `dualDistribL` as a continuous linear map via `liftEquiv` + `compContinuousLinearMapLRight` + `mkPiAlgebra`
- Proved `dualDistribL_tprod_apply` (evaluation on pure tensors = product of evaluations)
- Proved `norm_dualDistribL_tprod_le` (norm bound ≤ product of norms, via `liftIsometry` + `norm_compContinuousLinearMap_le` + `norm_mkPiAlgebra`)
- DualDistribL.lean is now completely sorry-free (0 errors, 0 warnings)
- Closed `ProjSeminorm-dtv.9`, `ProjSeminorm-dtv.10`, `ProjSeminorm-dtv.11`

**Current state:**
- Step 3 fully complete. 11 of 22 issues closed.
- Next actionable: `ProjSeminorm-dtv.12` (Step 4: create WithBidual.lean)

**Build fix:** `DualDistribL.lean` was never compiled by `lake build` — missing `open scoped TensorProduct BigOperators` and not registered in root module. Fixed both. Verified 0 sorries, 0 custom axioms (only propext/Classical.choice/Quot.sound).

**Next session should:**
1. `bd ready` to see available work
2. Start Step 4: prove `projectiveSeminorm_tprod_of_bidual_iso` using norming sequences + dualDistribL

### Session 9 (2026-02-08): Step 4 outer framework — 1 sorry remains

**What was done:**
- Closed `ProjSeminorm-dtv.12` (build verification)
- Built the outer proof framework for `projectiveSeminorm_tprod_of_bidual_iso`:
  - Norming sequences via `ContinuousLinearMap.exists_norming_sequence` + `choose`
  - Product convergence via `tendsto_finset_prod`
  - Limit passage via `le_of_tendsto'`
- One sorry remains: the `hle` step (each product term ≤ projectiveSeminorm)
- Build clean: 2315 jobs, 0 errors, 1 sorry warning

**Key learnings for filling the sorry (documented in file docstring):**
- `Finset.prod_div_distrib` requires `CommGroup` — `ℝ` is NOT a `CommGroup` under ×.
  Use `simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_inv_distrib]`
  then `mul_inv_le_iff₀` instead.
- `map_nonneg` fails for `projectiveSeminorm` (no `Preorder` on tensor product).
  Use `apply_nonneg projectiveSeminorm` or `(projectiveSeminorm ...).nonneg'`.
- `norm_pos_iff` for `StrongDual` needs type annotation due to `hasOpNorm` vs
  `NormedAddGroup.toNorm` mismatch.
- The calc chain itself works: `norm_prod` → `dualDistribL_tprod_apply` →
  `le_opNorm` → `injectiveSeminorm_le_projectiveSeminorm` →
  `norm_dualDistribL_tprod_le` → `mul_comm`.
- `inclusionInDoubleDual_apply` does NOT exist. Use `NormedSpace.dual_def` instead
  (`inclusionInDoubleDual 𝕜 E x f = f x`, proven by `rfl`).
- `gcongr` handles the monotonicity steps in the calc chain.

**Current state:**
- 12 of 22 issues closed. `ProjSeminorm-dtv.13` in progress.
- **BUILD HAS ERRORS** — WithBidual.lean has partial hle proof that doesn't compile.

**Next session should:**
1. Fix the `norm_pos_iff` type mismatch for StrongDual. The zero instance on
   `StrongDual 𝕜 (E i)` is `ContinuousLinearMap.zero`, but `norm_pos_iff`
   expects `SubtractionMonoid...zero`. Do NOT use `norm_pos_iff.mpr (h i)`.
   Instead try: `norm_ne_zero_iff.mpr (h i) |>.bot_lt` or
   `lt_of_le_of_ne (norm_nonneg _) (Ne.symm (norm_ne_zero_iff.mpr (h i)))`.
   Or just `by positivity` or `by simp [h i]`.
2. Once hle compiles, close ProjSeminorm-dtv.13.1, .13.2, .13.3, and .13
3. Then proceed to Step 5 (RCLike corollary — should be ~5 LOC)

### Session 10 (2026-02-08): Step 4 complete — WithBidual.lean sorry-free

**What was done:**
- Fixed 3 build errors in WithBidual.lean, making it sorry-free:
  1. `norm_pos_iff` zero-instance diamond for `StrongDual`: solved with direct proof
     via `ContinuousLinearMap.opNorm_nonneg` + `le_opNorm` + `norm_le_zero_iff`
  2. `norm_prod` needed explicit `Finset.univ` argument
  3. `injectiveSeminorm_le_projectiveSeminorm` takes 1 arg (pointwise), not 2
- Build verified: 2315 jobs, 0 errors, 0 warnings
- Closed ProjSeminorm-dtv.13, .13.1, .13.2, .13.3

**Key learnings:**
- `ContinuousLinearMap.opNorm_zero_iff` requires `NormedAddCommGroup` (not `Seminormed`).
  For seminormed sources, prove `f = 0` manually: `ext x; le_opNorm` + `simp` + `norm_le_zero_iff`.
- `norm_prod` signature: `(s : Finset β) (f : β → α)` — must supply both args.
- `injectiveSeminorm_le_projectiveSeminorm` is `Seminorm`-level `≤`, unfolds pointwise with 1 arg.

**Current state:**
- Step 4 fully complete. 16 of 22 issues closed.
- Next actionable: `ProjSeminorm-dtv.14` (Step 5: create RCLike.lean)

**Next session should:**
1. `bd ready` to see available work
2. Create RCLike.lean with `projectiveSeminorm_tprod` (~5 LOC using `inclusionInDoubleDualLi`)

### Session 12 (2026-02-09): Step 6 complete — DirectApproach.lean

**What was done:**
- Created `ProjSeminorm/DirectApproach.lean` documenting the direct algebraic approach
- Module docstring covers the full 5-step approach, the wrong-direction triangle inequality
  obstruction, special cases (ultrametric vs archimedean), and conclusion
- Two formalized lemmas (no sorry):
  - `reduced_representation_cost_ge`: the step that DOES work (reduced independent repr)
  - `triangle_wrong_direction`: the step that FAILS (triangle inequality ≤ not ≥)
- Build verified: 2317 jobs, 0 errors, 0 warnings, 0 sorries
- Closed `ProjSeminorm-dtv.17` and `ProjSeminorm-dtv.18`

**Current state:**
- Steps 1-6 complete. 17 of 22 issues closed.
- Next actionable: `ProjSeminorm-dtv.19` (Step 7: Counterexample.lean) and
  `ProjSeminorm-dtv.20` (computational counterexample search)

**Next session should:**
1. `bd ready` to see available work
2. Create Counterexample.lean (Step 7) — investigation of counterexamples for general fields
3. Then Step 8: summary report + final build verification

### Session 12 continued (2026-02-09): Step 7 complete — Counterexample.lean

**What was done:**
- Literature search found: no counterexample exists in the literature, question is genuinely open
- Key insight: over spherically complete fields (including ℚ_p), Ingleton's theorem (1952)
  gives Hahn-Banach, so h_bidual is automatic. Only ℂ_p-type fields remain open.
- Created `ProjSeminorm/Counterexample.lean` documenting all findings
- Closed `ProjSeminorm-dtv.19` and `ProjSeminorm-dtv.20`

**Current state:**
- Steps 1-7 complete. 19 of 22 issues closed.
- Next actionable: Step 8 — summary report (`ProjSeminorm-dtv.21`) and
  final build verification (`ProjSeminorm-dtv.22`)

**Next session should:**
1. `bd ready` to see available work
2. Write summary report (Step 8) and do final build verification

---

## Step 8: Summary Report

### Project Status: COMPLETE

All 8 steps of the implementation plan are finished. The project builds cleanly
(2318 jobs, 0 errors, 0 warnings, **0 sorries**, 0 non-standard axioms).

### What Compiles (sorry-free)

| File | Step | LOC | Content |
|------|------|-----|---------|
| `Basic.lean` | 1 | 17 | Imports, universes, variable block |
| `NormingSeq.lean` | 2 | 46 | `isLUB_opNorm`, `exists_norming_sequence` |
| `DualDistribL.lean` | 3 | 64 | `projectiveSeminorm_field_tprod`, `dualDistribL`, `dualDistribL_tprod_apply`, `norm_dualDistribL_tprod_le` |
| `WithBidual.lean` | 4 | 119 | `projectiveSeminorm_tprod_of_bidual_iso` (the main theorem) |
| `RCLike.lean` | 5 | 21 | `projectiveSeminorm_tprod` (unconditional over ℝ/ℂ) |
| `DirectApproach.lean` | 6 | 141 | `reduced_representation_cost_ge`, `triangle_wrong_direction` + detailed obstruction analysis |
| `Counterexample.lean` | 7 | 119 | Literature survey + analysis (documentation-only Lean file) |

**Total**: 7 Lean files, ~527 LOC, **every theorem fully proven**.

### Key Results

1. **`projectiveSeminorm_tprod_of_bidual_iso`** (Step 4):
   ```
   (m : Π i, E i) (h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖) :
       projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖
   ```
   Proof: norming sequences → dualDistribL evaluation → limit passage.

2. **`projectiveSeminorm_tprod`** (Step 5):
   ```
   [RCLike 𝕜] (m : Π i, E i) :
       projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖
   ```
   One-line proof: discharge `h_bidual` via `inclusionInDoubleDualLi.norm_map`.

### Mathematical Conclusion

**`h_bidual` is the right hypothesis.** It cannot be removed in full generality using
known techniques, but it holds automatically wherever the cross property is known to be true:

- **ℝ, ℂ** (archimedean): Hahn-Banach gives isometric bidual embedding. ✓
- **ℚ_p** and spherically complete fields: Ingleton's theorem (1952) gives Hahn-Banach. ✓
- **ℂ_p** and non-spherically-complete fields: **Open question.** No counterexample known,
  but every known proof technique requires Hahn-Banach at a critical step.
- **Finite dimensions** over any field: `h_bidual` holds (algebraic dual suffices). ✓

The direct algebraic approach (Step 6) fails due to a wrong-direction triangle inequality
when reducing representations to linearly independent form.

No counterexample exists in the literature (Step 7). A counterexample would require an
infinite-dimensional space over a non-spherically-complete non-archimedean field — a very
exotic setting.

### Recommendation to David Gross

1. **For mathlib PR #33969**: Keep `h_bidual`. It is the correct generality level. The
   `RCLike` corollary gives the "clean" unconditional statement for the most common use case.

2. **The hypothesis captures exactly what's needed**: isometric bidual embedding at each
   tensor factor. This is a natural functional-analytic condition, not an artificial restriction.

3. **Future work**: If someone proves Ingleton's theorem in Lean and formalizes spherical
   completeness, the `h_bidual` hypothesis could be discharged for a broader class of fields
   (all spherically complete non-archimedean fields), analogously to the `RCLike` corollary.

4. **The open question** (over ℂ_p-type fields) is genuinely interesting but likely requires
   new techniques or a counterexample construction that doesn't currently exist in the literature.

### Session 13 (2026-02-09): Research proposals + Cancellation Trick formalization plan

**What was done:**
- Read David Gross's review (`review.txt`): previous work didn't attempt mathematical creativity
- Launched 3 parallel Opus 4.6 research agents:
  - **Counterexample Hunter**: No counterexample found. Tightest characterization: requires
    ∞-dim space over non-spherically-complete field where finite-dim Hahn-Banach fails
    for subspace norms. All naive attempts to cheapen pure tensors increase cost.
  - **Proof Strategist**: Discovered **cancellation trick** — proves cross property for
    all collinear representations (span dim s=1) WITHOUT Hahn-Banach. The tensor constraint
    forces residual cancellation, making the triangle inequality go in the correct direction.
    General case (s≥2) remains stuck: quotient norm degradation blocks closure.
  - **Creative/Deep Knowledge**: C*-algebra self-tensor argument (π(v⊗v) = ‖v‖² via
    multiplication map). Model theory, condensed math, tropical geometry all explored
    and rejected with reasons. 85% confidence conjecture is TRUE.
- All findings documented in `RESEARCH_PROPOSALS.md`
- Created formalization plan for the cancellation trick: 5 steps, ~115 LOC total
- Registered as beads issues: epic `ProjSeminorm-x4a` with 5 sub-issues in dependency chain:
  1. `ProjSeminorm-mto`: Create CancellationTrick.lean setup (15 LOC)
  2. `ProjSeminorm-hoj`: Prove exists_algebraic_dual_eq_one (25 LOC)
  3. `ProjSeminorm-daw`: Prove tmul_eq_tmul_factorization (30 LOC)
  4. `ProjSeminorm-iq7`: Prove tmul_norm_invariant (20 LOC)
  5. `ProjSeminorm-e3s`: Prove collinear_cost_ge — main theorem (25 LOC)

**Key mathematical insight (the cancellation trick):**
For v ⊗ w = ∑ vⱼ ⊗ (αⱼ•w₁), bilinearity gives (∑ αⱼ•vⱼ) ⊗ w₁ = v ⊗ w.
The rank-1 tensor norm invariance gives ‖∑ αⱼ•vⱼ‖•‖w₁‖ = ‖v‖•‖w‖.
Triangle inequality: ∑|αⱼ|•‖vⱼ‖ ≥ ‖∑ αⱼ•vⱼ‖. Combining: Cost ≥ ‖v‖•‖w‖. QED.

**Key mathlib API identified:**
- `LinearEquiv.toSpanNonzeroSingleton` for algebraic functional construction
- `TensorProduct.map` + `TensorProduct.rid` for rank-1 factorization
- `norm_smul`, `NormedField.norm_inv` for norm invariance

**Current state:**
- No new Lean code written. All work is research + planning.
- Next session: implement Steps 1-5 of cancellation trick formalization.

**Next session should:**
1. `bd ready` to find first actionable issue
2. Create CancellationTrick.lean and work through the 5 steps
3. Key difficulty: Step 2 (algebraic functional) and Step 3 (rank-1 factorization)

### Session 14 (2026-02-09): Cancellation trick fully formalized — sorry-free

**What was done:**
- Created `ProjSeminorm/CancellationTrick.lean` (8 files total, ~145 LOC)
- All 5 sub-issues of epic `ProjSeminorm-x4a` completed and closed
- **Every theorem proved sorry-free**:
  - `tmul_eq_zero_of_field`: Over a field, `a ⊗ₜ b = 0 → a = 0 ∨ b = 0`.
    Proof: `Module.Free.of_divisionRing` → `Module.Flat` → `lTensor` preserves
    injectivity of `toSpanSingleton` → `TensorProduct.rid` extracts `a = 0`.
  - `left_eq_zero_of_tmul_eq_zero`: Corollary of above.
  - `exists_dual_eq_one`: For `v ≠ 0`, ∃ `g : V →ₗ 𝕜, g v = 1`.
    Proof: `Module.Free.chooseBasis` → find nonzero coordinate → rescale `Basis.coord`.
  - `tmul_norm_product_eq`: `v ⊗ₜ w = u ⊗ₜ w₁ → ‖v‖*‖w‖ = ‖u‖*‖w₁‖`.
    Proof: Apply `(g ⊗ id)` via `TensorProduct.map` + `TensorProduct.lid` to extract
    `w = c•w₁`, then `(u - c•v) ⊗ₜ w₁ = 0` gives `u = c•v`, then `norm_smul + ring`.
  - `collinear_cost_ge` (main theorem): Collinear representation cost ≥ `‖v‖*‖w‖`.
    Proof: `smul_tmul` + `sum_tmul` (bilinearity collapse) → `norm_sum_le` (triangle)
    → `tmul_norm_product_eq` (norm invariance).
- Build: 2334 jobs, 0 errors, 0 warnings, 0 sorries
- Closed: ProjSeminorm-mto, -hoj, -daw, -iq7, -e3s, -x4a (6 issues)

**Key insights:**
- `Module.Flat.lTensor_preserves_injective_linearMap` is the clean way to prove
  `a ⊗ₜ b = 0 → a = 0 ∨ b = 0` over a field.
- `TensorProduct.map g id` + `TensorProduct.lid` extracts scalar relationships
  from tensor equalities without needing `VanishesTrivially` or basis machinery.
- `TensorProduct.smul_tmul` direction: `(r • m) ⊗ₜ n = m ⊗ₜ (r • n)`.
- `TensorProduct.sum_tmul` requires `Finset` argument (not `Fintype`).

**Current state:**
- All original 8 steps + cancellation trick complete. 25 of 28 issues closed.
- Project has 8 Lean files, ~670 LOC, **all sorry-free**.

**Next session should:**
1. `bd ready` to check remaining work
2. Consider extending cancellation trick to general (non-collinear) case
3. Or: write final summary email to David Gross

### Session 15 (2026-02-09): 5-agent research — CP true unconditionally, proof reduces to FDNP

**What was done:**
- Spawned 3 independent research agents (Alpha, Beta, Gamma) to investigate CP vs HB:
  - **Unanimous verdict**: CP does NOT imply HB, but CP is almost certainly true unconditionally
  - CP is not independent of ZFC (99% confidence)
  - Created `CROSS_PROPERTY_REPORT.md` and `AGENT_GAMMA_REPORT.md`
- Spawned 2 further agents (Delta, Epsilon) to find unconditional CP proof:
  - **Key discovery**: Quotient + Cancellation Trick reduces CP to ONE open lemma (FDNP)
  - Created `PROOF_STRATEGY.md` with complete 7-step proof assuming FDNP
- The proof structure:
  ```
  General repr → (FDNP gives norming H) → quotient by H → collinear repr
  → cancellation trick (sorry-free) → ‖q(f)‖=‖f‖ (FDNP) → done
  ```

**FDNP (Finite-Dimensional Norming Problem):**
For any finite-dimensional normed space W over a valued field k and any f ∈ W,
does there exist a hyperplane H ⊂ W with dist(f, H) = ‖f‖?
Equivalently: does a Birkhoff-James orthogonal hyperplane always exist?

Known cases: Archimedean fields (yes, Hahn-Banach), spherically complete NA fields (yes, Ingleton).
Open: non-spherically complete NA fields like ℂ_p.

**Current state:**
- `PROOF_STRATEGY.md` documents the complete proof assuming FDNP
- `CROSS_PROPERTY_REPORT.md` documents the 3-agent CP vs HB investigation
- All existing Lean code remains sorry-free (no new Lean code this session)

**TOP PRIORITY for next session: Resolve the 3-term CP inequality over the pathological norm**

### Session 16 (2026-02-10): FDNP settled — counterexample confirmed, CP reduced to explicit inequality

**What was done:**
- Critically evaluated an argument showing FDNP **fails** over ℂ_p in dimension 2
- **Verdict: the counterexample is correct.** The construction:
  - Take a decreasing chain (λₙ, rₙ) in ℂ_p with ∩ B̄(λₙ,rₙ) = ∅ (exists by non-spherical-completeness)
  - Define norm N(x,y) = r∞ · supₙ |x+λₙy|/rₙ on ℂ_p², rescaled so N(e₁)=1
  - Norming condition forces c = φ(e₂) into the empty intersection → no norming functional
  - Key normalization fix: the argument as presented had a gap (‖f‖ = 1/r∞ ≠ 1);
    rescaling by r∞ fixes it cleanly
- This was NOT new — Agent Alpha (Session 15) had already found the same construction
  in CROSS_PROPERTY_REPORT §2.2, and PROOF_STRATEGY §4.4 noted Hahn-Banach fails over ℂ_p
- **Consequence: the quotient + FDNP proof strategy CANNOT give unconditional CP**
- **However: CP itself is strictly weaker than FDNP and may still be true**
- Derived the explicit 3-term CP test case:
  - E = F = (ℂ_p², N) with pathological norm, e = f = e₁
  - Cost C = N(c₁-αa,-αb)N(p,q) + N(c₂-βa,-βb)N(r,s) + N(a,b)N(αp+βr,αq+βs)
  - CP ⟺ C ≥ 1 for all 8 parameters with ps ≠ qr
- Set up adversarial proof framework in `three-term-cp/` with 19 nodes:
  - 4 proof strategies for Case A (CP holds): duality dead-end, collapse comparison,
    ultrametric case analysis, optimization/convexity
  - 4 counterexample approaches for Case B (CP fails): standard basis search,
    resonant basis, perturbative, numerical
  - Key insight from 1.4.2.3: when N(v₁) ≥ |α|N(v₃) for BOTH terms (isosceles
    dominance), C ≥ collapsed cost ≥ 1 automatically. The hard case is when
    the third term must compensate for ultrametric cancellation in w₃ = αw₁+βw₂.

**Key references:**
- Schikhof, *Ultrametric Calculus* §20 (non-spherical-completeness of ℂ_p)
- van Rooij, *Non-Archimedean FA* Ch.4 (Hahn-Banach failure)
- Ingleton 1952 (Hahn-Banach over spherically complete fields)

**Current state:**
- `three-term-cp/` contains the af proof workspace (19 nodes, all pending)
- All existing Lean code remains sorry-free (no new Lean code this session)
- FDNP is definitively settled: FALSE over ℂ_p, so the quotient strategy is blocked
- The open question is now purely: does the 3-term cost inequality C ≥ 1 hold?

**Next session should:**
1. `cd three-term-cp && af status` to see the proof tree
2. Attack node 1.4.2.3 (ultrametric case analysis) — the most promising proof path
3. Or attack node 1.5.1 (standard basis counterexample search) — concrete computation
4. The critical sub-question is 1.4.2.4: when |α|N(w₁) = |β|N(w₂), can ultrametric
   cancellation in N(αw₁+βw₂) make the third term too small to compensate?
5. Numerical experiments (node 1.5.4) could resolve the question empirically

### Session 17 (2026-02-10): BFS verification sweep — critical finding, then BFS prover sweep

**What was done:**
- Ran adversarial proof framework BFS sweep on the 19-node `three-term-cp/` proof tree
- Dispatched 24 Opus subagent jobs (13 provers, 11 verifiers) across 12 waves
- Tree grew from 19 → 25 nodes (6 corrected child nodes added by provers)

**Critical structural fix (Session 17a — verifier sweep, waves 1-3):**
- **ch-d076e166088 on node 1.1**: The reduction E=F=(ℂ_p²,N) with ONE norm is wrong.
  Correct: V=(k²,N_E) and W=(k²,N_F) with TWO INDEPENDENT norms.
  This propagated to all downstream nodes.
- Verifiers filed 15 challenges across 6 depth-0/1 nodes.
- Node 1.2 (parametrization algebra) validated as correct.

**BFS prover sweep (Session 17b — waves 1-12):**

Provers addressed all challenges at depths 0-2. Key outcomes:

| Node | Action | Result |
|------|--------|--------|
| 1 | Refined | "Equivalently" → "A key test case" (3 gaps acknowledged) |
| 1.1 | Refined | Single norm → two independent norms N_E, N_F |
| 1.3 | Refined + child 1.3.1 | Tautological case split → substantive two-norm reduction |
| 1.4 | Refined + child 1.4.5 | Single norm → universal quantification over all norm pairs |
| 1.5 | Refined | Two-norm cost defined; N_E≠N_F identified as search frontier |
| **1.4.2** | **ARCHIVED** | Comparison inequality T₁+T₂+T₃ ≥ S₁+S₂ is **FALSE** (explicit counterexamples in both archimedean and non-archimedean settings) |
| **1.4.4** | **ARCHIVED** | C is NOT piecewise-multiplicative; Berkovich language misapplied; "min at b=0" unsubstantiated |
| **1.5.2** | **ARCHIVED** | Resonant basis mechanism mathematically incoherent (chain norm determined by exit index, not near-cancellation); tensor constraint gives hard floor |
| **1.5.4** | **ARCHIVED** | √2 ∉ Q₂ (Hensel fails on double root); prior numerical evidence vacuous (2 of 8 params explored) |
| 1.4.1 | Refined + child 1.4.1.1 | "Dead end" → partially successful (duality works when FDNP holds for N_E) |
| 1.4.3 | Refined + children 1.4.3.1/1.4.3.2 | Non-equality cases PROVED; equality cases identified as hard core |
| 1.5.1 | Refined + child 1.5.1.1 | Two-norm standard basis search formulated |
| 1.5.3 | Refined | Piecewise constancy is correct but gives no analytical reduction |

**Validated nodes (3):** 1.2, 1.3.1, 1.4.5

**High-value findings from verifier agents:**
1. **1.4.2 disproof**: The bilinearity collapse comparison T₁+T₂+T₃ ≥ S₁+S₂ fails when
   w₃=αw₁+βw₂ exhibits norm cancellation (N_F(w₃) < |α|N_F(w₁)+|β|N_F(w₂)). This kills
   the entire 1.4.2.x subtree. CP itself is NOT refuted.
2. **1.4.1 partial success**: The duality approach Σ N_E(vⱼ)·N_F(wⱼ) ≥ Σ |φ(vⱼ)|·N_F(wⱼ)
   ≥ N_F(Σ φ(vⱼ)·wⱼ) = 1 needs FDNP for N_E ONLY (not both norms). This proves CP for
   all pairs (N_E,N_F) where N_E admits a norming functional for e₁.
3. **1.4.3 partial proof**: The isosceles property handles all non-equality cases
   (|c_j| ≠ |α|·N_E(v₃)). Only the equality loci remain open.
4. **1.5.2 chain norm formula**: N(1,c) = |1+c·λ_{M+1}| where M is the exit index of
   -1/c from the chain. The supremum is dominated by the tail, not individual chain points.
5. **1.5.4 mathematical error**: √2 does not exist in Q₂ (value group obstruction).
   Valid chains need pseudo-convergent sequences with no C₂-limit.

**The hard core of the problem (all strategies converge here):**
The equality cases |c_j| = |α|·N_E(v₃) (equivalently |α|·N_F(w₁) = |β|·N_F(w₂) on the
w-side). At these codimension-1 loci, ultrametric cancellation can reduce N_E(v_j) below
|c_j|, creating a deficit. Whether T₃ = N_E(v₃)·N_F(αw₁+βw₂) always compensates is THE
open question. The v-side and w-side cancellations are dual manifestations of the same
phenomenon. A viable proof likely needs to handle them jointly through the tensor equation,
rather than analyzing T₁, T₂, T₃ independently.

**Current state:**
- `three-term-cp/`: 25 nodes, 3 validated, 4 archived, 18 pending, 14 open challenges (mostly minor/note)
- All Lean code remains sorry-free (no new Lean code this session)
- Depth-3 nodes (1.4.2.1-1.4.2.4) are moot (parent archived) but contain relevant analysis of the equality obstruction
- Node 1.6 (extension to n>3 terms) not yet verified

**Next session should:**
1. `cd three-term-cp && af status` to see the updated proof tree
2. Archive depth-3 nodes 1.4.2.1-1.4.2.4 (parent dead)
3. Focus on the equality-case obstruction (nodes 1.4.3.2 / 1.4.2.4):
   - Can the tensor equation v₁+αv₃=c₁e₁, v₂+βv₃=c₂e₁ be exploited to couple
     the v-side and w-side cancellations?
   - Is there a direct proof that T₁+T₃ ≥ |c₁|·N_F(w₁) at the equality locus?
   - Or: search for counterexamples in the two-norm equality case
4. The duality partial success (1.4.1.1) reduces the open case to: k non-spherically-complete
   AND N_E fails FDNP at e₁. This is a very specific setting — analyze it directly

### Session 18 (2026-02-10): PDF report generated

**What was done:**
- Generated a 13-page pdflatex report at `report/report.tex` (→ `report/report.pdf`)
- Follows the format of `~/Projects/firstproof/problem01/report.tex` and `problem02/report.tex`
- Contents:
  - §1: Problem statement (CP, h_bidual, why it's hard)
  - §2: Lean 4 formalization summary (8 files, ~670 LOC, sorry-free)
  - §3: 3-term CP reduction (parametrization, two-norm cost inequality)
  - §4: Proof strategy + adversarial investigation (4 strategies attempted, 2 partially successful, 4 archived as dead)
  - §5: FDNP counterexample over ℂ_p (the key negative result)
  - §6: The hard core — equality cases (the open frontier)
  - §7: Assessment and recommendation (keep h_bidual)
  - Appendix A: Full proof tree from `af status`
  - Appendix B: Complete node descriptions from `af export --format latex` (all 25 nodes)
- Used `af export --format latex` for the appendix node descriptions

**Current state:**
- Report complete at `report/report.pdf`
- All Lean code remains sorry-free
- 3-term CP inequality remains open (equality cases are the hard core)

**Next session should:**
1. Attack the equality-case obstruction (node 1.4.3.2)
2. Or: attempt numerical counterexample search with proper ℂ_p chains
3. Or: share report with David Gross for feedback

### Session 19 (2026-02-12): Five proof strategy reports generated

**What was done:**
- Spawned 5 parallel Opus subagents to generate independent proof strategies for Conjecture 6.1 (the hard-core equality-case obstruction)
- Each agent wrote a detailed report in `reports/`:
  - `alpha_tropical.md` (34KB) — Tropical/valuative geometry: tropicalize C on Berkovich tree, exit index stratification, balancing condition
  - `beta_operator.md` (45KB) — Operator algebra: **key negative result** — systematically proves ALL linear-functional approaches reduce to FDNP
  - `gamma_convex.md` (60KB) — Convex duality: BFEP (Bilinear Form Existence Problem) — 4 DOF vs 2 DOF gap; verifies Monna-Springer bipolar theorem fails over ℂ_p
  - `delta_padic.md` (54KB) — p-adic ball geometry: **Schneider Reduction** — π_sum ≥ π_max = ‖v‖·‖w‖ for all ultrametric norms (Schneider Prop 17.4), reducing open case to non-ultrametric norms
  - `epsilon_algebraic.md` (61KB) — Algebraic/combinatorial: Cauchy-Binet positivity certificate, skeleton decomposition C-1 = (skeleton ≥ 0) + perturbation

**Key findings across reports:**
1. **Schneider Reduction** (Delta, 55-70% feasibility): CP holds for ALL ultrametric seminormed spaces over ANY NA field. The remaining open case is FDNP for non-ultrametric norms.
2. **All linear approaches → FDNP** (Beta): Every linear functional strategy (operator norm, trace, CP maps, Stinespring, Haagerup, Grothendieck) reduces to FDNP which fails over ℂ_p.
3. **BFEP** (Gamma, 35-45%): Bilinear forms have 4 DOF on k²×k² vs 2 DOF for product functionals — may bypass FDNP.
4. **Cauchy-Binet certificate** (Epsilon, 35%): Express C-1 as sum of non-negative terms using 2×2 minor structure.
5. **Tropical balancing** (Alpha, 25-35%): Geometric picture but key balancing claim unproven.

**Current state:**
- 5 detailed strategy reports in `reports/` (~254KB total)
- All Lean code remains sorry-free
- 3-term CP inequality remains open

**Next session should:**
1. **Verify Schneider Reduction**: Check Schneider Prop 17.4 applies to projective (not just maximal) tensor seminorm — if π_sum ≥ π_max is rigorous, CP is proved for all ultrametric norms
2. If Schneider works: prove FDNP for non-ultrametric norms (the reduced open case)
3. If gap found: pursue BFEP (Gamma) or Cauchy-Binet (Epsilon) as backup strategies
4. Consider formalizing the Schneider reduction in Lean 4

### Session 20 (2026-02-12): Schneider Reduction formalized — SchneiderReduction.lean

**What was done:**
- Created `ProjSeminorm/SchneiderReduction.lean` (~100 LOC) formalizing Schneider's Prop 17.4
  proof strategy for CP over ultrametric normed spaces
- **13 lemmas/theorems** with correct type signatures, all sorry'd with detailed proof sketches:
  1. `norm_sum_le_iSup_mul_norm` — ultrametric norm bound for basis expansions
  2. `IsEpsOrthogonal` — predicate for ε-orthogonal bases
  3. `exists_epsOrthogonal_basis_one` — ε-orthogonal basis in dim 1
  4. `exists_epsOrthogonal_basis` — general existence (Schneider Lemma 17.3)
  5. `coord_tensor_eq` — coordinate extraction for tensor representations
  6. `exists_product_ge_of_sum_eq` — ultrametric domination lemma
  7. `norm_ge_coord_mul_norm` — single-term norm lower bound
  8. `single_term_cost_bound` — product lower bound for one term
  9. `exists_max_coord_index` — maximizing coordinate index
  10. `representation_cost_ge` — KEY: every repr has cost ≥ (1+ε)⁻⁴ ‖v‖·‖w‖
  11. `projectiveSeminorm_tprod_ge_ultrametric` — lower bound via ε → 0
  12. `projectiveSeminorm_tprod_ultrametric` — **the main theorem** (= le_antisymm)
- Created beads epic `ProjSeminorm-o5d` (Schneider-Reduction) with 16 sub-issues, all closed
- Converted Schneider PDF to markdown via `marker_single` (Perez-Garcia still converting)
- Build verified: 2334 jobs, 0 errors, 10 sorry warnings
- Key API finding: `Basis` is `Module.Basis` in current mathlib (moved into `Module` namespace)

**Current state:**
- 9 Lean files, ~770 LOC total. Steps 1-8 + CancellationTrick sorry-free. SchneiderReduction has 10 sorries.
- `projectiveSeminorm_tprod_ultrametric` has correct type signature:
  ```
  [IsUltrametricDist 𝕜] [∀ i, IsUltrametricDist (E' i)] [∀ i, FiniteDimensional 𝕜 (E' i)]
  (m : Π i, E' i) : projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖
  ```
- Reference markdown: `references/schneider_md/` (Schneider book)

**Next session should:**
1. Read `references/schneider_md/` Ch. 17 to verify Lemma 17.3 / Prop 17.4 statements
2. Start filling sorries — easiest first: `norm_ge_coord_mul_norm` (Step 8),
   `single_term_cost_bound` (Step 9), `exists_max_coord_index` (Step 10)
3. The hardest sorry is `exists_epsOrthogonal_basis` (Step 5, ~20-30 LOC when filled)

### Session 21 (2026-02-12): Git history purge + exists_product_ge_of_sum_eq proved

**What was done:**
- Purged `references/` from entire git history (copyrighted PDFs + markdown conversions)
  - `git filter-branch --index-filter` to rewrite all 48 commits
  - `git gc --prune=now --aggressive` to remove old objects
  - Force pushed to remote
  - Added `/references/` to `.gitignore`
- Regenerated both markdown conversions locally via `marker_single` from `~/Projects/archivum/.venv/`:
  - Schneider: `references/schneider_md/978-3-662-04728-6/978-3-662-04728-6.md` (~11 min)
  - Perez-Garcia: `references/perezgarcia_md/...md` (~31 min)
- Proved `exists_product_ge_of_sum_eq` in SchneiderReduction.lean (ultrametric domination lemma):
  - Added `(hn : 0 < n)` hypothesis (lemma is unprovable for empty `Fin 0`)
  - Proof: `Nonempty (Fin n)` → `Finset.univ_nonempty` → `IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty` → witness + `norm_mul`
- Build: 2334 jobs, 0 errors, 9 sorry warnings (down from 10)

**Current state:**
- 9 Lean files, ~770 LOC. SchneiderReduction.lean has 9 sorries remaining.
- `references/` exists locally (PDFs + regenerated markdowns) but is gitignored
- Git history is clean — no copyrighted material in any commit

**Next session should:**
1. Read `references/schneider_md/` Ch. 17 to verify Lemma 17.3 / Prop 17.4 statements
2. Fill sorries — next easiest: `exists_epsOrthogonal_basis_one` (dim 1 base case), `coord_tensor_eq` (bilinear functional on tensors)
3. The hardest sorry is `exists_epsOrthogonal_basis` (Step 5, ~20-30 LOC when filled)
4. `marker_single` lives in `~/Projects/archivum/.venv/bin/marker_single` (uses `--output_dir` flag)

### Session 22 (2026-02-12): 4 SchneiderReduction sorries filled (9→5)

**What was done:**
- Filled 4 sorries in `SchneiderReduction.lean`, all sorry-free:
  1. `norm_sum_le_iSup_mul_norm` (Step 2): Ultrametric norm bound for basis expansions.
     Case split on `IsEmpty ι`; nonempty case uses `IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty`
     + `norm_smul` + `le_ciSup`.
  2. `norm_ge_coord_mul_norm` (Step 8): Single-coordinate lower bound from ε-orthogonal bases.
     Apply `hb.2` with `bE.repr v` as coefficients, `convert ... using 2` to handle `coord`/`repr`
     syntactic mismatch, then `gcongr` + `le_ciSup`.
  3. `single_term_cost_bound` (Step 9): Product of two `norm_ge_coord_mul_norm` bounds.
     `nlinarith` with nonnegativity witnesses.
  4. `exists_max_coord_index` (Step 10): Maximizing index via `Finite.exists_max`.
- Added `import Mathlib.Data.Fintype.Order` (needed for `Finite.bddAbove_range`)
- Build: 2334 jobs, 0 errors, 5 sorry warnings (down from 9)

**Key API learnings:**
- `bE.coord j v = bE.repr v j` by `rfl`, but syntactic mismatch blocks `rw`; use `convert ... using 2`
- `Finite.bddAbove_range` requires `import Mathlib.Data.Fintype.Order`
- `le_ciSup` needs explicit function: `le_ciSup (Finite.bddAbove_range (fun j => ...)) i`
- `Finite.exists_max` gives maximizer over any `[Finite α] [Nonempty α] [LinearOrder β]`
- `IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty` needs `Finset.Nonempty`, not `Nonempty ι`
- `mul_le_mul'` needs `MulLeftMono` which ℝ doesn't synthesize; use `nlinarith` instead

**Current state:**
- 9 Lean files, ~770 LOC. SchneiderReduction.lean has 5 sorries remaining:
  - `exists_epsOrthogonal_basis_one` (dim 1 base case)
  - `exists_epsOrthogonal_basis` (general, hardest — induction on finrank)
  - `coord_tensor_eq` (coordinate extraction via bilinear functional)
  - `representation_cost_ge` (key assembly — depends on above 3)
  - `projectiveSeminorm_tprod_ge_ultrametric` (ε→0 limit — depends on assembly)

**Next session should:**
1. Fill `exists_epsOrthogonal_basis_one` (dim 1 base case, should be straightforward)
2. Fill `coord_tensor_eq` (apply bilinear functional to tensor equation)
3. Attempt `exists_epsOrthogonal_basis` (induction on finrank, ~20-30 LOC)
4. Once those 3 are done, `representation_cost_ge` assembles them
5. Then `projectiveSeminorm_tprod_ge_ultrametric` takes ε→0

### Session 23 (2026-02-12): 3 more SchneiderReduction sorries filled (5→2)

**What was done:**
- Filled 3 sorries in `SchneiderReduction.lean`:
  1. `exists_epsOrthogonal_basis_one` (Step 4): Dim 1 base case.
     `Module.finBasisOfFinrankEq` for basis, `Fin.sum_univ_one` + `ciSup_unique` to simplify,
     `inv_le_one_iff_of_pos` + `mul_le_of_le_one_left` to close `(1+ε)⁻¹ * x ≤ x`.
  2. `coord_tensor_eq` (Step 6): Coordinate extraction via bilinear functional.
     Lift `(LinearMap.mul' 𝕜 𝕜).compl₁₂ (bE.coord i) (bF.coord k)` through `TensorProduct.lift`,
     then `congr_arg` + `map_sum` + `simp`.
  3. `representation_cost_ge` (Step 11): Key assembly of all helper lemmas.
     Edge cases (`n = 0` via `tmul_eq_zero_of_field`, `‖v‖ = 0` or `‖w‖ = 0`).
     Main case: ε-orthogonal bases → maximizers → coord identity → ultrametric domination
     → single term bound → ultrametric upper bounds (`norm_sum_le_iSup_mul_norm` + `ciSup_le`)
     → `nlinarith` with `mul_le_mul`, `mul_le_mul_of_nonneg_left`, `pow_le_pow_of_le_one`.
- Added `import ProjSeminorm.CancellationTrick` (for `tmul_eq_zero_of_field` in n=0 case)
- Build: 2334 jobs, 0 errors, 2 sorry warnings (down from 5)

**Key API learnings:**
- `Module.finBasisOfFinrankEq` needs `FiniteDimensional` + `Module.Free` instances manually via `haveI`
- `ciSup_unique` simplifies `⨆ i : Fin 1, f i` to `f default`; combine with `Fin.default_eq_zero`
- `(LinearMap.mul' 𝕜 𝕜).compl₁₂ f g` constructs the bilinear map `(u, t) ↦ f u * g t`
- `TensorProduct.lift.tmul` evaluates the lifted map on pure tensors
- `Module.finrank_pos_of_exists_ne_zero` derives positive dimension from a nonzero element
- `pow_le_pow_of_le_one` gives `(1+ε)⁻¹ ^ 4 ≤ (1+ε)⁻¹ ^ 2` for the conservative bound

**Current state:**
- 9 Lean files, ~840 LOC. SchneiderReduction.lean has 2 sorries remaining:
  - `exists_epsOrthogonal_basis` (Schneider Lemma 17.3, induction on finrank — hardest sorry)
  - `projectiveSeminorm_tprod_ge_ultrametric` (ε→0 limit for PiTensorProduct)

**Next session should:**
1. Fill `exists_epsOrthogonal_basis` — induction on finrank. Key steps:
   - Base: finrank 0 → empty basis, vacuous. finrank 1 → `exists_epsOrthogonal_basis_one`.
   - Inductive step: pick near-optimal v, quotient by `span {v}`, recurse, lift back.
   - Need: `Submodule.Quotient`, `Module.finrank_quotient_add_finrank`, lifting basis elements.
2. Fill `projectiveSeminorm_tprod_ge_ultrametric` — generalize binary case to PiTensorProduct.
   May need tensor associativity or direct argument via `projectiveSeminorm_apply` + `iInf`.

### Session 24 (2026-02-12): Induction skeleton for exists_epsOrthogonal_basis

**What was done:**
- Restructured `exists_epsOrthogonal_basis` from bare sorry into proper induction on finrank
- Uses `suffices` to factor through a helper quantifying universally over all spaces of
  dimension d (enabling IH to apply to quotient spaces)
- Base case (d=0): fully proved — empty basis, `simp [Finset.univ_eq_empty]`
- Inductive step (d=n+1): sorry'd with clear comment about what's needed
- Build verified: 2334 jobs, 0 errors, 2 sorry warnings (unchanged count)
- Investigated approach for `projectiveSeminorm_tprod_ge_ultrametric`:
  - Duality approach via `dualDistribL` with coordinate CLMs (mirrors WithBidual.lean)
  - Use `LinearMap.mkContinuous` (not `toContinuousLinearMap`) to avoid `CompleteSpace 𝕜`
  - Bound: `‖coord_{i₀}(v)‖ ≤ ((1+ε)/‖b(i₀)‖) * ‖v‖` from ε-orthogonal property
  - Chain: `∏|g_i(m_i)| ≤ ∏‖g_i‖ * projseminorm` via `dualDistribL` + `norm_dualDistribL_tprod_le`
  - Ratio bound: `|g_i(m_i)|/‖g_i‖ ≥ ‖m_i‖/(1+ε)`, giving `projseminorm ≥ (1+ε)^{-|ι|} * ∏‖m_i‖`
  - Take ε → 0

**Key API findings:**
- `LinearMap.mkContinuous` avoids `CompleteSpace 𝕜` requirement (unlike `toContinuousLinearMap`)
- `LinearMap.mkContinuous_norm_le` gives `‖f.mkContinuous C h‖ ≤ C` when `0 ≤ C`
- `LinearMap.mkContinuous_apply` gives `(f.mkContinuous C h) x = f x`
- `FiniteDimensional` needs `import Mathlib.Analysis.Normed.Module.FiniteDimension`
- `Module.Free.of_divisionRing` needs explicit `(K := 𝕜) (V := E)` in universally-quantified context

**Current state:**
- 9 Lean files, ~850 LOC. SchneiderReduction.lean has 2 sorries remaining:
  - `exists_epsOrthogonal_basis` inductive step (d=n+1): quotient + lift + ε-orthogonality
  - `projectiveSeminorm_tprod_ge_ultrametric`: duality approach fully planned, needs implementation

**Next session should:**
1. Fill `exists_epsOrthogonal_basis` inductive step:
   - Pick nonzero v₀ ∈ E, form quotient Q = E/⟨v₀⟩ (finrank = n)
   - Need `Submodule.Quotient.seminormedAddCommGroup`, `Submodule.Quotient.normedSpace`
   - Need ultrametric quotient (prove via `isUltrametricDist_of_isNonarchimedean_norm`)
   - IH gives ε-orthogonal basis of Q, lift back, combine with v₀
2. Fill `projectiveSeminorm_tprod_ge_ultrametric`:
   - Use `LinearMap.mkContinuous` for coordinate CLMs (no `CompleteSpace` needed)
   - Chain via `dualDistribL` as in WithBidual.lean
   - ε→0 limit via `le_of_forall_lt` or direct contradiction
