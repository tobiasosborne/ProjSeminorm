# HANDOFF: Projective Seminorm Multiplicativity on Pure Tensors

## The Problem

**Source**: Email from David Gao (see `dgemail.txt` in this directory)

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

**Stakes**: If proved unconditionally, David & Davood will clean it up and PR to mathlib.
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
- `inclusionInDoubleDual_apply` simplifies `incl(m)(f)` to `f(m)`.
- `gcongr` handles the monotonicity steps in the calc chain.

**Current state:**
- 12 of 22 issues closed. `ProjSeminorm-dtv.13` in progress (sorry in `hle`).

**Next session should:**
1. Fill the `hle` sorry using the documented approach (zero case + nonzero calc)
2. Then proceed to Step 5 (RCLike corollary — should be ~5 LOC)
