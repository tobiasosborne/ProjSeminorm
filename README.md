# ProjSeminorm

A Lean 4 formalization investigating whether the projective tensor seminorm is
multiplicative on pure tensors **without** assuming isometric bidual embedding.

**Status**: Complete. Sorry-free. Build clean (0 errors, 0 warnings).

## The Problem

For a finite family of seminormed spaces `{E_i}` over a nontrivially normed
field `𝕜`, the **projective seminorm** on `⨂[𝕜] i, E i` is defined as:

```
π(x) = inf { ∑_j ∏_i ‖m_j(i)‖ : x = ∑_j ⨂_i m_j(i) }
```

The infimum is over all representations of `x` as a sum of pure tensors.

**The question**: Is it always true that `π(⨂ₜ m_i) = ∏ ‖m_i‖`? That is, is
the projective seminorm multiplicative on pure tensors?

The **upper bound** `π(⨂ₜ m_i) ≤ ∏ ‖m_i‖` is trivial (take the one-term
representation). The lower bound is the hard part.

### Origin

Mathlib4 PR [#33969](https://github.com/leanprover-community/mathlib4/pull/33969)
(by David Gross and Davood Haji Taghi Tehrani) proves multiplicativity under an
additional hypothesis:

```lean
theorem projectiveSeminorm_tprod_of_bidual_iso
    (m : Π i, E i)
    (h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 _ (m i)‖ = ‖m i‖) :
    projectiveSeminorm (⨂ₜ[𝕜] i, m i) = ∏ i, ‖m i‖
```

The `h_bidual` hypothesis requires that each `m i` embeds isometrically into
its double dual. This holds automatically over `ℝ` and `ℂ` (by Hahn-Banach),
but not in general over non-archimedean fields like `ℚ_p`.

**This project asks**: Can `h_bidual` be removed?

## Results

### What we proved (all sorry-free)

1. **`projectiveSeminorm_tprod_of_bidual_iso`** — the main theorem from PR
   #33969, re-derived independently via norming sequences and a continuous dual
   distribution map.

2. **`projectiveSeminorm_tprod`** — unconditional multiplicativity over `ℝ`
   and `ℂ` (the `RCLike` corollary), derived as a one-liner from the above
   using `inclusionInDoubleDualLi` (the linear isometry given by Hahn-Banach).

3. **Why the direct algebraic approach fails** — the natural strategy of
   reducing tensor representations to ones with linearly independent components
   is blocked by a wrong-direction triangle inequality. The reduction can
   *increase* cost, so bounding the original cost below by the reduced cost
   does not work.

### The open question

Over a general `NontriviallyNormedField` (including non-archimedean fields),
whether `h_bidual` can be removed remains **open**. Our analysis shows:

- The duality proof inherently needs `h_bidual`: the lower bound it produces is
  `∏ ‖m_i‖_bidual`, which equals `∏ ‖m_i‖` only when the bidual embedding is
  isometric.
- The direct algebraic approach (bypassing duality) is blocked by a fundamental
  inequality going the wrong way.
- A counterexample would require an infinite-dimensional Banach space over a
  non-archimedean field with poor dual (e.g., trivial dual). No such
  counterexample was found.
- In finite dimensions, `h_bidual` holds automatically (even over non-archimedean
  fields), so no finite-dimensional counterexample exists.

**Conclusion**: `h_bidual` appears necessary for the general case. The `RCLike`
corollary is the right result for mathlib.

## Mathematical Background

### Why `h_bidual` enters the proof

For functionals `f_i ∈ E_i*` with `‖f_i‖ ≤ 1`:

```
|∏ f_i(m_i)| = |dualDistrib(⨂ f_i)(⨂ m_i)| ≤ ‖dualDistrib(⨂ f_i)‖ · π(⨂ m_i)
```

Since `‖dualDistrib(⨂ f_i)‖ ≤ ∏ ‖f_i‖ ≤ 1`, taking the supremum over `f_i`
gives:

```
∏ sup_{‖f_i‖≤1} |f_i(m_i)| ≤ π(⨂ m_i)
```

But `sup_{‖f‖≤1} |f(x)| = ‖inclusionInDoubleDual(x)‖`, which equals `‖x‖`
only when the bidual embedding is isometric. So we get:

```
∏ ‖inclusionInDoubleDual(m_i)‖ ≤ π(⨂ m_i) ≤ ∏ ‖m_i‖
```

The left side equals `∏ ‖m_i‖` precisely when `h_bidual` holds.

### Why the direct approach fails

Given `v ⊗ w = ∑ v_j ⊗ w_j` with `{w_j}` linearly dependent, one can reduce
to an independent set `{w_k}_{k≤s}` by writing `w_j = ∑_k a_{jk} w_k` and
combining: `u_k = v_k + ∑_{j>s} a_{jk} v_j`. For the **reduced**
representation the lower bound holds:

```
∑_k ‖u_k‖ · ‖w_k‖ = ‖v‖ · ∑_k |c_k| · ‖w_k‖ ≥ ‖v‖ · ‖w‖
```

But connecting this to the **original** cost requires
`∑_k |a_{jk}| · ‖w_k‖ ≤ ‖w_j‖`, while the triangle inequality gives only
`‖w_j‖ ≤ ∑_k |a_{jk}| · ‖w_k‖` — the wrong direction.

### Reference

Schneider's [NFA notes](https://ivv5hpp.uni-muenster.de/u/pschnei/publ/lectnotes/nfa.pdf),
Prop 17.4, proves multiplicativity for the ultrametric "max" projective norm
(a different definition) using d-orthogonal bases. This technique does not
directly transfer to the standard "sum" projective seminorm used in mathlib.

## File Structure

| File | Lines | Content |
|---|---|---|
| `Basic.lean` | 16 | Imports, universe variables, namespace |
| `NormingSeq.lean` | 46 | `isLUB_opNorm`, `exists_norming_sequence` |
| `DualDistribL.lean` | 64 | `projectiveSeminorm_field_tprod`, `dualDistribL` (continuous dual distribution), evaluation + norm bounds |
| `WithBidual.lean` | 119 | **Main theorem**: `projectiveSeminorm_tprod_of_bidual_iso` |
| `RCLike.lean` | 20 | **Corollary**: `projectiveSeminorm_tprod` (unconditional over ℝ/ℂ) |
| `DirectApproach.lean` | 141 | Formal analysis of why the direct algebraic approach fails |

### Dependency chain

```
Basic.lean
├── NormingSeq.lean
│   └── DualDistribL.lean
│       └── WithBidual.lean
│           └── RCLike.lean
└── DirectApproach.lean
```

## Critical API Note

In current mathlib, `‖x‖` for `x : ⨂[𝕜] i, E i` uses **injectiveSeminorm**,
not projectiveSeminorm. This project uses `projectiveSeminorm x` explicitly
throughout. PR #33969 proves `injectiveSeminorm = projectiveSeminorm` and
switches the instance; until that is merged, the distinction matters.

## Building

```bash
lake build ProjSeminorm 2>&1 | tail -40
```

**Never** run bare `lake build` — it rebuilds all of mathlib (~2 hours).

## Related

- **Mathlib PR**: [#33969](https://github.com/leanprover-community/mathlib4/pull/33969)
- **Mathlib file**: `Mathlib/Analysis/Normed/Module/PiTensorProduct/ProjectiveSeminorm.lean`

## License

Apache 2.0
