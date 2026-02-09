/-
Copyright (c) 2026 Tobias Osborne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Osborne
-/
import ProjSeminorm.Basic

/-!
# Counterexample Investigation: Projective Seminorm Cross Property

## The Question

Over a general `NontriviallyNormedField 𝕜`, does the projective seminorm satisfy the
cross property `π(⨂ m_i) = ∏ ‖m_i‖` unconditionally, or is the `h_bidual` hypothesis
(isometric bidual embedding) genuinely necessary?

## Summary of Findings

**No counterexample is known.** The question is open for non-spherically-complete
non-archimedean fields. For all other fields, the cross property holds unconditionally.

## Detailed Analysis by Field Type

### 1. Archimedean fields (ℝ, ℂ)

The cross property holds unconditionally. The Hahn-Banach theorem guarantees isometric
bidual embedding (`inclusionInDoubleDualLi`), making `h_bidual` automatic.
This is formalized in `ProjSeminorm/RCLike.lean` as `projectiveSeminorm_tprod`.

### 2. Spherically complete non-archimedean fields (e.g., ℚ_p)

**Ingleton's theorem (1952)**: If `K` is a spherically complete non-archimedean valued
field, then the Hahn-Banach extension theorem holds for all normed spaces over `K`.
The converse (spherical completeness is also *necessary*) was established by later
authors (see Perez-Garcia & Schikhof, 2010).

Since `ℚ_p` is spherically complete (it is a local field), the Hahn-Banach theorem holds,
the bidual embedding is isometric, and `h_bidual` is automatic. The cross property holds.

This means `h_bidual` could in principle be removed for `ℚ_p` by proving Ingleton's theorem
in Lean and deriving the isometric embedding. However, Ingleton's theorem is not yet in
mathlib.

### 3. Non-spherically-complete non-archimedean fields (e.g., ℂ_p)

This is the **only remaining case** where `h_bidual` might genuinely be needed.

**ℂ_p** (the completion of the algebraic closure of ℚ_p) is NOT spherically complete.
Over such fields:

- Hahn-Banach can fail: there exist Banach spaces `E` with `E* = {0}`.
- For such spaces, `‖inclusionInDoubleDual(x)‖ = 0` for all nonzero `x`.
- The duality lower bound gives `π(⨂ m_i) ≥ 0`, which is vacuous.

**However**: having a trivial dual does NOT automatically mean the cross property fails.
It only means the standard duality *proof technique* fails. The cross property might
still hold for purely algebraic/metric reasons.

### 4. Why no finite-dimensional counterexample exists

In finite dimensions over ANY nontrivially normed field, a version of Hahn-Banach holds:
for finite-dimensional subspaces, norm-achieving functionals can be constructed using
the algebraic dual (which is finite-dimensional, hence complete). So `h_bidual` holds
in finite dimensions, and the cross property follows from `WithBidual.lean`.

**Any counterexample must be infinite-dimensional.**

### 5. The ultrametric "max" definition (Schneider)

Schneider's *Nonarchimedean Functional Analysis* (Springer, 2002), Proposition 17.4,
proves multiplicativity for the **ultrametric projective norm**:

  `π_max(x) = inf { max_j ∏_i ‖m_j(i)‖ : x = ∑_j ⨂_i m_j(i) }`

This uses `max` instead of `∑`, satisfies the ultrametric triangle inequality, and the
proof uses d-orthogonal bases — no Hahn-Banach needed.

**This is a different seminorm from mathlib's `projectiveSeminorm`**, which uses `∑`:

  `π(x) = inf { ∑_j ∏_i ‖m_j(i)‖ : x = ∑_j ⨂_i m_j(i) }`

Schneider's result does NOT settle our question.

## Why a Counterexample is Elusive

A counterexample would require:

1. A **non-spherically-complete** nontrivially normed field `𝕜` (e.g., `ℂ_p`).
2. An **infinite-dimensional** seminormed `𝕜`-space `E` with poor dual (ideally `E* = {0}`).
3. Elements `v, w ∈ E` and a representation `v ⊗ w = ∑_j v_j ⊗ w_j` with
   `∑_j ‖v_j‖ · ‖w_j‖ < ‖v‖ · ‖w‖`.

Condition 3 is very restrictive: the algebraic constraint `v ⊗ w = ∑ v_j ⊗ w_j` forces
tight relationships between the `v_j` and `w_j` (as analyzed in `DirectApproach.lean`),
and naive attempts to "spread" a pure tensor into a cheaper sum always increase cost.

## Why a Positive Result is Also Elusive

Every known proof of the cross property uses Hahn-Banach (or Ingleton's theorem) at a
critical step. The algebraic approach (documented in `DirectApproach.lean`) runs into a
wrong-direction triangle inequality. No Hahn-Banach-free proof is known.

## Conclusion

The `h_bidual` hypothesis is the natural abstraction level:

- It holds automatically for all fields where we know the cross property is true.
- Removing it would require either a fundamentally new proof technique or a
  counterexample in an exotic setting (infinite-dimensional spaces over ℂ_p).
- For the mathlib PR, the result with `h_bidual` (Step 4) and the `RCLike` corollary
  (Step 5) represent the right level of generality.

## References

1. Ryan, *Introduction to Tensor Products of Banach Spaces* (Springer, 2002)
2. Defant & Floret, *Tensor Norms and Operator Ideals* (North-Holland/Elsevier, 1992)
3. Schneider, *Nonarchimedean Functional Analysis* (Springer, 2002), Prop 17.4
4. Ingleton, "The Hahn-Banach theorem for non-Archimedean-valued fields" (1952)
5. Perez-Garcia & Schikhof, *Locally Convex Spaces over Non-Archimedean Valued Fields*
   (Cambridge, 2010)
-/

-- This file is documentation only. No formal Lean content beyond the import.
-- The mathematical analysis above supports the conclusion that `h_bidual` is the
-- right hypothesis for the general case, with automatic discharge over RCLike fields.
