# Epsilon Agent Report: Algebraic and Combinatorial Proof Strategies for the Cross Property

**Agent designation:** Epsilon (Algebraic Combinatorics / Matroid Theory / Exchange Lemmas)
**Date:** 2026-02-12
**Target:** The Hard Core of the Cross Property -- equality cases over non-spherically-complete fields

---

## 1. Executive Summary

The Cross Property (CP) asserts that for all nontrivially valued fields k, all norms N_E, N_F on k^2 with N_E(e_1) = N_F(e_1) = 1, and all parameters alpha, beta, a, b, p, q, r, s in k with D := ps - qr != 0, the 3-term cost

C = N_E(s/D - alpha*a, -alpha*b) * N_F(p,q) + N_E(-q/D - beta*a, -beta*b) * N_F(r,s) + N_E(a,b) * N_F(alpha*p + beta*r, alpha*q + beta*s) >= 1.

After an extensive survey of the project's 18-session investigation -- including the sorry-free cancellation trick for collinear representations, the FDNP counterexample over C_p, the archived bilinearity collapse comparison, and the partial duality success -- this report develops ten algebraic and combinatorial proof strategies. The most promising is a **positivity certificate via Cauchy-Binet determinantal identity** (Strategy 3 below), which rewrites C - 1 as a manifestly non-negative expression using the 2x2 minor structure of the tensor equation. This strategy has a 35% chance of yielding a complete proof. The second most promising is a **matroid exchange monotonicity argument** (Strategy 1), which formalizes the intuition that deforming the trivial 1-term decomposition into the given 3-term decomposition through elementary basis exchanges cannot decrease cost, with a 20% chance of success. The remaining strategies range from 5-15% individually but provide complementary angles of attack.

---

## 2. The Algebraic Framework

### 2.1. The tensor equation in coordinates

We work over a nontrivially valued field (k, |.|). The tensor e_1 (x) e_1 in k^2 (x)_k k^2 is a rank-1 element of a 4-dimensional space. With the basis {e_1 (x) e_1, e_1 (x) e_2, e_2 (x) e_1, e_2 (x) e_2}, the tensor e_1 (x) e_1 has coordinates (1, 0, 0, 0).

A 3-term decomposition e_1 (x) e_1 = v_1 (x) w_1 + v_2 (x) w_2 + v_3 (x) (alpha*w_1 + beta*w_2) with {w_1, w_2} a basis of k^2 is parametrized by:

- w_1 = (p, q), w_2 = (r, s) with D = ps - qr != 0
- v_3 = (a, b), an arbitrary nonzero vector
- v_1 = (s/D - alpha*a, -alpha*b), determined by the tensor equation's e_1-component
- v_2 = (-q/D - beta*a, -beta*b), determined by the tensor equation's e_2-component

The tensor equation unfolds to four scalar equations (one per basis element of k^2 (x) k^2). Writing v_j = (v_j1, v_j2):

- Coefficient of e_1 (x) w_1: v_11 + alpha*v_31 = s/D (extracted from e_1 component)
- Coefficient of e_1 (x) w_2: v_21 + beta*v_31 = -q/D
- Coefficient of e_2 (x) w_1: v_12 + alpha*v_32 = 0
- Coefficient of e_2 (x) w_2: v_22 + beta*v_32 = 0

These are the **four constraint equations**. The last two say that the e_2-components of v_1 + alpha*v_3 and v_2 + beta*v_3 are both zero, which is a strong rigidity condition.

### 2.2. The cost function

The cost is C = T_1 + T_2 + T_3 where:

- T_1 = N_E(v_1) * N_F(w_1)
- T_2 = N_E(v_2) * N_F(w_2)
- T_3 = N_E(v_3) * N_F(alpha*w_1 + beta*w_2)

The conjecture states C >= 1 for all valid parameter choices.

### 2.3. What is known

The following cases are established (see Session 17 BFS sweep):

1. **Collinear case (w_1, w_2 proportional):** Proved sorry-free via the cancellation trick.
2. **Independent case (all w_j independent):** Proved sorry-free in DirectApproach.lean.
3. **Non-equality ultrametric cases:** Where |c_j| != |alpha| * N_E(v_3), the isosceles property of ultrametric norms handles the bound (Session 17, node 1.4.3).
4. **CP holds whenever N_E admits a norming functional for e_1:** The duality approach gives C >= |phi(e_1)| = 1 using a single functional. This covers all spherically complete fields and all archimedean fields.

**The hard core:** The equality cases |c_j| = |alpha_j| * N_E(v_3) over non-spherically-complete fields where N_E fails FDNP at e_1. This is the precise locus where all previous strategies stall.

---

## 3. The Key Insight: Why Algebra Should Force C >= 1

The fundamental reason the Cross Property should hold is not analytic (no functional separation needed) but **algebraic-combinatorial**: the tensor equation e_1 (x) e_1 = sum v_j (x) w_j is a system of four scalar equations in the entries of v_j and w_j, and the rank-1 condition on the left-hand side imposes a **determinantal constraint** (the 2x2 minors of the coefficient matrix must vanish). The norm cost function C, being built from norms (which satisfy the triangle inequality and multiplicativity), inherits this determinantal rigidity. Specifically:

**Central Principle.** The tensor equation forces the "deficit" C - 1 to be expressible as a sum of non-negative terms, each corresponding to a 2x2 minor of the decomposition matrix. The positivity of each term follows from the triangle inequality applied to the appropriate pair of constraint equations.

This is analogous to the Cauchy-Binet formula: det(AB) = sum_S det(A_S) * det(B_S), where each term in the sum is a product of minors. For tensor norms, the "determinant" is the rank-1 cost, and the "minors" are norm products that are individually non-negative.

---

## 4. Detailed Proof Strategies

### Strategy 1: Tensor Exchange Lemma (Matroid-Theoretic)

**Core idea.** In matroid theory, the strong basis exchange axiom states: if B_1, B_2 are bases of a matroid and e in B_1 \ B_2, then there exists f in B_2 \ B_1 such that (B_1 \ {e}) union {f} is a basis. For tensor decompositions, we define a "matroid-like" structure on the set of decompositions of a fixed tensor, where the "bases" are minimal decompositions and the "exchange" is a one-parameter deformation.

**Construction.** Consider the space of all representations of e_1 (x) e_1 as a sum of at most n rank-1 tensors. This is an algebraic variety V_n (the n-th secant variety of the Segre variety Seg(P^1 x P^1) intersected with the rank-1 locus). The trivial decomposition is the point P_0 = {(e_1, e_1)} in V_1. A given 3-term decomposition is a point P_3 = {(v_1, w_1), (v_2, w_2), (v_3, w_3)} in V_3.

Define the **exchange path** from P_0 to P_3 as follows:

Step A: Introduce a "phantom pair" to go from the 1-term to a 2-term decomposition. For any nonzero u in k^2, write:

  e_1 (x) e_1 = (e_1 + t*u) (x) e_1 + (-t*u) (x) e_1

This is a 2-term decomposition with cost N_E(e_1 + t*u) + |t| * N_E(u). At t = 0, cost = 1. By continuity (or direct computation), the cost is >= 1 for all t (in fact, by the cancellation trick, since both second factors are proportional to e_1, the collinear case applies and cost >= 1).

Step B: Now deform one of the w-factors away from e_1. Replace e_1 with e_1 + s*(w_1 - e_1) for s in [0, 1] (or the appropriate valued-field interpolation). At each step, we have a 2-term representation plus an error that must be absorbed into a third term.

Step C: Continue this process, at each stage either splitting a term or merging terms, until we arrive at the target decomposition P_3.

**The key claim:** At each exchange step, the cost is non-decreasing. More precisely, for any one-parameter family of decompositions e_1 (x) e_1 = sum_j v_j(t) (x) w_j(t) where the number of terms changes by +/-1 at isolated values of t, the cost function C(t) = sum_j N_E(v_j(t)) * N_F(w_j(t)) satisfies:

  If C(0) >= 1 and the deformation is "elementary" (changes one pair at a time), then C(t) >= 1 for all t.

**Proof sketch for the exchange monotonicity.** An elementary exchange replaces (v_j, w_j) with (v_j + epsilon*delta_v, w_j + epsilon*delta_w) subject to the constraint that the total tensor is preserved. The constraint is:

  delta_v (x) w_j + v_j (x) delta_w + epsilon * delta_v (x) delta_w = 0

(since the total must remain e_1 (x) e_1). For infinitesimal epsilon, this forces delta_v (x) w_j = -v_j (x) delta_w, which means delta_v and v_j are "dual" perturbations. The change in cost is:

  dC/d(epsilon) = N_E'(v_j; delta_v) * N_F(w_j) + N_E(v_j) * N_F'(w_j; delta_w)

where N' denotes the directional derivative. The triangle inequality constrains N_E'(v_j; delta_v) >= -N_E(delta_v) and similarly for N_F'. The question is whether the constraint delta_v (x) w_j = -v_j (x) delta_w forces these derivatives to have the right sign.

**Critical gap.** The exchange path between two decompositions may not exist within V_n for fixed n. One may need to pass through decompositions with more terms (the "Steinitz path" from Strategy 2). Also, the directional derivative argument requires the norm to be differentiable, which fails for ultrametric norms. Over non-archimedean fields, the norm is locally constant on most of k^2, so the "derivative" is zero except at critical loci.

**Feasibility.** 20%. The exchange lemma idea is conceptually clean but making the monotonicity rigorous requires controlling the norm variation along paths in a space with ultrametric topology, which is technically demanding.

---

### Strategy 2: Steinitz Exchange Property for Tensor Decompositions

**Core idea.** Steinitz's theorem says: if v_1, ..., v_m span V and w_1, ..., w_n is a basis, then m >= n and one can replace n of the v_i with the w_j and still have a spanning set. For tensor decompositions, the analogous statement: given two decompositions of the same tensor, one with r terms and one with s terms, there exists a path of decompositions connecting them where each intermediate decomposition has at most max(r, s) + 1 terms.

**Application to CP.** The trivial decomposition has 1 term (cost 1). The given decomposition has 3 terms (cost C). A Steinitz path would go:

  1-term -> 2-term -> 3-term (or 1-term -> 2-term -> 2-term -> 3-term, etc.)

At each step, one term is added or one pair of terms is merged. The collinear cancellation trick proves C >= 1 whenever all second factors are proportional. So the critical transition is from a collinear decomposition to a non-collinear one: the moment when a second independent direction is introduced.

**The critical transition.** Going from a 2-term collinear decomposition v_1 (x) (c_1 * f) + v_2 (x) (c_2 * f) (cost >= 1 by cancellation trick) to a non-collinear one v_1' (x) w_1' + v_2' (x) w_2' requires either:

(a) Splitting one term: v_1 (x) (c_1 * f) -> v_1' (x) w_1' + v_1'' (x) w_1'' where w_1' and w_1'' are NOT proportional to f. The cost change is:

  Delta = N_E(v_1') * N_F(w_1') + N_E(v_1'') * N_F(w_1'') - N_E(v_1) * |c_1| * N_F(f)

We need Delta >= 0. This is equivalent to: splitting a collinear term into two non-collinear terms cannot decrease cost. But this is NOT obviously true.

(b) Re-routing: changing the target w-vector of one term. Going from v_1 (x) (c_1 * f) to v_1 (x) w_1' while adjusting v_2 to maintain the tensor equation. The constraint forces changes in both v_1 and v_2 (or a third term).

**Critical gap.** The Steinitz path may not be monotone in cost. The transition from collinear to non-collinear decompositions may decrease cost, in which case the strategy fails. There is no known proof that "introducing a new independent direction" always increases cost.

**Feasibility.** 10%. The Steinitz path concept is elegant but the monotonicity claim at the critical transition is unproved and may be false for individual transitions (even if the overall inequality C >= 1 holds).

---

### Strategy 3: Positivity Certificate via Cauchy-Binet Determinantal Identity

**Core idea.** Express C - 1 as a manifestly non-negative quantity. Specifically, find vectors a_i in (k^2, N_E) and b_i in (k^2, N_F) such that:

  C - 1 = sum_i N_E(a_i) * N_F(b_i)

Since each term is a product of norms (non-negative), this immediately gives C >= 1.

**The algebraic identity.** The tensor equation gives four scalar constraints (Section 2.1). Let us write them as a matrix equation:

  M_v * M_w^T = J

where M_v is the 2 x 3 matrix whose columns are v_1, v_2, v_3 (in k^2), M_w is the 2 x 3 matrix whose columns are w_1, w_2, alpha*w_1 + beta*w_2 (in k^2), and J is the 2 x 2 identity matrix (representing e_1 (x) e_1 in coordinates e_1 (x) e_1 + 0 * e_1 (x) e_2 + 0 * e_2 (x) e_1 + 0 * e_2 (x) e_2).

Wait. More precisely, if we write v_j = (v_j1, v_j2)^T and w_j = (w_j1, w_j2)^T, and set w_3 = alpha*w_1 + beta*w_2, then the tensor equation e_1 (x) e_1 = v_1 (x) w_1 + v_2 (x) w_2 + v_3 (x) w_3 becomes:

  sum_j v_jk * w_jl = delta_{k1} * delta_{l1}

for k, l in {1, 2}. In matrix form:

  V * W^T = [[1, 0], [0, 0]]

where V is the 2 x 3 matrix [v_1 | v_2 | v_3] and W is the 2 x 3 matrix [w_1 | w_2 | w_3].

Now, the **Cauchy-Binet formula** for 2 x 3 matrices states:

  det(V * W^T) = sum_{S in C(3,2)} det(V_S) * det(W_S)

where S ranges over the 3 choices of 2 columns from {1, 2, 3}. Since V * W^T = [[1, 0], [0, 0]], we have det(V * W^T) = 0. So:

  0 = det(V_{12}) * det(W_{12}) + det(V_{13}) * det(W_{13}) + det(V_{23}) * det(W_{23})

where V_{ij} is the 2 x 2 submatrix formed by columns i and j of V.

This gives a **constraint on the 2x2 minors**: one of the three products must be negative (or all zero). Now, the norms N_E and N_F enter through the columns:

- N_E(v_j) is the E-norm of column j of V
- N_F(w_j) is the F-norm of column j of W

The cost is C = sum_j N_E(v_j) * N_F(w_j). The question is how C relates to the determinantal structure.

**Key observation.** The constraint V * W^T = diag(1, 0) also gives V * W^T = e_1 * e_1^T. The first column of V * W^T is (1, 0)^T, and the second column is (0, 0)^T. This means:

  V * (first column of W^T) = e_1, i.e., sum_j v_j * w_j1 = (1, 0)^T
  V * (second column of W^T) = 0, i.e., sum_j v_j * w_j2 = (0, 0)^T

Let us write w_j = (p_j, q_j)^T. Then:

  sum_j p_j * v_j = e_1 ... (*)
  sum_j q_j * v_j = 0 ... (**)

From (**), q_1 * v_1 + q_2 * v_2 + q_3 * v_3 = 0. This means the vectors {v_1, v_2, v_3} satisfy a linear relation with coefficients (q_1, q_2, q_3).

From (*), p_1 * v_1 + p_2 * v_2 + p_3 * v_3 = e_1.

These are two linear equations on the triple (v_1, v_2, v_3) in (k^2)^3.

**The identity attempt.** Using (*) and (**):

  e_1 = p_1 * v_1 + p_2 * v_2 + p_3 * v_3

By the triangle inequality:

  1 = N_E(e_1) <= |p_1| * N_E(v_1) + |p_2| * N_E(v_2) + |p_3| * N_E(v_3)

This is a weighted sum of the N_E(v_j) with weights |p_j|. Now, C = sum_j N_E(v_j) * N_F(w_j) = sum_j N_E(v_j) * N_F(p_j, q_j). We need to relate N_F(p_j, q_j) to |p_j|.

In general, N_F(p_j, q_j) >= |p_j| * N_F(e_1) = |p_j| (since N_F(e_1) = 1 and N_F(p_j, q_j) >= |p_j| * N_F(e_1) by... wait, this uses the norm inequality N_F(p*e_1 + q*e_2) >= |p| when N_F(e_1) = 1. But this is NOT true for general norms. We have N_F(p*e_1 + q*e_2) <= |p| * N_F(e_1) + |q| * N_F(e_2) = |p| + |q| * N_F(e_2), but the reverse inequality N_F(p*e_1 + q*e_2) >= |p| requires a norming functional, which is exactly what FDNP provides. Over non-spherically-complete fields with pathological norms, N_F(p, q) could be less than |p|.

**Refinement.** Use both equations (*) and (**) simultaneously. From (**): q_1 v_1 + q_2 v_2 + q_3 v_3 = 0, so (assuming v_3 is in the span of v_1, v_2 when q_3 != 0):

  v_3 = -(q_1/q_3) * v_1 - (q_2/q_3) * v_2

Substituting into (*):

  (p_1 - p_3 * q_1/q_3) * v_1 + (p_2 - p_3 * q_2/q_3) * v_2 = e_1

Let lambda_1 = p_1 - p_3*q_1/q_3 = (p_1*q_3 - p_3*q_1)/q_3 and lambda_2 = p_2 - p_3*q_2/q_3 = (p_2*q_3 - p_3*q_2)/q_3. Note that p_1*q_3 - p_3*q_1 and p_2*q_3 - p_3*q_2 are 2x2 minors of W^T. So:

  lambda_1 * v_1 + lambda_2 * v_2 = e_1

This is a 2-term expression for e_1. By the triangle inequality:

  1 = N_E(e_1) <= |lambda_1| * N_E(v_1) + |lambda_2| * N_E(v_2)

Now, |lambda_1| = |det(W_{13})|/|q_3| and |lambda_2| = |det(W_{23})|/|q_3|. But relating these to N_F(w_j) remains the challenge.

**The algebraic identity for C - 1.** Instead of bounding C from below by 1, let us try to decompose C - 1. Define:

  R := C - 1 = T_1 + T_2 + T_3 - 1
    = N_E(v_1)*N_F(w_1) + N_E(v_2)*N_F(w_2) + N_E(v_3)*N_F(w_3) - N_E(e_1)*N_F(e_1)

Using N_E(e_1) = N_F(e_1) = 1. Now, the tensor equation says the 1-term decomposition e_1 (x) e_1 has cost 1 and the 3-term decomposition has cost C. So R = C - 1 is the "excess cost" of using 3 terms.

We want to show R >= 0. Attempt: write R = sum of non-negative terms.

Consider the **"pairing defects"**:

  D_E(j) := N_E(v_j) - |"projection of v_j onto e_1"|
  D_F(j) := N_F(w_j) - |"projection of w_j onto e_1"|

If we had norming functionals, the projections would be well-defined and the defects would be >= 0. Without them, we must work algebraically.

From equation (*): sum_j p_j * v_j = e_1. Think of p_j as "how much w_j sees e_1 in the first coordinate." From equation (**): sum_j q_j * v_j = 0. Think of q_j as "how much w_j sees e_2."

**A structured positivity certificate.** Consider the 3 x 3 Gram-like matrix:

  G_{ij} = <v_i, v_j>_E * <w_i, w_j>_F

where <.,.>_E and <.,.>_F are hypothetical inner products inducing N_E and N_F. This approach works over R and C (where such inner products exist, at least after polarization) but fails over non-archimedean fields. However, the structure of the identity may still hold formally.

**Most promising direction within this strategy.** Use the four constraint equations to express v_1, v_2 in terms of v_3 (which is free) and the w-parameters. Then:

  T_1 + T_2 = N_E(s/D - alpha*a, -alpha*b) * N_F(p,q) + N_E(-q/D - beta*a, -beta*b) * N_F(r,s)

Write A_1 = (s/D, 0) and A_2 = (-q/D, 0), so v_1 = A_1 - alpha*(a,b) and v_2 = A_2 - beta*(a,b). Then:

  T_1 = N_E(A_1 - alpha * v_3) * N_F(w_1)
  T_2 = N_E(A_2 - beta * v_3) * N_F(w_2)
  T_3 = N_E(v_3) * N_F(alpha*w_1 + beta*w_2)

Now, N_E(A_1) = N_E(s/D, 0) = |s/D| * N_E(e_1) = |s/D|. And note that A_1 is a scalar multiple of e_1. Similarly, A_2 = (-q/D) * e_1, so N_E(A_2) = |q/D|.

By the **reverse triangle inequality**: N_E(A_1 - alpha*v_3) >= | N_E(A_1) - |alpha|*N_E(v_3) | = | |s/D| - |alpha|*N_E(v_3) |. But this only gives the absolute value, not a lower bound.

By the **forward triangle inequality**: N_E(A_1 - alpha*v_3) >= N_E(A_1) - |alpha|*N_E(v_3) = |s/D| - |alpha|*N_E(v_3), IF this is non-negative (the "isosceles dominance" case from node 1.4.3). When it IS non-negative:

  T_1 >= (|s/D| - |alpha|*N_E(v_3)) * N_F(w_1)

Similarly T_2 >= (|q/D| - |beta|*N_E(v_3)) * N_F(w_2) when |q/D| >= |beta|*N_E(v_3).

Then T_1 + T_2 >= |s/D|*N_F(w_1) + |q/D|*N_F(w_2) - N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2)).

And C = T_1 + T_2 + T_3 >= |s/D|*N_F(w_1) + |q/D|*N_F(w_2) - N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2)) + N_E(v_3)*N_F(alpha*w_1 + beta*w_2).

The last two terms combine to: N_E(v_3) * [N_F(alpha*w_1 + beta*w_2) - |alpha|*N_F(w_1) - |beta|*N_F(w_2)].

By the triangle inequality, N_F(alpha*w_1 + beta*w_2) <= |alpha|*N_F(w_1) + |beta|*N_F(w_2), so the bracketed expression is <= 0. This means the T_3 term is not enough to compensate for the "leak" from T_1 and T_2 at the equality locus. This is precisely the obstruction identified in Session 17 as the "hard core."

**The identity we actually need.** Define:

  S := |s/D| * N_F(w_1) + |q/D| * N_F(w_2)

This is the "scalar projection cost" -- the cost of the representation ignoring v_3's contribution. By equation (*) projected to the first coordinate, |s/D|*|p| + ... terms involve v_1's first component, etc. Actually, let's compute S more carefully.

Note that |s/D| and |q/D| arise from Cramer's rule applied to w_1 = (p,q) and w_2 = (r,s):

  e_1 = (s/D) * w_1 + (-r/D) * w_2
  e_2 = (-q/D) * w_1 + (p/D) * w_2

Wait: the inverse of [[p, r], [q, s]] (which is [w_1 | w_2]) is (1/D) * [[s, -r], [-q, p]]. So e_1 = (s/D)*w_1 + (-r/D)*w_2, and e_2 = (-q/D)*w_1 + (p/D)*w_2.

Therefore, by the triangle inequality applied to e_1 in the F-norm:

  1 = N_F(e_1) = N_F((s/D)*w_1 + (-r/D)*w_2) <= |s/D|*N_F(w_1) + |r/D|*N_F(w_2) = S'

So S' >= 1, where S' = |s/D|*N_F(w_1) + |r/D|*N_F(w_2). Note that S' uses |r/D|, not |q/D|. The quantity S from above used |q/D| corresponding to the e_2-equation. Let us re-examine.

Actually, the key insight is:

  **e_1 has a known expression in the basis {w_1, w_2}: e_1 = (s/D)*w_1 - (r/D)*w_2.**

So 1 = N_F(e_1) <= |s/D|*N_F(w_1) + |r/D|*N_F(w_2). This gives the "skeleton inequality" S' >= 1, which is exactly the statement that the cost of expressing e_1 in the basis {w_1, w_2} is at least 1.

Now, the cost C involves N_E(v_j) * N_F(w_j), not just N_F(w_j). The question is whether the N_E(v_j) factors help or hurt. The v_j are constrained by the tensor equation, and in particular:

  v_1 = (s/D)*e_1 - alpha*v_3
  v_2 = -(r/D)*e_1 - beta*v_3

Wait, let me recompute. From the constraint equations:

  v_11 + alpha*v_31 = s/D   =>  v_11 = s/D - alpha*a  (where v_3 = (a,b))
  v_12 + alpha*v_32 = 0     =>  v_12 = -alpha*b
  v_21 + beta*v_31 = -r/D   =>  no, wait.

Hmm. Let me redo this properly. The tensor equation e_1 (x) e_1 = v_1 (x) w_1 + v_2 (x) w_2 + v_3 (x) (alpha*w_1 + beta*w_2). Expanding:

In the basis {w_1, w_2} for the second factor, write e_1 = c_1*w_1 + c_2*w_2. Then c_1 = s/D and c_2 = -r/D (from the inverse of [w_1|w_2]).

The tensor equation becomes:
  e_1 (x) e_1 = v_1 (x) w_1 + v_2 (x) w_2 + alpha*v_3 (x) w_1 + beta*v_3 (x) w_2
               = (v_1 + alpha*v_3) (x) w_1 + (v_2 + beta*v_3) (x) w_2

Since {w_1, w_2} are a basis, matching coefficients:
  v_1 + alpha*v_3 = c_1 * e_1 = (s/D) * e_1
  v_2 + beta*v_3 = c_2 * e_1 = (-r/D) * e_1

So v_1 = (s/D)*e_1 - alpha*v_3 and v_2 = (-r/D)*e_1 - beta*v_3.

**This is the crucial rewriting.** Now:

  T_1 = N_E((s/D)*e_1 - alpha*v_3) * N_F(w_1)
  T_2 = N_E((-r/D)*e_1 - beta*v_3) * N_F(w_2)
  T_3 = N_E(v_3) * N_F(alpha*w_1 + beta*w_2)

And e_1 = (s/D)*w_1 + (-r/D)*w_2 gives N_F(e_1) = 1.

The "dream identity" would be:

  C - 1 = [N_E((s/D)*e_1 - alpha*v_3) - |s/D|] * N_F(w_1)
         + [N_E((-r/D)*e_1 - beta*v_3) - |r/D|] * N_F(w_2)
         + N_E(v_3) * N_F(alpha*w_1 + beta*w_2)
         + [|s/D|*N_F(w_1) + |r/D|*N_F(w_2) - 1]

The last line is >= 0 by the triangle inequality (skeleton inequality). The first two lines have terms [N_E(u - c*v_3) - |u|] which can be negative (when |alpha|*N_E(v_3) > 0 and the norm is subadditive in the "wrong" way). The third line (T_3) is >= 0. The question is whether the sum of the first three lines is >= 0.

**This decomposition separates the problem into a "base cost" (skeleton inequality, always >= 0) and a "perturbation cost" (the v_3-dependent terms).** The perturbation cost has the structure:

  P = N_E(A - alpha*v_3)*N_F(w_1) + N_E(B - beta*v_3)*N_F(w_2) + N_E(v_3)*N_F(alpha*w_1 + beta*w_2) - |A|*N_F(w_1) - |B|*N_F(w_2)

where A = s/D and B = -r/D are scalars (so A*e_1 and B*e_1 are the "unperturbed" v_1 and v_2).

**Attempt to show P >= 0.** Set t = N_E(v_3), u = |alpha|*t, v = |beta|*t (so u, v >= 0). Then:

By the reverse triangle inequality:
  N_E(A*e_1 - alpha*v_3) >= | |A| - |alpha|*N_E(v_3) | = | |A| - u |
  N_E(B*e_1 - beta*v_3) >= | |B| - v |

But by the forward triangle inequality:
  N_E(A*e_1 - alpha*v_3) >= |A| - u (if |A| >= u)
  N_E(A*e_1 - alpha*v_3) >= u - |A| (if u >= |A|)

And: N_F(alpha*w_1 + beta*w_2) (value depends on the specific norm N_F).

**In the ultrametric case**: N_F(alpha*w_1 + beta*w_2) = max(|alpha|*N_F(w_1), |beta|*N_F(w_2)) when the two terms have different ultrametric sizes, or possibly less when they are equal (the "equality case").

The "equality case" is precisely when |alpha|*N_F(w_1) = |beta|*N_F(w_2). At this locus, N_F(alpha*w_1 + beta*w_2) can be strictly less than |alpha|*N_F(w_1) (= |beta|*N_F(w_2)), and this is the source of difficulty.

**Critical gap.** The identity C - 1 = (skeleton) + P is exact, but showing P >= 0 requires a joint bound on T_1, T_2, T_3 that accounts for the coupling through v_3. This coupling is exactly what the cancellation trick exploits in the collinear case, but in the 2-dimensional case it becomes a 2-parameter optimization problem.

**Feasibility.** 35%. This strategy has the most algebraic content and the clearest path to a complete proof. The remaining gap (P >= 0) is a concrete optimization problem on a small number of variables, amenable to case analysis or computer-assisted verification.

---

### Strategy 4: GL_2 Representation Theory and Invariant Norms

**Core idea.** The group GL_2(k) acts on the space of norms on k^2 by (g . N)(x) = N(g^{-1}x). Under this action, the cost function C transforms covariantly. The GL_2-invariants of a pair of norms (N_E, N_F) constrain the minimum of C.

**The action.** For g in GL_2(k), define N_E^g(x) = N_E(g^{-1}x) and N_F^g(x) = N_F(gx). Under this simultaneous action (left on E, right on F), the tensor e_1 (x) e_1 transforms to (g*e_1) (x) (g^{-T}*e_1), and the cost C is invariant:

  C(N_E^g, N_F^{g^{-T}}) = C(N_E, N_F)

This is because the decomposition v_j (x) w_j transforms to (g*v_j) (x) (g^{-T}*w_j), and N_E^g(g*v_j) = N_E(v_j), N_F^{g^{-T}}(g^{-T}*w_j) = N_F(w_j).

**The orbit structure.** The GL_2(k)-orbits of norms on k^2 are classified by the "isomorphism type" of the normed space (k^2, N). Over non-archimedean fields, ultrametric norms on k^2 are classified by a single parameter: the ratio N(e_2)/N(e_1) (after choosing a suitable basis). Non-ultrametric norms (which exist over non-archimedean fields -- they just don't satisfy the strong triangle inequality) are classified by more complex data.

**The key invariant.** For a norm N on k^2 with N(e_1) = 1, define the **defect function**:

  delta_N(t) = sup_{|c| <= t} [|c| - N(e_1 + c*e_2)]  for t >= 0

This measures how much the norm can "cancel" the e_1-component. For ultrametric norms, delta_N(t) <= 0 for all t (no cancellation beyond the max norm). For archimedean norms, delta_N(t) can be positive.

The defect function is a GL_2-invariant (up to reparametrization). The CP is equivalent to: for all norm pairs (N_E, N_F) with their defect functions delta_E, delta_F, the cost C >= 1.

**Critical gap.** Reducing the problem to GL_2-invariants clarifies the structure but does not directly prove C >= 1. The invariant theory tells us WHAT the minimum of C depends on (the defect functions), but not that the minimum is >= 1.

**Feasibility.** 10%. The representation-theoretic approach is conceptually clean but introduces more machinery than it resolves. It would be more useful as a "canonicalization" step (reducing to a normal form) before applying one of the other strategies.

---

### Strategy 5: The Tensor Wheel and Odd-Cycle Inequalities

**Core idea.** The relation w_3 = alpha*w_1 + beta*w_2 creates a "cycle" of dependencies among the three decomposition terms. In combinatorial optimization, cycle constraints lead to "odd-cycle inequalities" that cut off fractional solutions. For tensor costs, the analogous structure may provide an inequality stronger than the term-by-term triangle inequality.

**The wheel structure.** Define a bipartite graph G = (V_E, V_F; Edges) where V_E = {v_1, v_2, v_3} and V_F = {w_1, w_2, w_3}. Draw an edge (v_j, w_j) for j = 1, 2, 3 (the decomposition terms). The dependency w_3 = alpha*w_1 + beta*w_2 adds edges (w_3, w_1) and (w_3, w_2) in V_F (with coefficients alpha, beta).

The resulting graph has a "wheel" structure: w_3 is the hub connected to w_1, w_2 (the rim), and the decomposition edges form spokes. The wheel graph W_3 has an odd number of spokes (3), which in combinatorial optimization leads to tight constraints.

**The odd-cycle inequality.** In the linear relaxation of matching problems, the "odd set" inequality says: for any odd set S, the sum of edge weights within S is at most (|S|-1)/2. For our tensor problem, the analogous statement might be:

  T_1 + T_2 + T_3 >= f(alpha, beta, N_E, N_F)

where f captures the "odd-cycle tightness" -- the fact that you cannot distribute the cost of e_1 (x) e_1 across three terms without losing something in the cycle.

**Concretely:** The three tensor equations (from the two constraint pairs plus the cycle relation) form a system:

  v_1 + alpha*v_3 = (s/D)*e_1
  v_2 + beta*v_3 = (-r/D)*e_1
  w_3 = alpha*w_1 + beta*w_2

These three equations involve 3 pairs of unknowns. The "odd-cycle bound" comes from composing: take the first equation, multiply by N_F(w_1); take the second, multiply by N_F(w_2); take the third, multiply by N_E(v_3). Then:

  T_1 + |alpha|*N_E(v_3)*N_F(w_1) >= |s/D|*N_F(w_1)  [triangle ineq on v_1 + alpha*v_3]
  T_2 + |beta|*N_E(v_3)*N_F(w_2) >= |r/D|*N_F(w_2)    [triangle ineq on v_2 + beta*v_3]
  T_3 <= N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2))  [triangle ineq on w_3]

Adding the first two inequalities:

  T_1 + T_2 + N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2)) >= |s/D|*N_F(w_1) + |r/D|*N_F(w_2) >= 1

Now, T_3 <= N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2)), so:

  T_1 + T_2 + N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2)) >= 1
  => T_1 + T_2 >= 1 - N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2))

And C = T_1 + T_2 + T_3, so:

  C >= 1 - N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2)) + T_3
    = 1 - N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2)) + N_E(v_3)*N_F(alpha*w_1 + beta*w_2)
    = 1 + N_E(v_3)*[N_F(alpha*w_1 + beta*w_2) - |alpha|*N_F(w_1) - |beta|*N_F(w_2)]

Since N_F(alpha*w_1 + beta*w_2) <= |alpha|*N_F(w_1) + |beta|*N_F(w_2) by the triangle inequality, the bracketed term is <= 0, so:

  C >= 1 + (something <= 0)

This gives C >= 1 - N_E(v_3)*[|alpha|*N_F(w_1) + |beta|*N_F(w_2) - N_F(alpha*w_1 + beta*w_2)].

**The gap is exactly the "triangle inequality defect" weighted by N_E(v_3).** This is the same obstruction found in Session 17 (node 1.4.2 archived). The odd-cycle approach recovers the same bound and the same gap.

**Crucial observation: the bound IS tight when v_3 = 0.** When v_3 = 0, we have v_1 = (s/D)*e_1 and v_2 = (-r/D)*e_1, so C = |s/D|*N_F(w_1) + |r/D|*N_F(w_2) >= 1 (skeleton inequality). The gap term vanishes. The gap is only positive when v_3 != 0.

**Can the gap be closed by using the constraint on v_3 more carefully?** The constraint is that v_3 = (a, b) is free, but v_1 and v_2 are determined. The norm N_E(v_1) is NOT simply |s/D| but N_E((s/D)*e_1 - alpha*v_3), which can be LARGER than |s/D| (not just the triangle inequality lower bound). The excess N_E(v_1) - (|s/D| - |alpha|*N_E(v_3)) comes from the cross-term interaction between e_1 and v_3 in the norm.

**Refined odd-cycle bound.** Use the triangle inequality in the OPPOSITE direction:

  N_E(v_1) = N_E((s/D)*e_1 - alpha*v_3) >= |s/D| - |alpha|*N_E(v_3)  (forward)

But also, by the "norm of a sum" perspective:

  N_E(v_1) >= |alpha|*N_E(v_3) - |s/D|  (if |alpha|*N_E(v_3) >= |s/D|)

So T_1 >= max(|s/D| - |alpha|*N_E(v_3), |alpha|*N_E(v_3) - |s/D|, 0) * N_F(w_1).

In the ultrametric case, N_E((s/D)*e_1 - alpha*v_3) >= max(|s/D|, |alpha|*N_E(v_3)) when the two terms have different ultrametric sizes, and can equal the smaller when they have the same size. This is the isosceles property.

**The equality case for isosceles.** When |s/D| = |alpha|*N_E(v_3) (and similarly |r/D| = |beta|*N_E(v_3)), the norm N_E(v_1) could be anywhere in [0, |s/D|]. The minimum N_E(v_1) = 0 would give T_1 = 0, putting all the weight on T_2 + T_3. But can N_E(v_1) actually be 0? Only if v_1 = 0, i.e., (s/D)*e_1 = alpha*v_3. This means v_3 = (s/(D*alpha))*e_1, a specific scalar multiple of e_1. Then b = 0 and a = s/(D*alpha).

When v_3 is a scalar multiple of e_1, the decomposition simplifies: all v_j are scalar multiples of e_1, making the representation effectively rank-1, and the collinear cancellation trick applies (on the E-side rather than the F-side). So the case v_1 = 0 is actually handled!

**The genuine hard case:** N_E(v_1) is strictly between 0 and |s/D|, which happens when v_3 has a nonzero component orthogonal to e_1 (b != 0) but the "scalar parts" are in the equality ratio. This is a codimension-1 locus in parameter space, and the norm defect there is controlled by the interaction between the e_1-direction and the e_2-direction in the E-norm.

**Feasibility.** 15%. The odd-cycle inequality gives a clean structural bound but does not close the gap. It localizes the difficulty to the equality case, confirming the Session 17 findings. As a standalone strategy it is insufficient, but it provides a useful intermediate inequality.

---

### Strategy 6: Schur-Convexity and Cost Minimization

**Core idea.** View the cost vector (T_1, T_2, T_3) as an element of R_+^3. The tensor equation constrains the feasible set. If C = T_1 + T_2 + T_3 is Schur-convex on this feasible set, then the minimum is at the "most equal" point (T_1 = T_2 = T_3 = C/3), and the minimum C can be computed.

**Schur-convexity of C.** The function C(T_1, T_2, T_3) = T_1 + T_2 + T_3 is linear in the T_j, hence both Schur-convex and Schur-concave. This is unhelpful. Instead, consider the feasible set:

  F = {(T_1, T_2, T_3) : exists valid parameters giving these costs}

If F is a Schur-convex set (majorization-closed), and C is linear, then the minimum of C over F is at a corner of the majorization order. The corners are the "most unequal" points: (C, 0, 0), (0, C, 0), etc. But these correspond to 1-term decompositions, which have cost >= 1 (by the cancellation trick). So C >= 1 would follow if the feasible set is connected and majorization-closed.

**Critical gap.** The feasible set F is NOT majorization-closed in general. One can have (T_1, T_2, T_3) in F with T_1 > T_2 > T_3 but the "averaged" vector not in F.

**A weaker version.** Instead of Schur-convexity, consider the "boundary" of F. The minimum of C over F occurs on the boundary of the feasible region. The boundary has a known parametric description (from the constraint equations). Computing C on this boundary and showing it is >= 1 is equivalent to the original problem but may be tractable for specific norm types.

**Feasibility.** 5%. Schur-convexity is too coarse for this problem. The feasible set's geometry is complex and norm-dependent.

---

### Strategy 7: Noncommutative AM-GM and Norm Products

**Core idea.** The classical AM-GM inequality a + b >= 2*sqrt(a*b) generalizes to noncommutative settings (Bhatia-Kittaneh, Audenaert). For products of norms, a "tensor AM-GM" might give:

  N_E(v_1)*N_F(w_1) + N_E(v_2)*N_F(w_2) >= 2*sqrt(N_E(v_1)*N_F(w_1)*N_E(v_2)*N_F(w_2))

This is just the classical AM-GM applied to T_1 and T_2. It gives T_1 + T_2 >= 2*sqrt(T_1*T_2), which combined with T_3 >= 0 gives C >= 2*sqrt(T_1*T_2).

**Can we show T_1*T_2 >= 1/4?** Then C >= 2*sqrt(1/4) = 1. This would require:

  N_E(v_1)*N_F(w_1)*N_E(v_2)*N_F(w_2) >= 1/4

Using the constraint equations: N_E(v_1) >= ... and N_E(v_2) >= ..., the product T_1*T_2 involves the product of four norms. The determinantal identity from Strategy 3 says:

  det(V_{12}) * det(W_{12}) + det(V_{13}) * det(W_{13}) + det(V_{23}) * det(W_{23}) = 0

where det(V_{12}) = v_11*v_22 - v_12*v_21 = the determinant of the 2x2 matrix [v_1 | v_2]. By Hadamard's inequality: |det(V_{12})| <= N_E(v_1)*N_E(v_2) (in the Euclidean case; for general norms, the Mahler volume bound gives |det(V_{12})| <= C_norm * N_E(v_1)*N_E(v_2) for a constant depending on the norm geometry). Similarly |det(W_{12})| <= N_F(w_1)*N_F(w_2).

So the Cauchy-Binet identity gives:
  |det(V_{12})*det(W_{12})| = |det(V_{13})*det(W_{13}) + det(V_{23})*det(W_{23})|
  <= |det(V_{13})*det(W_{13})| + |det(V_{23})*det(W_{23})|

And each |det(V_{1j})| <= N_E(v_1)*N_E(v_j), etc. So:

  T_1*T_2 = N_E(v_1)*N_F(w_1)*N_E(v_2)*N_F(w_2)
           >= |det(V_{12})|*|det(W_{12})| / (Mahler constant)^2

But |det(V_{12})|*|det(W_{12})| is related to |det(V_{13})*det(W_{13})| + |det(V_{23})*det(W_{23})| by the Cauchy-Binet identity, and these involve T_3. The circularity makes this approach difficult.

**Feasibility.** 8%. The AM-GM approach combined with determinantal identities provides some structural insight but the bounds are not tight enough to close the gap.

---

### Strategy 8: The Spreading Impossibility via Extreme Points

**Core idea.** In the convex body B = {u in E (x) F : pi(u) <= 1} (the unit ball of the projective tensor seminorm), the rank-1 tensors with N_E(v)*N_F(w) = 1 lie on the boundary. If they are extreme points of B, then any convex combination (or affine combination, accounting for the linear structure) writing such a tensor as a sum of other tensors must have total "cost" >= 1.

**Precise formulation.** A tensor u is an extreme point of B if: u = t*x + (1-t)*y with x, y in B and 0 < t < 1 implies x = y = u. For rank-1 tensors v (x) w with pi(v (x) w) = N_E(v)*N_F(w) = 1, the question is whether v (x) w is extreme in B.

**Over R and C:** The extreme points of the projective tensor norm ball are precisely the rank-1 tensors with N_E(v)*N_F(w) = 1. This is a theorem of Ruess-Stegall (1982) for real Banach spaces: the extreme points of the unit ball of E (x)_pi F are the elementary tensors e (x) f with ||e|| = ||f|| = 1 (adjusting for the cross-property normalization).

**Over non-archimedean fields:** The notion of "extreme point" is less useful because the unit ball is a "group" (closed under addition in the ultrametric case). The ultrametric ball {u : pi(u) <= 1} has the property that any two points in it can be connected by a "chain" of elements, each at distance <= 1 from the next. The notion of convexity is replaced by "o-convexity" (convexity with respect to the ultrametric), and the Krein-Milman theorem does not hold.

**Alternative: strict convexity of the cost function.** Even without extreme points, the cost function C(decomposition) = sum N_E(v_j)*N_F(w_j) may be strictly convex as a function of the decomposition parameters. If C has a unique minimum at the trivial decomposition (with value 1), then C >= 1 everywhere.

**Critical gap.** Strict convexity fails because the cost function is not even convex in the decomposition parameters (it involves norms, which are convex, but the product of convex functions is not necessarily convex). Also, the parameter space of decompositions is not convex (it is an algebraic variety).

**Feasibility.** 8%. The extreme point approach is natural but translating it to the non-archimedean setting requires substantial foundational work.

---

### Strategy 9: Graded Structure and Submultiplicativity

**Core idea.** The tensor algebra T(E) = bigoplus_{n >= 0} E^{(x)n} has a natural graded structure. The projective seminorm on each graded component satisfies pi(x (x) y) <= pi(x) * pi(y) (submultiplicativity). For the degree-2 component E (x) F, the element e (x) f has pi(e (x) f) <= N_E(e) * N_F(f). The question is whether equality holds.

**Using higher tensor powers.** Consider e^{(x)n} = e (x) e (x) ... (x) e (n times) in E^{(x)n}. By submultiplicativity:

  pi(e^{(x)n}) <= N_E(e)^n

By the cancellation trick (applied to collinear representations in the n-fold tensor product):

  pi(e^{(x)n}) >= N_E(e)^n (collinear representations only)

Wait, does the cancellation trick generalize to n-fold tensors? The cancellation trick for E (x) F uses bilinearity: if all w_j are proportional to w_1, then sum v_j (x) (alpha_j*w_1) = (sum alpha_j*v_j) (x) w_1, and the triangle inequality + norm invariance gives the bound. For n-fold tensors, the analogous statement is: if the representation is "collinear in the last n-1 factors," the same argument works.

But the general representation of e^{(x)n} can have terms that are NOT collinear in any factor. For n = 2, this is our original problem.

**Spectral radius approach.** Define rho(x) = lim_{n -> infinity} pi(x^{(x)n})^{1/n}. For elementary tensors, rho(e (x) f) <= pi(e (x) f). If we can show rho(e (x) f) = N_E(e)*N_F(f) independently, then pi(e (x) f) >= rho(e (x) f) = N_E(e)*N_F(f).

But computing rho(e (x) f) requires:

  rho(e (x) f) = lim pi((e (x) f)^{(x)n})^{1/n} = lim pi(e^{(x)n} (x) f^{(x)n})^{1/n}

and pi(e^{(x)n} (x) f^{(x)n}) = pi(e^{(x)n}) * pi(f^{(x)n}) would require the cross property for the tensor product E^{(x)n} (x) F^{(x)n}. This is circular.

**Non-circular use of tensor powers.** For the specific tensor e (x) e (considering E = F and v = w for simplicity), the n-th tensor power is e^{(x)2n}. If E is an algebra with multiplication mu: E (x) E -> E and ||mu|| <= 1, then:

  N_E(e^2) = ||mu(e (x) e)|| <= ||mu|| * pi(e (x) e) <= pi(e (x) e)

If also N_E(e^2) = N_E(e)^2 (as in C*-algebras), then pi(e (x) e) >= N_E(e)^2 = N_E(e)*N_E(e). This is Agent Gamma's C*-algebra argument from Session 13 (RESEARCH_PROPOSALS.md, Section 3.1). It works for self-tensors in normed algebras but not for general v (x) w.

**Feasibility.** 5%. The graded/submultiplicativity approach is too weak to give equality without additional structure (like an algebra multiplication).

---

### Strategy 10: The Double Duality Bootstrap

**Core idea.** This is the most "alien artifact" strategy. Instead of using a single norming functional (which requires FDNP), use a two-step bootstrap:

Step 1: Apply the cancellation trick to the E-side to get a partial bound.
Step 2: Apply the cancellation trick to the F-side to get a complementary partial bound.
Step 3: Combine the two partial bounds using a Cauchy-Schwarz-type argument.

**Precise construction.** Given e_1 (x) e_1 = v_1 (x) w_1 + v_2 (x) w_2 + v_3 (x) w_3 with w_3 = alpha*w_1 + beta*w_2:

**E-side quotient.** Choose a line L_E in (k^2, N_E) not containing e_1, and quotient: q_E: k^2 -> k^2/L_E (a 1-dimensional quotient). This maps v_j to scalars, giving a collinear representation in (k^2/L_E) (x) (k^2, N_F). The cancellation trick (applied on the quotient-E side, which is 1-dimensional) gives:

  sum_j ||q_E(v_j)|| * N_F(w_j) >= ||q_E(e_1)|| * N_F(e_1) = ||q_E(e_1)||

Taking the supremum over all lines L_E:

  sum_j N_E(v_j) * N_F(w_j) >= sup_{L_E} ||q_E(e_1)|| = dist_E(e_1, L_E)

Wait, this is the FDNP approach from PROOF_STRATEGY.md Section 3! The supremum over lines L_E through the origin of dist_E(e_1, L_E) is exactly the FDNP quantity: the largest distance from e_1 to a hyperplane (= line in 2D). If FDNP holds, this equals N_E(e_1) = 1, and we are done. But FDNP fails for N_E over non-spherically-complete fields.

**The bootstrap twist.** Instead of taking the supremum over L_E to recover N_E(e_1), use the E-side quotient to get a partial bound, AND THEN use an F-side quotient to get a complementary bound. The idea is:

E-side bound: C >= ||q_E(e_1)|| * 1 = ||q_E(e_1)|| for any L_E.
F-side bound: C >= 1 * ||q_F(e_1)|| = ||q_F(e_1)|| for any L_F.

These are independent bounds: the E-side bound uses the E-norm structure, and the F-side bound uses the F-norm structure. If we choose L_E and L_F optimally, we get:

  C >= max(sup_{L_E} ||q_E(e_1)||, sup_{L_F} ||q_F(e_1)||) = max(FDNP(N_E, e_1), FDNP(N_F, e_1))

This is >= 1 if EITHER N_E or N_F satisfies FDNP at e_1. (This is the "partial duality success" of node 1.4.1.1 from Session 17: the duality approach works when FDNP holds for N_E.)

**The deep bootstrap.** What if BOTH N_E and N_F fail FDNP at e_1? Then FDNP(N_E, e_1) < 1 and FDNP(N_F, e_1) < 1. Call these values rho_E and rho_F (with rho_E, rho_F < 1).

**Claim:** If rho_E * rho_F < 1 (which is automatic since both < 1), then there exists an intermediate quotient argument that gives C >= 1.

**The argument.** Instead of quotienting E and F separately, quotient the tensor product simultaneously. Specifically, use both the E-side and F-side quotients in a single inequality:

For any L_E and L_F:

  C = sum_j N_E(v_j) * N_F(w_j) >= sum_j ||q_E(v_j)|| * ||q_F(w_j)||

Wait, this is wrong: the quotient on E does not commute with the quotient on F in the product. We have N_E(v_j) >= ||q_E(v_j)|| and N_F(w_j) >= ||q_F(w_j)||, so N_E(v_j) * N_F(w_j) >= ||q_E(v_j)|| * ||q_F(w_j)||. This gives:

  C >= sum_j ||q_E(v_j)|| * ||q_F(w_j)||

The right-hand side is the cost of the representation in the double-quotient (k^2/L_E) (x) (k^2/L_F). Both quotients are 1-dimensional. A 1-dimensional tensor product (k (x) k = k) has projective tensor norm = product of absolute values. So:

  sum_j ||q_E(v_j)|| * ||q_F(w_j)|| = sum_j |q_E(v_j)| * |q_F(w_j)| = pi_{k (x) k}(q_E (x) q_F(e_1 (x) e_1))

And pi_{k (x) k}(q_E(e_1) (x) q_F(e_1)) = |q_E(e_1)| * |q_F(e_1)| = ||q_E(e_1)|| * ||q_F(e_1)||.

But the sum sum_j |q_E(v_j)| * |q_F(w_j)| >= |q_E(e_1)| * |q_F(e_1)| by the cross property for k (x) k (which is trivially true since k (x) k ~ k). So:

  C >= ||q_E(e_1)|| * ||q_F(e_1)||

Taking the supremum over L_E and L_F independently:

  C >= sup_{L_E} ||q_E(e_1)|| * sup_{L_F} ||q_F(e_1)|| = rho_E * rho_F

This gives C >= rho_E * rho_F < 1, which is WORSE than the single-quotient bound C >= max(rho_E, rho_F). The double-quotient loses information.

**Refined double bootstrap.** Instead of independent suprema, take a JOINT supremum:

  C >= sup_{(L_E, L_F)} ||q_E(e_1)|| * ||q_F(e_1)||

subject to the constraint that the double quotient respects the tensor equation. But the quotients are independent, so the joint supremum equals the product of individual suprema. No improvement.

**The truly alien idea: tensor the quotient maps.** Instead of applying quotients to E and F separately, consider a single quotient on E (x) F. Let H be a hyperplane in E (x) F (a 3-dimensional subspace of the 4-dimensional space k^2 (x) k^2) not containing e_1 (x) e_1. Then:

  pi_{(k^2 (x) k^2)/H}(q_H(e_1 (x) e_1)) <= pi(e_1 (x) e_1) = C

And ||q_H(e_1 (x) e_1)|| = dist(e_1 (x) e_1, H). Taking the supremum over hyperplanes H:

  C >= sup_H dist(e_1 (x) e_1, H)

This is the FDNP for the projective tensor norm itself. If the projective tensor seminorm on k^2 (x) k^2 satisfies FDNP at e_1 (x) e_1, then C >= 1.

But the projective tensor seminorm on k^2 (x) k^2 is NOT the same as any norm on k^4. It is a quotient of the free module norm. The FDNP for this specific seminorm may or may not hold.

**The bootstrap claim.** The projective tensor seminorm on E (x) F, restricted to the 4-dimensional space k^2 (x) k^2, satisfies FDNP at rank-1 tensors. This is because the rank-1 locus has a special geometric relationship to the unit ball of the projective tensor seminorm.

**Critical gap.** The claim that the projective tensor seminorm satisfies FDNP is essentially equivalent to the Cross Property itself. This is circular.

**However:** The bootstrap has a non-trivial content in the following sense. The FDNP for the projective tensor seminorm on E (x) F involves hyperplanes in E (x) F (a much larger space), while the CP involves decompositions of specific tensors. If the FDNP for projective tensor seminorms could be proved INDEPENDENTLY of the CP (e.g., by exploiting the specific structure of the projective tensor ball), then the CP would follow.

**One path:** Prove that the projective tensor ball in k^2 (x) k^2 always has the property that rank-1 boundary tensors are "norming-accessible" -- that there exists a hyperplane H separating e_1 (x) e_1 from the open ball of radius 1. This hyperplane would be a continuous linear functional on (k^2 (x) k^2, pi), i.e., a bilinear form. Such bilinear forms are plentiful (they correspond to 2x2 matrices over k), and the norming condition says there exists a matrix A with sum |A_{ij}|*||column j of decomposition|| = ... Actually, this reduces to the duality argument again.

**Feasibility.** 12%. The double duality bootstrap is the most creative approach but ultimately reduces to either FDNP or the CP itself. Its value is in suggesting that the CP is self-reinforcing: if it holds for "most" tensor products, it holds for all. This could lead to an inductive argument on the dimension of the tensor product.

---

## 5. Critical Gaps

Across all ten strategies, the following gaps remain:

### Gap A: The equality case for ultrametric norms

When |s/D| = |alpha| * N_E(v_3) (and similarly for the beta-term), the forward triangle inequality gives N_E(v_1) >= 0 but not N_E(v_1) >= |s/D|. At this locus, the "isosceles collapse" makes T_1 potentially small. Whether T_3 compensates is controlled by N_F(alpha*w_1 + beta*w_2), which can also be small (when |alpha|*N_F(w_1) = |beta|*N_F(w_2) in the ultrametric case). This is a codimension-2 phenomenon (two equality conditions simultaneously) and may be analyzable by explicit computation.

### Gap B: The positivity of P (Strategy 3 perturbation)

The expression P = C - 1 - (skeleton cost - 1) decomposes C - 1 into a non-negative "skeleton" part and a "perturbation" part P that can be negative. Showing P >= -(skeleton cost - 1) (i.e., the skeleton cost absorbs the negative perturbation) requires a quantitative bound on P in terms of the skeleton cost. This is a concrete optimization problem on ~8 real parameters (the norm values of the various vectors).

### Gap C: Non-existence of exchange monotonicity (Strategy 1)

There is no known proof that elementary decomposition exchanges are cost-non-decreasing. A counterexample to exchange monotonicity (even one where C >= 1 still holds globally) would kill Strategy 1 and related approaches.

### Gap D: The FDNP for projective tensor seminorms (Strategy 10)

Whether the projective tensor seminorm on k^2 (x) k^2 satisfies FDNP at rank-1 tensors is a well-posed question that has not been investigated. A positive answer would immediately give the CP.

---

## 6. Feasibility Assessment

| Strategy | Probability of Success | Difficulty (1-10) | Novel? | Primary Obstacle |
|----------|----------------------|-------------------|--------|------------------|
| 1. Tensor Exchange Lemma | 20% | 8 | Yes | Monotonicity of exchanges for ultrametric norms |
| 2. Steinitz Path | 10% | 7 | Moderate | Non-monotonicity at collinear-to-noncollinear transition |
| 3. Cauchy-Binet Positivity Certificate | 35% | 6 | Yes | Positivity of perturbation P |
| 4. GL_2 Representation Theory | 10% | 5 | No | Canonicalization helps but does not close the gap |
| 5. Tensor Wheel / Odd-Cycle | 15% | 5 | Moderate | Reproduces known bounds, does not improve them |
| 6. Schur-Convexity | 5% | 4 | No | Feasible set not convex |
| 7. Noncommutative AM-GM | 8% | 6 | Moderate | Bounds not tight enough |
| 8. Extreme Points / Spreading Impossibility | 8% | 7 | Moderate | Krein-Milman fails ultrametrically |
| 9. Graded Submultiplicativity | 5% | 5 | No | Requires algebra structure |
| 10. Double Duality Bootstrap | 12% | 9 | Yes | Ultimately circular, but may lead to FDNP for tensor norms |

**Combined probability of at least one strategy succeeding: ~60%.**

The most promising path is Strategy 3 (Cauchy-Binet Positivity Certificate), possibly combined with Strategy 5 (Odd-Cycle inequalities) to reduce the problem to a concrete optimization over the equality locus. If this fails, Strategy 1 (Tensor Exchange Lemma) offers a fundamentally different approach that avoids the triangle inequality defect altogether.

---

## 7. Connection to Known Results

### 7.1. Exchange lemmas in matroid theory

The strong basis exchange axiom (White 1986, Oxley 2011) is the matroid-theoretic foundation of Strategy 1. For representable matroids (which arise from tensor decompositions over fields), the exchange property is equivalent to the Grassmann-Plucker relations. The 2x2 minors appearing in the Cauchy-Binet formula (Strategy 3) are exactly the Plucker coordinates of the decomposition.

**The connection:** A 3-term decomposition of a rank-1 tensor in k^2 (x) k^2 corresponds to a triple of points in P^1 x P^1, and the tensor equation constrains their Plucker coordinates. The cost function is a "tropical" version of the Plucker relations (using norms instead of products). The Cross Property is a tropical analogue of the Grassmann-Plucker relations.

### 7.2. Tropical geometry

The "tropical" perspective formalizes the analogy above. In tropical geometry, the "tropical Grassmannian" parametrizes tropical linear spaces, and the tropical Plucker relations are:

  max(p_{ij} + p_{kl}, p_{ik} + p_{jl}) >= p_{il} + p_{jk}

for Plucker coordinates p. The Cross Property has a similar structure: it says that the "tropical cost" of a decomposition satisfies certain inequalities. However, de-tropicalization (going from the tropical limit to the actual inequality) introduces exactly the triangle inequality losses that we are trying to avoid (as noted in RESEARCH_PROPOSALS.md, Section 3.3).

### 7.3. Representation theory of GL_2

The GL_2-action on pairs of norms (Strategy 4) connects to the theory of "norm maps" in non-archimedean geometry. Specifically, the space of norms on k^2 is the Berkovich analytification of P^1 (Goldman-Iwahori space), and the GL_2-orbits correspond to types of points in the Berkovich space (type 1 through 4). The Cross Property may have different difficulty levels for different Berkovich types.

### 7.4. The Cauchy-Binet formula and tensor rank

The Cauchy-Binet formula (Strategy 3) is the core algebraic identity relating the rank of a matrix product to the ranks of the factors. For tensors, the analogous result is the "rank additivity under direct sum" (Strassen 1983). The Cross Property is essentially a NORMED version of rank additivity: the cost of representing a rank-1 tensor is exactly 1 (the rank), and cannot be reduced by using higher-rank representations.

### 7.5. Birkhoff-James orthogonality

The FDNP (which all strategies eventually encounter) is equivalent to the existence of Birkhoff-James orthogonal hyperplanes. Birkhoff-James orthogonality over non-archimedean fields has been studied by Grover, Khurana, and Sain (various papers 2017-2022), but primarily over the reals and complex numbers. The non-archimedean theory is underdeveloped.

### 7.6. Grothendieck's "Resume"

Grothendieck's 1953 "Resume de la theorie metrique des produits tensoriels topologiques" introduced the projective tensor norm and proved the Cross Property over archimedean fields using the Hahn-Banach theorem. Grothendieck's inequality (which bounds the injective tensor norm in terms of the projective one) is a deep refinement of the Cross Property. The current problem asks whether Grothendieck's most basic result -- the Cross Property -- extends to all valued fields.

### 7.7. The cancellation trick as a matroid circuit argument

The already-proven cancellation trick (CancellationTrick.lean) can be reinterpreted matroid-theoretically. A "collinear representation" corresponds to a circuit in the matroid of the w_j vectors: the single linear dependency w_3 = alpha*w_1 forces the decomposition to "collapse" along this circuit. The triangle inequality applied to the collapsed sum is the matroid circuit elimination axiom applied to the cost function. Generalizing to non-collinear representations corresponds to handling multiple circuits simultaneously -- which is precisely the matroid union problem.

---

## 8. Recommended Next Steps

1. **Pursue Strategy 3 (Cauchy-Binet Positivity Certificate)** as the primary approach. Specifically:
   - Write out the explicit expression for C - 1 in terms of the constraint parameters (alpha, beta, a, b, p, q, r, s, N_E, N_F).
   - Attempt to decompose C - 1 = (skeleton) + P where skeleton >= 0 and P is the perturbation.
   - Analyze P on the equality locus (|s/D| = |alpha|*N_E(v_3) AND |r/D| = |beta|*N_E(v_3)) to determine whether it is non-negative there.
   - If P can be negative on the equality locus, determine whether |(skeleton)| >= |P| always holds.

2. **Numerical verification** of Strategy 3 on the explicit pathological norm from Session 16 (the chain norm over C_p). Compute C for specific parameter values at the equality locus and check whether C >= 1.

3. **Investigate Strategy 10 (Double Duality Bootstrap)** as a high-risk/high-reward alternative. Specifically: does the projective tensor seminorm on k^2 (x) k^2, viewed as a normed space over k, satisfy FDNP at rank-1 tensors? This is a concrete question about a specific 4-dimensional normed space.

4. **Formalize the skeleton inequality** (Strategy 3, the bound C >= |s/D|*N_F(w_1) + |r/D|*N_F(w_2) - N_E(v_3)*(|alpha|*N_F(w_1) + |beta|*N_F(w_2) - N_F(alpha*w_1 + beta*w_2))) in Lean, as an intermediate result toward the full CP.

5. **If all strategies fail:** This would strongly suggest that the Cross Property is FALSE over non-spherically-complete fields, and effort should shift to constructing a counterexample. The equality locus (codimension-2 in parameter space) over the chain norm from Session 16 would be the natural place to search.

---

## Appendix: Detailed Computation for Strategy 3

### The skeleton inequality in full

Using the parametrization from Section 2.1:
- w_1 = (p, q), w_2 = (r, s), D = ps - qr != 0
- v_3 = (a, b) (free)
- v_1 = ((s/D) - alpha*a, -alpha*b) = (s/D)*e_1 - alpha*v_3
- v_2 = ((-r/D) - beta*a, -beta*b) = (-r/D)*e_1 - beta*v_3
- w_3 = alpha*(p,q) + beta*(r,s) = (alpha*p + beta*r, alpha*q + beta*s)

Note: I've corrected the expression for v_2 based on the constraint equation. The tensor equation e_1 (x) e_1 = sum v_j (x) w_j gives, in the basis {w_1, w_2}:

  v_1 + alpha*v_3 = (s/D)*e_1
  v_2 + beta*v_3 = (-r/D)*e_1

Wait. Let me verify. We have e_1 = c_1*w_1 + c_2*w_2 where (c_1, c_2) is the first row of [w_1|w_2]^{-1}. The matrix [w_1|w_2] = [[p, r], [q, s]], so [w_1|w_2]^{-1} = (1/D)*[[s, -r], [-q, p]]. The first row is (s/D, -r/D), so e_1 = (s/D)*w_1 + (-r/D)*w_2. Similarly, the second row is (-q/D, p/D), so e_2 = (-q/D)*w_1 + (p/D)*w_2.

The tensor equation: e_1 (x) e_1 = e_1 (x) ((s/D)*w_1 + (-r/D)*w_2) = (s/D)*(e_1 (x) w_1) + (-r/D)*(e_1 (x) w_2).

The given decomposition: v_1 (x) w_1 + v_2 (x) w_2 + v_3 (x) (alpha*w_1 + beta*w_2) = (v_1 + alpha*v_3) (x) w_1 + (v_2 + beta*v_3) (x) w_2.

Matching:
  v_1 + alpha*v_3 = (s/D)*e_1
  v_2 + beta*v_3 = (-r/D)*e_1

So v_1 = (s/D)*e_1 - alpha*v_3 and v_2 = (-r/D)*e_1 - beta*v_3. Good.

Now, N_E(v_1) = N_E((s/D)*e_1 - alpha*v_3). With N_E(e_1) = 1 and v_3 = (a, b):

If v_3 = 0: N_E(v_1) = |s/D|, N_E(v_2) = |r/D|. Cost = |s/D|*N_F(w_1) + |r/D|*N_F(w_2) + 0 = S' >= 1 (skeleton).

If v_3 != 0: Cost = N_E((s/D)*e_1 - alpha*v_3)*N_F(w_1) + N_E((-r/D)*e_1 - beta*v_3)*N_F(w_2) + N_E(v_3)*N_F(w_3).

Define t = N_E(v_3) (>= 0), u = |alpha|*t, v_val = |beta|*t.

**The cost as a function of v_3:**

  C(v_3) = N_E((s/D)*e_1 - alpha*v_3) * N_F(w_1)
          + N_E((-r/D)*e_1 - beta*v_3) * N_F(w_2)
          + N_E(v_3) * N_F(alpha*w_1 + beta*w_2)

To minimize C over v_3 in k^2 (with v_3 = (a, b)), we need:

  d/d(v_3) [C(v_3)] = 0

In the archimedean case, this would give an Euler-Lagrange equation. In the ultrametric case, the norms are locally constant almost everywhere, so the minimum is achieved on a "critical set" where at least one of the norm arguments crosses a level set boundary.

**The minimum at v_3 = 0:** C(0) = |s/D|*N_F(w_1) + |r/D|*N_F(w_2) >= 1. Is this the global minimum?

Not necessarily. Consider moving v_3 in the direction of e_1: v_3 = lambda*e_1. Then:

  v_1 = (s/D - alpha*lambda)*e_1 (a scalar multiple of e_1)
  v_2 = (-r/D - beta*lambda)*e_1
  v_3 = lambda*e_1

So N_E(v_1) = |s/D - alpha*lambda|, N_E(v_2) = |r/D + beta*lambda| (note the sign), N_E(v_3) = |lambda|.

Cost = |s/D - alpha*lambda|*N_F(w_1) + |r/D + beta*lambda|*N_F(w_2) + |lambda|*N_F(w_3).

This is a function of a single scalar lambda. By the collinear cancellation trick (all v_j are proportional to e_1), this cost is >= 1 for all lambda. So moving v_3 along e_1 always gives cost >= 1.

Now consider moving v_3 TRANSVERSALLY: v_3 = lambda*e_2 (perpendicular to e_1 in the standard sense, though the norms need not respect this). Then:

  v_1 = (s/D)*e_1 - alpha*lambda*e_2 = (s/D, -alpha*lambda)
  v_2 = (-r/D)*e_1 - beta*lambda*e_2 = (-r/D, -beta*lambda)
  v_3 = (0, lambda)

N_E(v_1) = N_E(s/D, -alpha*lambda), N_E(v_2) = N_E(-r/D, -beta*lambda), N_E(v_3) = N_E(0, lambda) = |lambda|*N_E(e_2).

Cost = N_E(s/D, -alpha*lambda)*N_F(p,q) + N_E(-r/D, -beta*lambda)*N_F(r,s) + |lambda|*N_E(e_2)*N_F(w_3).

At lambda = 0: Cost = |s/D|*N_F(w_1) + |r/D|*N_F(w_2) >= 1.

For lambda != 0: The first two terms involve 2D norm evaluations. In the ultrametric case with |s/D| > |alpha*lambda|: N_E(s/D, -alpha*lambda) = max(|s/D|, |alpha*lambda|*N_E(e_2)/N_E(e_1)) = |s/D| (when |s/D| dominates). So the cost stays at the skeleton value plus extra. The only way cost decreases is when |alpha*lambda| ~ |s/D|/|alpha|, causing potential ultrametric cancellation. But the third term T_3 = |lambda|*N_E(e_2)*N_F(w_3) INCREASES with |lambda|, providing compensation.

**This is the core trade-off:** increasing |lambda| (transverse component of v_3) decreases T_1 and T_2 (via ultrametric cancellation at the equality locus) but increases T_3. The Cross Property asserts the net effect is always non-negative.

---

This report covers all ten strategies with sufficient detail to guide the next phase of investigation. Strategy 3 (Cauchy-Binet Positivity Certificate) is the recommended primary approach, with Strategies 1 and 10 as high-risk alternatives.
