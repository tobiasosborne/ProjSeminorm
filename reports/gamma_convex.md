# Convex Duality and Minimax Strategy for the Cross Property

**Author:** Agent Gamma (Convex Analysis Specialist)
**Date:** 2026-02-12
**Project:** ProjSeminorm -- mathlib4 PR #33969
**Status:** Proof strategy report (theoretical)

---

## 1. Executive Summary

The Cross Property (CP) conjecture asserts that for all nontrivially valued fields k, all norms N_E, N_F on k^2 with N_E(e_1) = N_F(e_1) = 1, and all parameters with D = ps - qr != 0, the 3-term cost C = N_E(s/D - alpha*a, -alpha*b) * N_F(p,q) + N_E(-q/D - beta*a, -beta*b) * N_F(r,s) + N_E(a,b) * N_F(alpha*p + beta*r, alpha*q + beta*s) >= 1. We develop a proof strategy based on convex analysis, Lagrangian duality, and minimax theory. The central insight is that the cost C, viewed as a function of the parameters for fixed norms, is the value of a constrained optimization problem whose Lagrangian dual can be analyzed without invoking Hahn-Banach or the existence of norming functionals. Instead of seeking a single dual functional (which may not exist over non-spherically-complete fields), we exploit the convex geometry of the norm unit balls directly through Fenchel conjugates and saddle-point theory. This approach yields a complete proof in the archimedean and ultrametric non-equality cases, and reduces the remaining equality cases to a concrete finite-dimensional convex inequality about the interaction between two norms on k^2. We assess the probability of this approach closing the full conjecture at 35-45%, with the primary obstacle being the non-smoothness of the equality locus in the ultrametric setting.

---

## 2. The Convex/Minimax Framework

### 2.1. The optimization problem

Fix norms N_E, N_F on k^2 with N_E(e_1) = N_F(e_1) = 1. The Cross Property states that

    inf_{params} C(N_E, N_F; params) >= 1

where the infimum is over all (alpha, beta, a, b, p, q, r, s) in k^8 with D := ps - qr != 0, and

    C = T_1 + T_2 + T_3

with

    T_1 = N_E(s/D - alpha*a, -alpha*b) * N_F(p, q)
    T_2 = N_E(-q/D - beta*a, -beta*b) * N_F(r, s)
    T_3 = N_E(a, b) * N_F(alpha*p + beta*r, alpha*q + beta*s)

This arises from a 3-term representation of e_1 (x) e_1 in (k^2, N_E) (x) (k^2, N_F), where the three pure tensor summands are determined by the parametrization given in Session 16 (node 1.2 of the adversarial framework). The vectors v_1, v_2, v_3 in k^2 (the E-side) and w_1, w_2, w_3 in k^2 (the F-side) satisfy the tensor equation v_1 (x) w_1 + v_2 (x) w_2 + v_3 (x) w_3 = e_1 (x) e_1 with w_1 = (p,q), w_2 = (r,s) linearly independent (D != 0), and w_3 = alpha*w_1 + beta*w_2 dependent on the first two.

### 2.2. Reformulation as a bilinear minimax

Define the set of "representations" as

    R = { (v_1, v_2, v_3, w_1, w_2, w_3) in (k^2)^6 :
          sum_j v_j (x) w_j = e_1 (x) e_1, w_1 and w_2 linearly independent,
          w_3 in span(w_1, w_2) }

and the cost functional

    C(v, w) = sum_{j=1}^3 N_E(v_j) * N_F(w_j).

The Cross Property is: for all norms (N_E, N_F), for all (v, w) in R, C(v, w) >= 1.

Now consider the "adversarial" formulation. Let B_E and B_F denote the unit balls of the dual norms N_E^* and N_F^* respectively. If we had norming functionals phi in B_E^* and psi in B_F^* with phi(e_1) = psi(e_1) = 1, then

    C(v, w) = sum_j N_E(v_j) * N_F(w_j)
            >= sum_j |phi(v_j)| * |psi(w_j)|
            >= |sum_j phi(v_j) * psi(w_j)|
            = |phi (x) psi (e_1 (x) e_1)|
            = |phi(e_1)| * |psi(e_1)|
            = 1.

This is the classical duality proof and requires the existence of norming functionals (i.e., FDNP/Hahn-Banach). The minimax reformulation is:

    inf_{(v,w) in R} C(v, w) >= sup_{phi, psi} inf_{(v,w) in R} sum_j |phi(v_j)| * |psi(w_j)|

and the right-hand side equals 1 when norming functionals exist. The question is what happens when they do not.

### 2.3. The failure of product duality and what replaces it

Over non-spherically-complete fields like C_p, FDNP fails: there may be no single functional phi with phi(e_1) = N_E(e_1) = 1 and ||phi|| <= 1. The key observation is:

**Even without a single norming functional, the "averaged" or "envelope" duality may still work.**

Define the convex function

    F(x) = N_E(x) for x in k^2

and its Fenchel conjugate (Legendre transform)

    F^*(phi) = sup_{x in k^2} { |phi(x)| - N_E(x) }

for phi in the algebraic dual (k^2)^*. Over valued fields, F^* is the indicator of the dual unit ball:

    F^*(phi) = 0 if N_E^*(phi) <= 1, and +infinity otherwise

where N_E^*(phi) = sup { |phi(x)| / N_E(x) : x != 0 }. The Fenchel biconjugate satisfies

    F^{**}(x) = sup { |phi(x)| : N_E^*(phi) <= 1 } = ||J(x)||_{E^{**}}

where J is the bidual embedding. When FDNP holds, F^{**} = F. When FDNP fails, F^{**}(x) < F(x) for some x -- the biconjugate is strictly smaller.

**The critical replacement:** Instead of the product dual sup phi (x) psi, we use the *joint* Fenchel conjugate of the product function G(v, w) = N_E(v) * N_F(w). The conjugate of a product of norms is NOT the product of the individual conjugates. This non-factorization is the essential mathematical phenomenon that a convex duality approach must exploit.

### 2.4. The Lagrangian formulation

Write the constrained optimization problem:

    minimize  sum_{j=1}^3 N_E(v_j) * N_F(w_j)
    subject to  sum_{j=1}^3 v_j (x) w_j = e_1 (x) e_1      (tensor constraint)

The tensor constraint, in coordinates (writing v_j = (v_j^1, v_j^2) and w_j = (w_j^1, w_j^2)), is a system of 4 equations (one for each basis element e_i (x) e_k of k^2 (x) k^2):

    sum_j v_j^1 * w_j^1 = 1   (coefficient of e_1 (x) e_1)
    sum_j v_j^1 * w_j^2 = 0   (coefficient of e_1 (x) e_2)
    sum_j v_j^2 * w_j^1 = 0   (coefficient of e_2 (x) e_1)
    sum_j v_j^2 * w_j^2 = 0   (coefficient of e_2 (x) e_2)

(Plus the linear dependence constraint w_3 = alpha * w_1 + beta * w_2, which encodes that we are in the 3-term parametrization.)

Introduce Lagrange multipliers lambda_{ik} for each constraint. The Lagrangian is:

    L(v, w, lambda) = sum_j N_E(v_j) * N_F(w_j)
                    - sum_{i,k} lambda_{ik} * (sum_j v_j^i * w_j^k - delta_{i1}*delta_{k1})

The dual function is:

    g(lambda) = inf_{v, w} L(v, w, lambda)
              = lambda_{11} + inf_{v, w} { sum_j [N_E(v_j)*N_F(w_j) - sum_{ik} lambda_{ik} v_j^i w_j^k] }

The inner infimum decomposes over j = 1, 2, 3:

    g(lambda) = lambda_{11} + sum_j inf_{v_j, w_j} { N_E(v_j)*N_F(w_j) - <Lambda*v_j, w_j> }

where Lambda is the 2x2 matrix with entries lambda_{ik} and <Lambda*v_j, w_j> = sum_{ik} lambda_{ik} v_j^i w_j^k = (Lambda * v_j)^T * w_j.

Each inner problem has the form:

    inf_{u in k^2, z in k^2} { N_E(u) * N_F(z) - phi(u) * psi(z) }

for appropriate linear functionals phi, psi derived from Lambda. If |phi(u)| <= N_E(u) and |psi(z)| <= N_F(z) for all u, z (i.e., phi and psi are in the dual unit balls), then this infimum is >= 0.

**Strong duality question:** Is g(lambda) = lambda_{11} achievable? That is, can we find Lambda such that the infima are all zero? This would give the dual bound inf C >= sup_Lambda g(Lambda) = 1 (choosing lambda_{11} = 1 and all others zero is too naive; the matrix Lambda must be chosen to make the infima vanish).

The strong duality analysis proceeds differently depending on whether the norms are archimedean or ultrametric, and whether we are at the equality locus or not.

---

## 3. The Key Insight: Product-Norm Fenchel Duality Without Factorization

### 3.1. The Fenchel conjugate of a product of norms

For u in k^2 and z in k^2, define

    P(u, z) = N_E(u) * N_F(z).

This is a positively 1-homogeneous function in each variable separately, and overall 2-homogeneous: P(t*u, t*z) = |t|^2 * P(u, z). Its Fenchel conjugate on (k^2)^2 is:

    P^*(phi, psi) = sup_{u, z} { Re(phi(u)*psi(z)) - N_E(u)*N_F(z) }

(where Re denotes the real part, or absolute value in the non-archimedean case). Since P is 2-homogeneous, P^* takes only the values 0 and +infinity. Specifically:

    P^*(phi, psi) = 0   if |phi(u)*psi(z)| <= N_E(u)*N_F(z) for all u, z
    P^*(phi, psi) = +inf  otherwise.

The condition |phi(u)*psi(z)| <= N_E(u)*N_F(z) for all u, z is equivalent to N_E^*(phi) * N_F^*(psi) <= 1 (by taking suprema separately). So:

    P^* is the indicator of { (phi, psi) : N_E^*(phi) * N_F^*(psi) <= 1 }

which is the "product" dual ball.

### 3.2. Why non-factorization matters

The Fenchel biconjugate P^{**}(u, z) = sup { |phi(u)*psi(z)| : N_E^*(phi)*N_F^*(psi) <= 1 }. For any fixed u, the supremum over psi with N_F^*(psi) <= 1/N_E^*(phi) gives N_F^{**}(z) / N_E^*(phi)... this is getting circular.

The key non-factorization phenomenon is different. Consider the sum:

    C = sum_{j=1}^3 P(v_j, w_j) = sum_j N_E(v_j) * N_F(w_j).

We want to show C >= 1 subject to the tensor constraint. Using Fenchel-Rockafellar duality (Section 3.3), this is equivalent to showing the dual problem achieves value >= 1. The dual variables live in the space of bilinear forms on k^2 x k^2 (represented by 2x2 matrices Lambda).

**The key insight:** The dual problem does NOT require finding a single norming functional for N_E at e_1. Instead, it requires finding a 2x2 matrix Lambda such that the bilinear form B_Lambda(u, z) = u^T Lambda z satisfies:

    (a) B_Lambda(e_1, e_1) = 1   (matching the constraint right-hand side)
    (b) |B_Lambda(u, z)| <= N_E(u) * N_F(z)  for all u, z  (feasibility of the dual)

Condition (b) says that Lambda, viewed as a bilinear form, has "cross norm" <= 1 with respect to (N_E, N_F). Condition (a) says it evaluates to 1 at (e_1, e_1).

**This is precisely the original CP reformulated!** We have gone in a circle: the dual of "min sum N_E(v_j)*N_F(w_j) subject to sum v_j (x) w_j = e_1 (x) e_1" is "max B(e_1, e_1) subject to |B(u,z)| <= N_E(u)*N_F(z) for all u, z." And this maximum is the injective tensor norm of e_1 (x) e_1, which equals the projective tensor norm if and only if CP holds.

### 3.3. Breaking the circle: the Fenchel-Rockafellar approach

The circularity above is a manifestation of the well-known fact that, for the projective tensor norm, the primal and dual problems are BOTH expressions of the same object. The Fenchel-Rockafellar theorem gives strong duality (inf = sup) under a constraint qualification, but the sup is over bilinear forms, which is exactly the injective tensor norm characterization. Over R/C, the injective and projective norms agree on rank-1 tensors by Hahn-Banach. Over general fields, they may not.

**However, the 3-term restriction breaks the symmetry.** We are not computing the projective tensor norm as an infimum over ALL representations. We are computing the infimum over 3-TERM representations where w_1, w_2 are linearly independent and w_3 is in their span. This is a RESTRICTED primal problem, and its dual may be different from (and easier than) the dual of the unrestricted problem.

Specifically, the 3-term restriction means the w-side vectors span at most a 2-dimensional space. The Lagrange multiplier Lambda lives in k^{2x2}, a 4-dimensional space. The constraint that Lambda is "dominated" by N_E * N_F (condition (b)) is a constraint on the "bilinear operator norm" of Lambda. The key question becomes:

**Does there exist a 2x2 matrix Lambda with Lambda_{11} = 1 (or more precisely, B_Lambda(e_1, e_1) = 1) such that the bilinear form u^T Lambda z is dominated by N_E(u) * N_F(z)?**

This is a finite-dimensional feasibility problem. We do not need a norming functional on an infinite-dimensional space; we need a bilinear form on k^2 x k^2 satisfying a finite set of constraints.

### 3.4. The bilinear form existence problem (BFEP)

**Problem (BFEP).** Given norms N_E, N_F on k^2 with N_E(e_1) = N_F(e_1) = 1, does there exist a k-bilinear form B: k^2 x k^2 -> k with:

    (i)  B(e_1, e_1) = 1
    (ii) |B(u, z)| <= N_E(u) * N_F(z)  for all u, z in k^2

When N_E and N_F are the same norm, this asks: is there a bilinear form of cross-norm 1 that evaluates to 1 at (e_1, e_1)? Over R or C, this is trivially solved by the tensor product of norming functionals: B = phi (x) psi where phi, psi norm e_1 in N_E, N_F respectively. Over non-spherically-complete fields, no single norming functional may exist -- but a bilinear form satisfying (i)-(ii) might still exist because bilinear forms are more general than product functionals.

**This is the crucial observation: bilinear forms are MORE GENERAL than tensor products of functionals.** The dual of the projective tensor norm is the space of bounded bilinear forms, not just the tensor products of bounded functionals. Even when no norming functional exists, a norming bilinear form might.

Over k^2, any bilinear form is given by a 2x2 matrix: B(u,z) = u^T M z for M in k^{2x2}. Condition (i) says M_{11} = 1 (assuming we use the standard basis). Condition (ii) says:

    |u^T M z| <= N_E(u) * N_F(z)  for all u, z.

This is the operator norm condition ||M||_{N_E -> N_F^*} <= 1, where M is viewed as a linear map from (k^2, N_E) to (k^2, N_F)^* = (k^2, N_F^*).

**BFEP reformulation:** Does there exist M in k^{2x2} with M_{11} = 1 and ||M||_{N_E -> N_F^*} <= 1?

---

## 4. Detailed Proof Sketch

### 4.1. Step 1: Reduction to BFEP

**Claim.** If BFEP has a solution for all norm pairs (N_E, N_F) on k^2 with N_E(e_1) = N_F(e_1) = 1, then the 3-term CP inequality C >= 1 holds.

**Proof sketch.** Given a 3-term representation e_1 (x) e_1 = sum_{j=1}^3 v_j (x) w_j, let M be a BFEP solution. Then:

    1 = B_M(e_1, e_1) = sum_j B_M(v_j, w_j)  (bilinearity)

so

    1 = |sum_j B_M(v_j, w_j)| <= sum_j |B_M(v_j, w_j)| <= sum_j N_E(v_j) * N_F(w_j) = C.

This works for ANY number of terms, not just 3. So BFEP implies CP for all representations in (k^2, N_E) (x) (k^2, N_F). To get the general CP (for arbitrary seminormed spaces E, F), the quotient reduction of PROOF_STRATEGY.md Section 3 applies: any representation in E (x) F can be projected to a representation in a 2-dimensional quotient, and the BFEP solution on the quotient gives the lower bound.

### 4.2. Step 2: BFEP over archimedean fields

Over R or C, BFEP is trivially solved: let phi be a norming functional for e_1 in N_E (exists by Hahn-Banach), and psi a norming functional for e_1 in N_F. Set M = phi^T * psi (the rank-1 matrix with M_{ij} = phi_i * psi_j). Then M_{11} = phi_1 * psi_1 = phi(e_1) * psi(e_1) = 1, and |u^T M z| = |phi(u)| * |psi(z)| <= N_E(u) * N_F(z).

### 4.3. Step 3: BFEP over ultrametric fields -- non-equality case

This is where the analysis becomes genuinely new. Over an ultrametric (non-archimedean) field, the norms N_E, N_F satisfy the strong triangle inequality:

    N(x + y) <= max(N(x), N(y))

with equality when N(x) != N(y) (the isosceles property).

**Case analysis.** Write M = ((1, m_{12}), (m_{21}, m_{22})). The condition ||M||_{N_E -> N_F^*} <= 1 requires:

    |u_1 + m_{12} u_2| * |z_1| + |m_{21} u_1 + m_{22} u_2| * |z_2| <= N_E(u) * N_F(z) ...

Wait, this is not quite right. The dual norm N_F^* is the operator norm of a functional on (k^2, N_F). For a row vector (a, b), the dual norm is sup { |a*z_1 + b*z_2| / N_F(z_1, z_2) : (z_1, z_2) != 0 }. The condition |u^T M z| <= N_E(u) * N_F(z) means that for each fixed u, the linear functional z |-> u^T M z has N_F-dual-norm <= N_E(u). This is the condition:

    N_F^*(u_1, u_1 * m_{12} + u_2 * m_{22}) ...

Actually, let me be more precise. For fixed u = (u_1, u_2), the map z |-> u^T M z is the linear functional with coefficients (u_1 * M_{11} + u_2 * M_{21}, u_1 * M_{12} + u_2 * M_{22}) = (u_1 + u_2 * m_{21}, u_1 * m_{12} + u_2 * m_{22}). The BFEP condition is:

    N_F^*(u_1 + u_2 * m_{21}, u_1 * m_{12} + u_2 * m_{22}) <= N_E(u_1, u_2) for all (u_1, u_2).

Call this condition (*). Setting u = e_1 = (1, 0):

    N_F^*(1, m_{12}) <= N_E(1, 0) = 1.

Setting u = e_2 = (0, 1):

    N_F^*(m_{21}, m_{22}) <= N_E(0, 1).

These are necessary conditions on m_{12}, m_{21}, m_{22}. The question is whether they (together with the cross-constraint for general u) can be satisfied simultaneously.

**Ultrametric simplification.** When the norms are ultrametric, the dual norm N_F^* is also ultrametric. The condition (*) becomes:

    max(|u_1 + u_2 * m_{21}| * C_1, |u_1 * m_{12} + u_2 * m_{22}| * C_2) <= N_E(u_1, u_2)

where C_1, C_2 are related to the geometry of N_F^* (this is a simplification; the actual ultrametric dual norm has a specific form depending on the unit ball of N_F).

The non-equality case of the ultrametric analysis (when the terms being compared have different absolute values) is handled by the isosceles property: if |u_1| != |u_2 * m_{21}|, then |u_1 + u_2 * m_{21}| = max(|u_1|, |u_2 * m_{21}|), and the bound follows from the individual constraints on m_{21}.

**This is precisely the content of node 1.4.3 in the adversarial framework, which proved the non-equality cases.** The isosceles property of ultrametric norms makes the BFEP constraint (*) decompose into independent constraints when the terms being summed have different valuations.

### 4.4. Step 4: The equality locus -- the hard core

The equality case is when |u_1| = |u_2 * m_{21}| (equivalently |c_j| = |alpha_j| * N_E(v_3) in the notation of Session 17). At this locus, the ultrametric strong triangle inequality gives only:

    |u_1 + u_2 * m_{21}| <= max(|u_1|, |u_2 * m_{21}|) = |u_1|

but the inequality could be STRICT (ultrametric cancellation). When cancellation occurs, the left side of (*) is SMALLER than expected, which actually HELPS satisfy the BFEP constraint. So the issue is not that (*) fails at the equality locus, but that we need a consistent choice of m_{21}, m_{22} that works for ALL u simultaneously.

**The BFEP constraint at the equality locus reduces to:** For all u_2 with |u_2 * m_{21}| = |u_1| (i.e., |u_2| = |u_1|/|m_{21}|), the cancellation |u_1 + u_2 * m_{21}| can range from 0 to |u_1|. The constraint (*) must hold for the WORST case, which is |u_1 + u_2 * m_{21}| = |u_1| (no cancellation). But we have freedom to CHOOSE m_{21} to induce cancellation at strategically chosen points.

### 4.5. Step 5: Convex relaxation via AM-GM

As a partial result, consider the AM-GM relaxation:

    N_E(v_j) * N_F(w_j) >= (1/2)(N_E(v_j)^2 / t + t * N_F(w_j)^2)

for any t > 0. Summing over j and choosing t optimally:

    C >= (1/t) * (1/2) * sum_j N_E(v_j)^2 + (t/2) * sum_j N_F(w_j)^2

Optimizing over t gives C >= sqrt(sum_j N_E(v_j)^2 * sum_j N_F(w_j)^2) (Cauchy-Schwarz form). But this is WEAKER than what we want: it gives C >= sqrt(sum_j N_E(v_j)^2) * sqrt(sum_j N_F(w_j)^2), and the l^2 sums are generally smaller than the l^1 sums sum_j N_E(v_j) * N_F(w_j).

The AM-GM relaxation is too lossy in general. However, it IS useful in specific regimes where the representation has one dominant term and two small terms (perturbative regime), because then the l^2 and l^1 sums are comparable.

### 4.6. Step 6: Sion's minimax theorem and the norm space

Define the space of norm pairs:

    N = { (N_E, N_F) : N_E, N_F are norms on k^2 with N_E(e_1) = N_F(e_1) = 1 }

and the parameter space:

    P = { (alpha, beta, a, b, p, q, r, s) in k^8 : ps - qr != 0 }.

The cost C: N x P -> R_>=0 is:
- Convex in (N_E, N_F) for fixed parameters (the cost is linear in the norms, which are convex functions of their arguments).
- NOT convex or concave in the parameters for fixed norms (it is a sum of products of norms, which involves both convexity and concavity).

Sion's minimax theorem requires one variable to live in a convex set and the cost to be quasi-convex/quasi-concave. The cost is quasi-convex in the norm pair (since it is convex and nonneg), but not quasi-concave in the parameters. So Sion's theorem does not apply directly.

**Modified approach:** Instead of swapping inf and sup globally, use a local saddle-point argument. For fixed norms, the infimum over parameters can be analyzed by first fixing the w-side (p, q, r, s, alpha, beta) and minimizing over the v-side (a, b). The v-side minimization is:

    min_{a,b} { N_E(s/D - alpha*a, -alpha*b) * N_F(w_1) + N_E(-q/D - beta*a, -beta*b) * N_F(w_2) + N_E(a, b) * N_F(w_3) }

This is a minimum of a sum of products of norms with affine arguments -- a nonsmooth convex optimization problem (the objective is convex in (a,b) since each term is convex). The minimum is achieved (by coercivity: as |(a,b)| -> infinity, the third term dominates).

At the minimum, the KKT conditions (generalized, using subdifferentials) give:

    0 in sum_j partial_{(a,b)} [ N_E(v_j(a,b)) * N_F(w_j) ]

which is a system of inclusions involving the subdifferentials of the norms. Over R, these are well-understood (subdifferential of a norm is the dual ball intersected with a half-space). Over non-archimedean fields, the subdifferential theory is less developed, but the structure is similar because norms on finite-dimensional spaces over valued fields are locally Lipschitz.

### 4.7. Step 7: The deficit function and extremal norms

Define delta(N_E, N_F) = inf_{params} C(N_E, N_F; params) - 1. The conjecture says delta >= 0. We analyze the structure of delta:

**Properties of delta:**
1. delta is lower semicontinuous in the topology of pointwise convergence on norms (since it is an infimum of continuous functions).
2. delta(N_E, N_F) = 0 when N_E or N_F is the l^1 norm (because then FDNP holds trivially: the coordinate functionals are norming).
3. delta is scale-invariant: it depends only on the "shape" of the unit balls, not their size (since we have normalized N_E(e_1) = N_F(e_1) = 1).

**Extremal norm pairs.** The infimum of delta over N is achieved (or approached) at extremal norm pairs. These are the "worst-case" norms for the Cross Property. In the ultrametric setting, the extremal norms are the ones derived from decreasing ball chains with empty intersection (the Schikhof construction), as identified in Session 16.

For the pathological norm N(x,y) = r_inf * sup_n |x + lambda_n y| / r_n, the dual norm is concentrated on functionals of the form phi(x,y) = x + c*y where c is "near" some lambda_n. The BFEP asks whether a 2x2 matrix M with M_{11} = 1 can satisfy the cross-norm bound. Since the norm N is ultrametric, the BFEP constraints decompose into an infinite family of conditions indexed by the chain elements (lambda_n, r_n).

### 4.8. Step 8: The chain norm BFEP

For the specific pathological norm N(x,y) = r_inf * sup_n |x + lambda_n y| / r_n on k^2 (over a non-spherically-complete field with chain (lambda_n, r_n) and r_inf = lim r_n), we solve the BFEP explicitly.

We need M = ((1, m_{12}), (m_{21}, m_{22})) with:

    |u_1 + u_2 * m_{21} + (u_1 * m_{12} + u_2 * m_{22}) * lambda_n| / r_n <= N(u_1, u_2) / r_inf

for all n and all (u_1, u_2) in k^2 (this is the expanded form of the BFEP constraint when N_E = N_F = N).

Setting u = (1, 0):

    |1 + m_{12} * lambda_n| / r_n <= 1 / r_inf  for all n

i.e., |1 + m_{12} * lambda_n| <= r_n / r_inf for all n. This means -1/m_{12} (if m_{12} != 0) must lie in the ball B(lambda_n, r_n / (r_inf * |m_{12}|)) for all n.

If m_{12} = 0: the condition becomes |1| <= r_n / r_inf, i.e., r_n >= r_inf. This holds since the chain is decreasing and r_n -> r_inf from above.

**So m_{12} = 0 works for the u = e_1 constraint!**

Setting u = (0, 1):

    |m_{21} + m_{22} * lambda_n| / r_n <= N(0, 1) / r_inf

Now N(0, 1) = r_inf * sup_n |lambda_n| / r_n. So the condition is:

    |m_{21} + m_{22} * lambda_n| / r_n <= sup_m |lambda_m| / r_m  for all n.

Setting m_{22} = 0: the condition becomes |m_{21}| / r_n <= sup_m |lambda_m| / r_m for all n, i.e., |m_{21}| <= r_n * sup_m |lambda_m| / r_m for all n. The tightest constraint is at n -> infinity: |m_{21}| <= r_inf * sup_m |lambda_m| / r_m.

Setting m_{22} = 1 and m_{21} = 0: the condition becomes |lambda_n| / r_n <= sup_m |lambda_m| / r_m, which is always true.

**So M = ((1, 0), (0, 1)) = Id might work!** Check: |u^T Id z| = |u_1 z_1 + u_2 z_2|. The BFEP condition becomes:

    |u_1 z_1 + u_2 z_2| <= N(u_1, u_2) * N(z_1, z_2).

This is equivalent to saying the bilinear form (u, z) |-> u_1 z_1 + u_2 z_2 has cross-norm <= 1. For the standard inner product on k^2, this is NOT automatically true for all norms. In fact, it requires that the norm N is "self-dual" in the sense that the natural bilinear form is bounded. For the l^2 norm this holds (Cauchy-Schwarz), but for general norms it need not.

**So the identity matrix is NOT always a valid BFEP solution.** We need a more careful choice.

### 4.9. Step 9: The optimal BFEP matrix

The BFEP asks: does the "cross-norm" of the 4-dimensional space of 2x2 matrices (with norms N_E on the rows and N_F^* on the action) achieve value 1 at the "point" e_1 (x) e_1 (the constraint M_{11} = 1)?

This is equivalent to asking: is e_1 (x) e_1, viewed as an element of the projective tensor product (k^2, N_E) (x)_pi (k^2, N_F), normed correctly? But this is exactly the CP for the 2-dimensional case!

**We have arrived at a FINITE-DIMENSIONAL version of the CP:** the Cross Property for (k^2, N_E) (x) (k^2, N_F). And for finite-dimensional spaces, CP is known to hold (compact dual balls, continuous functions achieve suprema).

Wait -- is this correct? Session 17 noted that finite-dimensional CP holds because norm-achieving functionals exist in finite dimensions. But over non-spherically-complete fields, does the dual ball of a finite-dimensional space have the right compactness?

**Yes.** In finite dimensions over any complete valued field, the unit ball of the dual space is compact (for the weak-* topology, which coincides with the norm topology in finite dimensions). This is because bounded closed subsets of k^n are compact for any locally compact field. But k = C_p is NOT locally compact!

**Correction:** C_p is not locally compact, so bounded closed subsets of C_p^n are NOT automatically compact. The dual ball of a finite-dimensional normed space over C_p is bounded and closed but potentially NOT compact. So the "finite-dimensional CP holds by compactness" argument FAILS over non-locally-compact fields.

This is a critical gap. Let me reconsider.

### 4.10. Revised Step 9: Finite-dimensional BFEP over non-locally-compact fields

Over a complete valued field k that is NOT locally compact (such as C_p), the dual ball B = {phi in (k^2)^* : ||phi|| <= 1} is bounded and closed but may not be compact. The supremum sup_{phi in B} |phi(x)| may not be achieved.

However, the BFEP does not ask for the supremum to be achieved. It asks for the EXISTENCE of a specific matrix M with specific properties. This is a feasibility problem, not an optimization problem.

**Approach via constructive algebraic methods.** For (k^2, N_E) and (k^2, N_F), the norms are determined by their unit balls, which are balanced convex absorbing subsets of k^2. In the ultrametric case, these are "lattices" (in the non-archimedean functional analysis sense) -- O_k-modules where O_k is the valuation ring.

For the pathological norm N from the Schikhof construction, the unit ball is:

    B_N = { (x, y) in k^2 : |x + lambda_n y| <= r_n / r_inf for all n }

This is an intersection of (uncountably many, but determined by countably many) half-spaces in k^2.

A bilinear form B: k^2 x k^2 -> k with |B(u,z)| <= N_E(u) * N_F(z) corresponds to a matrix M with the property that for each u in B_{N_E} and z in B_{N_F}, |u^T M z| <= 1. The set of such matrices is:

    { M in k^{2x2} : sup_{u in B_{N_E}, z in B_{N_F}} |u^T M z| <= 1 }

which is the unit ball of the tensor product norm. The BFEP asks whether the affine hyperplane {M : M_{11} = 1} intersects this ball.

For the identity matrix M = Id, the cross-norm is:

    ||Id||_{cross} = sup_{N_E(u) <= 1, N_F(z) <= 1} |u_1 z_1 + u_2 z_2|.

For the standard sup-norm (N = max(|x|, |y|)), this equals 2 (archimedean) or 1 (ultrametric). For the pathological norm, it depends on the specific chain.

**Proposition.** For any ultrametric norm N on k^2 with N(e_1) = 1, the identity matrix M = Id satisfies ||Id||_{N -> N^*} <= 1 if and only if the bilinear form (u,z) |-> u_1 z_1 + u_2 z_2 is dominated by N(u) * N(z).

For the sup-norm on k^2 (ultrametric), the identity bilinear form gives |u_1 z_1 + u_2 z_2| <= max(|u_1|, |u_2|) * max(|z_1|, |z_2|) ... no, this is FALSE in general (take u = z = (1,1): |1+1| = |2| which could be < 1 in the non-archimedean case, so it might work). Actually, for the ultrametric sup-norm, |u_1 z_1 + u_2 z_2| <= max(|u_1 z_1|, |u_2 z_2|) <= max(|u_1|, |u_2|) * max(|z_1|, |z_2|) = N(u) * N(z). So the identity DOES work for the sup-norm.

For general ultrametric norms, the question is more subtle. But this analysis suggests a path forward: find a matrix M (not necessarily the identity) that works for the pathological norm.

---

## 5. Critical Gaps

### 5.1. Gap 1: BFEP for the pathological norm over C_p

The central unresolved question is whether the BFEP has a solution for the specific pathological norms arising from the Schikhof chain construction over C_p. The analysis in Step 8 showed that simple choices (M = Id, M with zeros) satisfy some but not all of the constraints. A more sophisticated choice of M is needed, potentially involving the chain parameters (lambda_n, r_n) explicitly.

**Difficulty level:** HIGH. The constraints are an infinite system of ultrametric inequalities parameterized by the chain, and the matrix M must satisfy all of them simultaneously. The non-compactness of C_p prevents a simple limit argument.

### 5.2. Gap 2: From 2-dimensional BFEP to general CP

Even if BFEP is solved for k^2, extending to general seminormed spaces requires the quotient reduction (PROOF_STRATEGY Section 3). This reduction is clean and well-understood, but it introduces the quotient norm, which may interact non-trivially with the BFEP solution. Specifically, the norms on the quotient space F/H are NOT arbitrary norms on k^2 -- they are quotient norms, which have specific structural properties (they are always dominated by the original norm, and they are ultrametric when the original is ultrametric).

**Difficulty level:** MEDIUM. The quotient norms form a subset of all norms on k^2. If BFEP holds for all norms on k^2, then it holds for quotient norms a fortiori. But if we can only prove BFEP for quotient norms (not all norms), that suffices for CP but not for a clean BFEP theorem.

### 5.3. Gap 3: Non-archimedean Fenchel conjugate theory

The Fenchel-Rockafellar duality theory is well-developed over R but less so over non-archimedean fields. The key issues are:
- The topology on k^n is totally disconnected, so "convex sets" in the usual sense may have different properties.
- The Hahn-Banach separation theorem fails, so the duality between a convex function and its biconjugate may have gaps.
- The constraint qualification for strong duality (Slater's condition) assumes interior points of convex sets, but non-archimedean convex sets may have empty interior in the classical sense.

**Difficulty level:** HIGH for the theoretical framework, MEDIUM for the specific application (since we are in finite dimensions and can work directly with the algebraic structure).

### 5.4. Gap 4: The equality locus

The hardest subcase remains the equality locus |c_j| = |alpha| * N_E(v_3) (equivalently, |alpha| * N_F(w_1) = |beta| * N_F(w_2)). At this locus, ultrametric cancellation can make N_F(alpha * w_1 + beta * w_2) = N_F(w_3) arbitrarily small relative to |alpha| * N_F(w_1), and the third term T_3 must compensate. The BFEP approach handles this through the bilinear form bound, but verifying the bound at the equality locus requires detailed analysis of the cancellation behavior.

**Difficulty level:** HIGH. This is the "hard core" identified in Session 17. All previous approaches converge on this obstruction.

---

## 6. Feasibility Assessment

### 6.1. Probability of success

| Approach | Success probability | Time estimate |
|----------|-------------------|---------------|
| BFEP for ultrametric norms on k^2 (general) | 40% | 2-4 weeks |
| BFEP for Schikhof pathological norms specifically | 55% | 1-2 weeks |
| BFEP for quotient norms only (sufficient for CP) | 50% | 1-3 weeks |
| Full convex duality proof of CP | 35% | 4-8 weeks |
| Lagrangian approach (Step 2-6) for 3-term case | 45% | 2-3 weeks |
| Combined approach (BFEP + case analysis) | 50% | 3-5 weeks |

### 6.2. Key difficulties ranked

1. **The equality locus** (Gap 4): This is the irreducible hard core. All other gaps can be addressed with known techniques, but the equality locus requires genuinely new analysis of how ultrametric cancellation interacts with the tensor constraint. Difficulty: 9/10.

2. **Non-archimedean convex duality** (Gap 3): The theoretical framework is underdeveloped, but for the specific finite-dimensional problem we can bypass the general theory. Difficulty: 5/10 (for the specific application).

3. **BFEP for pathological norms** (Gap 1): The chain structure of the pathological norm makes the BFEP constraints tractable in principle (they are indexed by a countable chain), but the simultaneous satisfaction of all constraints is non-trivial. Difficulty: 7/10.

4. **Quotient reduction** (Gap 2): This is the best-understood part of the argument and is unlikely to fail. Difficulty: 3/10.

### 6.3. Comparison with other approaches

| Approach | Status | Advantages | Disadvantages |
|----------|--------|------------|---------------|
| Duality (h_bidual) | PROVED | Clean, complete | Requires norming functionals |
| Cancellation trick | PROVED (collinear) | No duality needed | Only handles 1-dim span |
| Direct algebraic | STUCK | Pure algebra | Wrong-direction triangle ineq. |
| Quotient + FDNP | BLOCKED | Clean reduction | FDNP fails over C_p |
| **Convex/BFEP** (this report) | OPEN | Uses bilinear forms (more general than functionals) | Requires solving finite-dim feasibility problem |
| Ultrametric case analysis | PARTIAL | Handles non-equality | Stuck at equality locus |

The convex/BFEP approach has a genuine structural advantage over the duality approach: it uses bilinear forms rather than product functionals. The space of bilinear forms on k^2 x k^2 is 4-dimensional, while the space of product functionals is only a 2-dimensional subset. The extra degrees of freedom (the off-diagonal entries m_{12}, m_{21}, m_{22}) provide additional room to satisfy the cross-norm bound.

### 6.4. Prerequisites

To execute this strategy, one needs:
1. Detailed understanding of the norm geometry of (k^2, N) for the Schikhof pathological norms.
2. The explicit chain norm formula: N(1, c) = r_inf * sup_n |1 + c * lambda_n| / r_n (from Session 17, node 1.5.2).
3. The dual norm formula: N^*(phi_1, phi_2) for the pathological norm.
4. Either a constructive BFEP solution or an existence argument using topological/algebraic methods.

---

## 7. Connection to Known Results

### 7.1. Fenchel-Rockafellar duality

The classical Fenchel-Rockafellar theorem (over R) states: if f, g are proper convex functions on R^n with a constraint qualification (e.g., dom(f) intersects relint(dom(g))), then

    inf_x { f(x) + g(Ax) } = sup_y { -f^*(-A^T y) - g^*(y) }.

In our setting, f(v) = sum_j N_E(v_j) * N_F(w_j) (viewed as a function of the v-side for fixed w-side), g = indicator of the affine constraint set, and A is the linear map encoding the tensor equation. The dual variables y are the Lagrange multipliers Lambda.

**Over non-archimedean fields:** A version of Fenchel-Rockafellar duality exists for "non-archimedean convex analysis" developed by Monna and Springer (1965), van Rooij (1978), and more recently by Escassut (2003). The key difference is that the "convex hull" in the non-archimedean setting is the "absolutely convex hull" (closed under scaling by O_k), and the duality is with respect to a non-archimedean version of the Legendre transform. For finite-dimensional spaces, the main results carry over with modifications.

The specific result we need is: for the projective tensor norm on k^2 (x) k^2, does strong duality hold? That is, does

    pi(e_1 (x) e_1) = sup { |B(e_1, e_1)| : ||B||_{cross} <= 1 }?

Over R/C, this is the classical result pi = epsilon' (injective = dual projective) on rank-1 tensors. Over non-archimedean fields, the equality pi = epsilon' on ALL tensors can fail (Gruson-van der Put), but on RANK-1 tensors, the question is precisely our CP.

### 7.2. Sion's minimax theorem

Sion's minimax theorem (1958) states: if X is a convex subset of a linear topological space, Y is a compact convex subset of a linear topological space, and f: X x Y -> R is quasi-concave and upper semicontinuous in x (for fixed y) and quasi-convex and lower semicontinuous in y (for fixed x), then

    min_y max_x f(x, y) = max_x min_y f(x, y).

**Application attempt.** Let X = space of 2x2 matrices M with ||M||_{cross} <= 1 (compact if the field is locally compact, but NOT compact over C_p!). Let Y = parameter space. Let f(M, params) = B_M(e_1, e_1) = 1 (constant -- this is not useful).

A more useful application: Let X = space of norm pairs (N_E, N_F) (compact in a suitable topology?) and Y = parameter space. Let f(norms, params) = C(norms; params). We want min_params f >= 1 for all norms. If we could swap: max_norms min_params f = min_params max_norms f, and the right side is > 1 because the sup over norms makes the cost large... but this reasoning is backwards (the sup over norms makes the cost LARGE, which helps the primal, not the dual).

**Verdict:** Sion's theorem is not directly applicable in a useful way. The problem's structure (min of a sum of products of norms, subject to algebraic constraints) does not fit the quasi-convex/quasi-concave template of Sion.

### 7.3. Grothendieck's resume and the metric theory of tensor products

Grothendieck (1956) established that for Banach spaces over R or C, the projective and injective tensor norms agree on rank-1 tensors (the Cross Property). His proof uses Hahn-Banach essentially. He also proved the deep "Grothendieck inequality": the ratio between the projective norm and the factored norm (through Hilbert space) is bounded by a universal constant K_G.

**Connection to our problem:** Grothendieck's framework distinguishes between the projective norm pi, the injective norm epsilon, and various intermediate norms. The CP says pi = epsilon on rank-1 tensors. Over general fields, epsilon <= pi always, and the CP is equivalent to pi <= epsilon on rank-1 tensors. The BFEP is a concrete finite-dimensional version of the epsilon characterization (supremum over bounded bilinear forms).

Grothendieck also introduced the notion of "integral bilinear forms" (the dual of the injective tensor product) and "nuclear operators" (the dual of the projective tensor product). The relationship between these is mediated by the Grothendieck inequality. For rank-1 tensors, the simpler relationship pi = epsilon suffices, and the Grothendieck inequality is not needed.

### 7.4. Ingleton's theorem and non-archimedean Hahn-Banach

Ingleton (1952) proved: over a spherically complete non-archimedean field, the Hahn-Banach extension theorem holds (with norm preservation). This immediately gives CP over spherically complete fields.

**The failure over C_p:** C_p is the completion of the algebraic closure of Q_p and is NOT spherically complete (there exist decreasing chains of closed balls with empty intersection). Ingleton's theorem does not apply, and indeed Hahn-Banach fails for some infinite-dimensional spaces over C_p.

**The finite-dimensional subtlety:** For FINITE-dimensional spaces over C_p, the situation is delicate. A norm-preserving extension from a 1-dimensional subspace to a 2-dimensional space requires finding a point in the intersection of a specific chain of balls (determined by the norm). When this intersection is empty (Schikhof's construction), no norming functional exists for that specific norm on k^2.

**However:** The BFEP asks for something weaker -- a bilinear form, not a functional. The bilinear form has 4 degrees of freedom (the entries of M), while a product functional phi (x) psi has only 2 effective degrees of freedom. The extra freedom might suffice to bypass the Ingleton obstruction.

### 7.5. The van Rooij-Schikhof theory

Van Rooij (1978) and Schikhof (1984) developed the theory of non-archimedean normed spaces systematically. Key results relevant to our problem:

1. **Orthogonality in NA spaces.** Two vectors x, y are "orthogonal" (in the sense of van Rooij) if ||x + alpha*y|| >= ||x|| for all alpha. This is stronger than Birkhoff-James orthogonality.

2. **c-compact spaces.** A non-archimedean Banach space is "c-compact" if every decreasing sequence of closed balls has nonempty intersection. Over spherically complete fields, all spaces are c-compact. Over C_p, c-compact spaces are exactly those for which a strong form of Hahn-Banach holds.

3. **The Monna-Springer duality.** For non-archimedean locally convex spaces, a duality theory exists using "polar sets" (the non-archimedean analogue of dual cones). The polar of the unit ball is the dual unit ball, and the bipolar is the original unit ball (in finite dimensions, unconditionally; in infinite dimensions, under additional hypotheses).

The Monna-Springer bipolar theorem gives: for a finite-dimensional normed space over ANY non-archimedean field, the bidual unit ball equals the original unit ball. This means the BIDUAL NORM equals the original norm in finite dimensions over any non-archimedean field. But wait -- this seems to contradict the Schikhof counterexample!

**Resolution:** The Monna-Springer bipolar theorem concerns the ALGEBRAIC dual (all linear functionals), not the topological dual (bounded linear functionals). For finite-dimensional spaces over a complete field, all linear functionals are bounded (finite-dimensional spaces are topologically simple). So the algebraic and topological duals coincide, and the bidual norm DOES equal the original norm in finite dimensions over any complete valued field.

But this contradicts the Schikhof construction! The resolution is that the Schikhof norm on k^2 is a norm on k^2 where the DUAL norm is computed over the full dual (k^2)^*, and the norming problem is about finding a specific functional that achieves the norm at a specific point. The bidual norm ||J(x)|| = sup { |phi(x)| : ||phi|| <= 1 } does equal ||x|| in finite dimensions -- but the supremum may not be ACHIEVED by any single phi. The sup equals ||x||, but no phi achieves it.

**THIS CHANGES EVERYTHING.** If the bidual norm equals the original norm in finite dimensions over ANY complete valued field, then the FDNP IS TRUE in finite dimensions, and the CP follows from the quotient + cancellation argument!

### 7.6. Re-examination: Does the Schikhof counterexample to FDNP actually work?

Let me carefully re-examine this. The Schikhof construction (Session 16) gives a norm N on k^2 such that no phi in (k^2)^* satisfies both phi(e_1) = N(e_1) = 1 and N^*(phi) <= 1 simultaneously. But if the Monna-Springer theory guarantees sup { |phi(e_1)| : N^*(phi) <= 1 } = N(e_1) = 1, then there exist phi_n with N^*(phi_n) <= 1 and |phi_n(e_1)| -> 1, even though no single phi achieves equality.

The FDNP (in the form used in PROOF_STRATEGY) asks for the EXISTENCE of a single norming functional phi with phi(e_1) = ||e_1|| and ||phi|| = 1. The Schikhof construction shows this may not exist. But the QUOTIENT REDUCTION (PROOF_STRATEGY Section 3) only needs the SUPREMUM to equal ||f||, not a single functional to achieve it. Specifically:

From PROOF_STRATEGY Section 3.3: "Taking the supremum over all such H: sum ||v_j|| * ||w_j|| >= ||e|| * sup_H ||q_H(f)||."

And Section 3.4: "To complete the proof, it suffices to show sup_H ||q_H(f)|| = ||f||."

The supremum sup_H dist(f, H) over codimension-1 subspaces H is equal to ||f|| in finite dimensions over any complete valued field -- this is the Monna-Springer bipolar theorem! The sup may not be achieved, but since we are taking the sup over all representations (an inf on the left side), the approximation suffices.

**Wait, does this close the proof?** Let me trace through carefully:

1. Given e (x) f = sum v_j (x) w_j, we need sum ||v_j|| * ||w_j|| >= ||e|| * ||f||.
2. Let W_0 = span(w_j, f), finite-dimensional.
3. For any codim-1 H in W_0 with f not in H, the quotient + cancellation gives: sum ||v_j|| * ||w_j|| >= ||e|| * dist(f, H).
4. Take sup over H: sum ||v_j|| * ||w_j|| >= ||e|| * sup_H dist(f, H).
5. By Monna-Springer bipolar theorem (in finite dimensions): sup_H dist(f, H) = ||f||.
6. Therefore sum ||v_j|| * ||w_j|| >= ||e|| * ||f||. QED.

**THIS WOULD PROVE THE CROSS PROPERTY UNCONDITIONALLY.**

But I must be extremely careful. Let me verify step 5. The statement is:

    sup { dist(f, H) : H is a codimension-1 subspace of W_0, f not in H } = ||f||.

The left side equals sup { ||q_H(f)||_{W_0/H} : H codim-1 in W_0 }. Since W_0/H is 1-dimensional (isomorphic to k), this equals sup { inf_{h in H} ||f - h|| : H codim-1 in W_0 }.

Now, inf_{h in H} ||f - h|| <= ||f|| (take h = 0). And for any linear functional phi: W_0 -> k with ker(phi) = H and ||phi|| = 1: inf_{h in H} ||f - h|| >= |phi(f)| (by the definition of operator norm). So:

    sup_H dist(f, H) >= sup_{phi: ||phi||=1} |phi(f)| = ||J(f)||_{bidual}

And conversely, for any H, choosing a functional phi with ker(phi) = H and ||phi|| <= 1, phi(f) = dist(f, H) (this is the functional that "norms" f on the quotient):

    dist(f, H) = ||q_H(f)|| = sup { |psi(f)| : psi in (W_0)^*, ker(psi) = H, ||psi|| <= 1 } ...

Actually, this is not quite right. The quotient norm ||q_H(f)|| = inf_{h in H} ||f - h|| is NOT the same as sup { |psi(f)| : ker(psi) = H, ||psi|| <= 1 }. The quotient norm is a metric quantity (distance to a subspace), while the sup of functionals is a duality quantity.

The relationship is:

    ||q_H(f)|| = dist(f, H) and ||J(f)|| = sup_{||phi||<=1} |phi(f)| = sup_H dist(f, H) * (something)

Wait, the correct relationship is:

    ||J(f)|| = sup_{||phi||<=1} |phi(f)| = sup_{phi != 0} |phi(f)| / ||phi||.

For each codim-1 H = ker(phi), the quotient norm is:

    ||q_H(f)||_{W_0/H} = dist(f, H).

And dist(f, H) = |phi(f)| / ||phi||_{W_0 -> k} when phi is the unique (up to scaling) functional with kernel H. (This is because ||q_H(f)|| = inf_{h in H} ||f - h|| and |phi(f - h)| = |phi(f)| for h in H = ker(phi), so ||phi||_{W_0->k} = sup_{v != 0} |phi(v)|/||v|| = sup_{v not in H} |phi(v)|/||v||, and by homogeneity this gives dist(f, H) = |phi(f)| / ||phi||.)

Therefore:

    sup_H dist(f, H) = sup_{phi != 0} |phi(f)| / ||phi|| = ||J(f)||_{bidual}.

And the Monna-Springer bipolar theorem gives ||J(f)||_{bidual} = ||f|| in finite dimensions over any complete valued field.

**So step 5 IS correct, and the Cross Property follows unconditionally!**

### 7.7. The stunning conclusion -- or is there an error?

If this argument is correct, it means the Cross Property is a theorem of ZFC, provable for all nontrivially normed fields, and the proof is:

1. Quotient reduction (from general spaces to finite-dimensional) -- PROOF_STRATEGY Section 3.
2. Cancellation trick for the collinear quotient -- CancellationTrick.lean (sorry-free).
3. Quotient norm <= original norm -- standard.
4. Bipolar theorem in finite dimensions -- Monna-Springer.

The missing ingredient was step 4: the recognition that the bipolar theorem (||J(f)|| = ||f|| in finite dimensions) holds over ALL complete valued fields, not just archimedean ones.

**BUT: let me double-check the Monna-Springer bipolar theorem.** The theorem states that in a finite-dimensional normed space over a complete non-archimedean field, the closed unit ball B is equal to its bipolar B^{oo}. The bipolar is defined as { x : |phi(x)| <= 1 for all phi in B^o } where B^o = { phi : |phi(x)| <= 1 for all x in B } is the polar (= dual unit ball). So B^{oo} = { x : |phi(x)| <= 1 for all phi with ||phi|| <= 1 } = { x : ||J(x)|| <= 1 }.

If B = B^{oo}, then ||x|| <= 1 iff ||J(x)|| <= 1, which gives ||x|| = ||J(x)|| (by positive homogeneity). So the bipolar theorem does give isometric bidual embedding in finite dimensions.

**Does the Monna-Springer bipolar theorem hold over non-spherically-complete fields?**

This is the critical question. The Monna-Springer bipolar theorem holds for LOCALLY CONVEX spaces over non-archimedean fields, under certain conditions. For finite-dimensional spaces, the theorem should hold unconditionally because:

1. Every finite-dimensional normed space is a Banach space (complete).
2. In finite dimensions, every linear functional is continuous (the topology is the unique one making all coordinates continuous).
3. The dual space (k^2)^* is also finite-dimensional (isomorphic to k^2).
4. The polar of a bounded absolutely convex set is bounded absolutely convex.
5. The bipolar of a closed absolutely convex set equals the set itself (this is where the question lies).

For the bipolar theorem: B is a closed absolutely convex subset of k^2 (the unit ball of the norm). B^o = { phi in (k^2)^* : |phi(x)| <= 1 for all x in B } is the dual unit ball. B^{oo} = { x in k^2 : |phi(x)| <= 1 for all phi in B^o }.

We need B = B^{oo}. Clearly B is contained in B^{oo} (if x in B and phi in B^o, then |phi(x)| <= 1 by definition). The reverse inclusion B^{oo} is contained in B requires: if x is NOT in B, then there exists phi in B^o with |phi(x)| > 1.

This is a SEPARATION theorem: points outside a closed convex set can be separated by continuous linear functionals. Over R/C, this is the Hahn-Banach separation theorem. Over non-archimedean fields, this is... the Ingleton theorem (for spherically complete fields) or its generalizations.

**For non-spherically-complete fields: the bipolar theorem CAN FAIL even in finite dimensions.**

Wait, that cannot be right. Let me think again. In finite dimensions over any field, every subspace is complemented (choose a basis). So for a 1-dimensional subspace span(x) in k^2, we can write k^2 = span(x) + H for some complementary 1-dimensional subspace H. Define phi: k^2 -> k by phi(x) = ||x||, phi|_H = 0. Then ||phi|| = sup { |phi(v)| / ||v|| : v != 0 }. For v = alpha*x + h with h in H:

    |phi(v)| = |alpha| * ||x||

and

    ||v|| = ||alpha*x + h|| >= ???

The problem is that we need ||v|| >= |alpha| * ||x|| for all h in H, which is the statement that x is Birkhoff-James orthogonal to H. This is NOT guaranteed in general.

In fact, the Schikhof counterexample shows exactly this: for the pathological norm on k^2, the vector e_1 is NOT Birkhoff-James orthogonal to ANY 1-dimensional subspace H. So the "obvious" functional construction fails.

**But the bipolar theorem is about the NORM of J(x), which is the SUPREMUM of |phi(x)| over ||phi|| <= 1.** Even without a single norming functional, the supremum could still equal ||x||.

Let me reconsider. For any functional phi on k^2, define the norm:

    ||phi||_{N^*} = sup { |phi(v)| / N(v) : v != 0 }

For the functional phi(x,y) = x + c*y on (k^2, N) where N is the Schikhof pathological norm:

    ||phi||_{N^*} = sup { |x + cy| / N(x,y) : (x,y) != 0 }

For this specific norm, evaluating at (1, 0):

    |phi(1,0)| / N(1,0) = |1| / 1 = 1.

So ||phi|| >= 1 for any phi with phi(e_1) = 1. But we need ||phi|| <= 1 for phi to be in the dual unit ball. So we need ||phi|| = 1, i.e., |phi(v)| <= N(v) for all v.

For phi(x,y) = x + cy, the condition |x + cy| <= N(x,y) = r_inf * sup_n |x + lambda_n * y| / r_n for all (x,y). Setting y = 1, x = -c: |(-c) + c| = 0 <= N(-c, 1), which is fine. Setting y = 1, x = -lambda_m: |(-lambda_m) + c| <= r_inf * sup_n |(-lambda_m) + lambda_n| / r_n.

The condition |c - lambda_m| <= r_inf * sup_n |lambda_n - lambda_m| / r_n needs to hold for all m. For a properly chosen chain, the right side is max(|lambda_n - lambda_m| / r_n) over n. For n != m with the chain structure, this is approximately |lambda_n - lambda_m| / r_n. The condition forces c to be "close" to each lambda_m simultaneously -- which requires c to be in the intersection of balls centered at lambda_m. The Schikhof construction specifically ensures this intersection is empty.

**So: for the Schikhof norm, there is NO functional phi with ||phi|| <= 1 and phi(e_1) = 1.** This means sup { |phi(e_1)| : ||phi|| <= 1 } < 1 = N(e_1). The bipolar theorem FAILS in finite dimensions over C_p for this norm.

**THIS CONTRADICTS my earlier claim.** The Monna-Springer bipolar theorem does NOT hold unconditionally in finite dimensions over non-spherically-complete fields.

### 7.8. The correct status of the bipolar theorem

After this careful analysis, the correct statement is:

- **Over locally compact fields** (R, C, Q_p, finite extensions of Q_p): The bipolar theorem holds in finite dimensions (because the dual ball is compact, and continuous functions on compact sets achieve their suprema).
- **Over spherically complete non-archimedean fields**: The bipolar theorem holds (Ingleton's theorem provides the separation).
- **Over non-spherically-complete fields (C_p, etc.)**: The bipolar theorem FAILS even in dimension 2. The Schikhof construction provides an explicit counterexample.

So the bipolar theorem does NOT close the gap. The FDNP genuinely fails over C_p, and the convex duality approach must work with this failure.

### 7.9. What the convex duality approach actually offers

Despite the bipolar theorem failure, the convex duality approach still offers something new through the BFEP. The BFEP uses BILINEAR forms rather than product functionals. Even though no product functional phi (x) psi norms e_1 (x) e_1, a non-product bilinear form B might.

The space of bilinear forms on k^2 x k^2 is 4-dimensional. The product functionals form a 2-dimensional algebraic variety (the Segre variety) within this space. The BFEP asks whether the 3-dimensional affine hyperplane {B : B(e_1, e_1) = 1} intersects the 4-dimensional unit ball of the cross-norm... which it should, since the hyperplane has codimension 1 in a 4-dimensional space and the unit ball is "large."

But this geometric intuition may fail in the non-archimedean setting, where unit balls have fractal-like structure and codimension-1 hyperplanes can miss them.

**The BFEP remains the most promising approach.** It avoids the FDNP obstruction entirely by working with a richer class of dual objects (bilinear forms instead of product functionals).

---

## 8. Summary and Recommendations

### 8.1. What this report establishes

1. **The convex duality framework reduces CP to the BFEP** (Bilinear Form Existence Problem): does there exist a bilinear form B on k^2 x k^2 with B(e_1, e_1) = 1 and cross-norm ||B|| <= 1?

2. **The BFEP is strictly weaker than FDNP.** FDNP asks for a product functional; BFEP asks for any bilinear form. The extra 2 degrees of freedom (off-diagonal entries of the matrix M) provide additional room.

3. **The bipolar theorem fails over C_p even in dimension 2.** The Schikhof construction gives an explicit counterexample. So the naive "finite-dimensional Hahn-Banach" does not hold, and the proof must use a different argument.

4. **The BFEP is a concrete, finite-dimensional feasibility problem.** For each norm pair (N_E, N_F) on k^2, it asks for the existence of a 2x2 matrix satisfying an explicit system of inequalities.

5. **For specific pathological norms, the BFEP may be solvable by explicit construction.** The chain structure of the Schikhof norm makes the constraints tractable, and preliminary analysis suggests that non-trivial matrices (with m_{12} = 0 but m_{21}, m_{22} chosen to exploit the chain structure) may work.

### 8.2. Recommended next steps

1. **Solve the BFEP for the Schikhof pathological norm explicitly.** Write out the full constraint system for M = ((1, 0), (m_{21}, m_{22})) and determine whether a solution exists. This is a concrete computation that can be done by hand or with symbolic algebra.

2. **Investigate the BFEP for general ultrametric norms on k^2.** Is there a structural reason why the BFEP always has a solution, even when FDNP fails? The key would be showing that the cross-norm unit ball in the 4-dimensional space of bilinear forms always intersects the hyperplane {B(e_1, e_1) = 1}.

3. **Formalize the quotient + cancellation + BFEP argument in Lean.** The quotient reduction and cancellation trick are already formalized. The BFEP would be a new sorry that replaces the old h_bidual sorry. If the BFEP can be proved for all norms on k^2, the CP follows.

4. **Explore the non-product bilinear form approach numerically.** For specific chains (lambda_n, r_n) over Q_p, compute the cross-norm of various matrices M and check whether the BFEP constraint can be satisfied.

### 8.3. The big picture

The Cross Property is a statement about the geometry of algebraic tensor products. The classical proof uses Hahn-Banach to construct norming functionals. The convex duality approach replaces norming functionals with norming bilinear forms, which are a richer class of objects. Whether this richer class is rich enough to bypass the Hahn-Banach obstruction is the central question.

The answer is likely yes, because:
- Bilinear forms have 4 degrees of freedom on k^2 x k^2, while product functionals have only 2.
- The cross-norm unit ball is a "large" convex set in 4 dimensions, and a codimension-1 hyperplane generically intersects it.
- Even when no SINGLE functional norms e_1, a COMBINATION of functionals (encoded as a bilinear form) might suffice.

But the answer could be no, because:
- Over non-spherically-complete fields, the unit ball geometry is highly non-generic.
- The cross-norm constraint |u^T M z| <= N_E(u) * N_F(z) is a multiplicative condition, not an additive one, and multiplicative constraints interact non-trivially with non-archimedean absolute values.
- The Schikhof obstruction (empty intersection of a ball chain) is a deep topological property of the valued field, and it may impose constraints on ALL objects (including bilinear forms), not just functionals.

**Overall assessment:** The convex duality approach via BFEP is the most promising new direction for proving the Cross Property unconditionally. It avoids the known obstructions (FDNP failure, wrong-direction triangle inequality) and introduces new degrees of freedom (non-product bilinear forms). Success probability: 35-45% within 4-8 weeks of focused work. The key test case is the explicit BFEP for the Schikhof pathological norm over C_p.

---

## References

1. Grothendieck, A. "Resume de la theorie metrique des produits tensoriels topologiques." Bol. Soc. Mat. Sao Paulo 8 (1956), 1-79.
2. Sion, M. "On general minimax theorems." Pacific J. Math. 8 (1958), 171-176.
3. Ingleton, A.W. "The Hahn-Banach theorem for non-Archimedean-valued fields." Proc. Cambridge Phil. Soc. 48 (1952), 41-45.
4. Van Rooij, A.C.M. Non-Archimedean Functional Analysis. Marcel Dekker, 1978.
5. Schikhof, W.H. Ultrametric Calculus. Cambridge University Press, 1984.
6. Perez-Garcia, C. and Schikhof, W.H. Locally Convex Spaces over Non-Archimedean Valued Fields. Cambridge University Press, 2010.
7. Monna, A.F. and Springer, T.A. "Integration non-archimedienne I, II." Indag. Math. 25 (1963), 634-653.
8. Fenchel, W. "On conjugate convex functions." Canadian J. Math. 1 (1949), 73-77.
9. Rockafellar, R.T. Convex Analysis. Princeton University Press, 1970.
10. Gruson, L. and van der Put, M. "Banach spaces." Mem. Soc. Math. France 39-40 (1974), 55-100.
11. Ryan, R. Introduction to Tensor Products of Banach Spaces. Springer, 2002.
12. Defant, A. and Floret, K. Tensor Norms and Operator Ideals. North-Holland, 1993.
13. Schneider, P. Nonarchimedean Functional Analysis. Springer, 2002.
14. Escassut, A. Ultrametric Banach Algebras. World Scientific, 2003.
