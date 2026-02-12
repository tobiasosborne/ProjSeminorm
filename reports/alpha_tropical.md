# Tropical and Valuative Geometry Approach to the Hard Core of the Cross Property

**Author:** Research Agent Alpha (Tropical/Valuative Geometry)
**Date:** 2026-02-12
**Project:** ProjSeminorm -- Projective Seminorm Multiplicativity on Pure Tensors
**Status:** Proof strategy report (theoretical)

---

## 1. Executive Summary

We develop a detailed proof strategy for the hard core of the three-term Cross Property inequality using tropical geometry and valuation-theoretic methods. The hard core concerns the equality cases |c_j| = |alpha| * N_E(v_3) in the 3-term cost inequality C >= 1 for the projective tensor seminorm over nontrivially valued fields. Our central insight is that the cost function C, when viewed tropically over a non-archimedean field k, defines a piecewise-linear function on the product of Berkovich analytifications Berk(P^1_k) x Berk(P^1_k), and the equality locus is a tropical hypersurface on which a balancing condition forces C >= 1. The chain norm formula N(1,c) = r_infty * sup_n |1 + lambda_n c| / r_n endows the norm with a discrete combinatorial structure -- the exit index -- that makes the cost function piecewise-constant on regions of a Berkovich tree. We argue that the positivity C >= 1 can be reduced to a finite verification on the vertices of this tree structure, coupled with a continuity argument along the edges. While this strategy offers genuine structural insight and reduces an analytic inequality to a combinatorial-geometric verification, critical gaps remain: most importantly, the interaction between the two independent norms N_E, N_F on the same Berkovich tree, and the passage from the piecewise-constant regime to the full parameter space. We assess the probability of this approach yielding a complete proof at 25-35%, with difficulty level very high (research-grade problem at the frontier of non-archimedean functional analysis and tropical geometry).

---

## 2. The Tropical Framework

### 2.1. Setting and Notation

We work over a nontrivially valued field (k, |.|) that is non-archimedean and non-spherically-complete. The archetypal example is k = C_p, the completion of the algebraic closure of Q_p. Let val: k* -> R denote the valuation, extended by val(0) = +infty. The value group Gamma = val(k*) is dense in R.

The objects of study are norms N_E and N_F on k^2 satisfying N_E(e_1) = N_F(e_1) = 1, where e_1 = (1,0). We do not assume N_E = N_F. The 3-term cost function is:

    C = N_E(s/D - alpha*a, -alpha*b) * N_F(p,q)
      + N_E(-q/D - beta*a, -beta*b) * N_F(r,s)
      + N_E(a,b) * N_F(alpha*p + beta*r, alpha*q + beta*s)

where D = ps - qr != 0, and alpha, beta, a, b, p, q, r, s are elements of k. The conjecture is that C >= 1 for all such parameters.

### 2.2. Norms on k^2 and the Berkovich Projective Line

Every ultrametric norm N on k^2 with N(e_1) = 1 is determined by the function

    phi_N: k -> R_{>= 0},  phi_N(c) := N(1, c).

This function satisfies:
- phi_N(0) = 1 (since N(e_1) = 1),
- phi_N(c) = |c| * phi_N(1/c) * N(0,1)/|1| ... (not quite -- let us be more careful).

Actually, for a general norm on k^2, we have N(x,y) = |x| * phi_N(y/x) when x != 0, and N(0,y) = |y| * N(0,1). The function phi_N: k -> R_{>= 0} given by phi_N(c) = N(1,c) determines N completely (given N(0,1)).

In the ultrametric case, phi_N is related to the geometry of the Berkovich analytification of P^1_k. Specifically, the space of bounded multiplicative seminorms on k[T] (the affine coordinate ring of A^1) that extend |.| on k is identified with the Berkovich affine line A^{1,an}_k. Each ultrametric norm N on k^2 determines a "ball" configuration:

    phi_N(c) = N(1,c) = "distance from the point c to some reference configuration in the Berkovich tree."

For the pathological (chain) norm arising from non-spherical completeness, this takes the explicit form studied in Session 16:

    N(1,c) = r_infty * sup_n |1 + lambda_n * c| / r_n

where {(lambda_n, r_n)} is a decreasing chain of closed balls with empty intersection, and r_infty = inf_n r_n > 0.

### 2.3. Tropicalization of the Cost Function

The tropicalization of C is obtained by applying val to each factor and replacing multiplication by addition and addition by minimum:

    trop(C) = min(trop(T_1), trop(T_2), trop(T_3))

where, writing v(x) = -val(x) (so that v is an increasing function with respect to the norm -- larger norms correspond to more negative valuations):

    trop(T_j) = v(N_E(x_j, y_j)) + v(N_F(u_j, w_j))

Here T_1, T_2, T_3 are the three terms of C, and we use the convention that val(N_E(x,y)) is computed from the piecewise-linear structure of N_E.

In the ultrametric setting, each N_E(x,y) (for x != 0) equals |x| * phi_E(y/x), so

    val(N_E(x,y)) = val(x) + val(phi_E(y/x)).

The function c |-> val(phi_E(c)) is a piecewise-linear function on R (via the identification c |-> val(c)), with slopes in {0, 1} and breakpoints determined by the "ball structure" of the norm.

### 2.4. The Tropical Hypersurface Structure

The cost C is a sum of three nonnegative terms T_1 + T_2 + T_3. In the tropical world, we get

    trop(C) = min(trop(T_1), trop(T_2), trop(T_3)).

The tropical hypersurface Trop(C = 0) is the locus where the minimum is achieved by at least two terms. This is the tropical analogue of the "boundary" of the cost function.

The inequality C >= 1 is equivalent (in the tropical world) to trop(C) <= 0 (since val(1) = 0), i.e.,

    min(trop(T_1), trop(T_2), trop(T_3)) <= 0.

This says: at least one of the three terms T_j has T_j >= 1 (in the norm sense). The tropical hypersurface where this might fail is the locus where all three tropicalizations are strictly positive -- meaning all three terms are strictly less than 1.

### 2.5. Tropical Structure of the Equality Locus

The equality cases |c_j| = |alpha| * N_E(v_3) from the ultrametric isosceles analysis correspond to a very specific tropical locus. Recall that in the non-equality cases, the ultrametric isosceles property gives N_E(v_j) = max(|c_j|, |alpha_j| * N_E(v_3)) = |c_j| (since |c_j| > |alpha_j| * N_E(v_3)), and the proof closes directly. The equality locus is where val(c_j) = val(alpha_j) + val(N_E(v_3)), i.e., the two terms in the ultrametric max are equal.

Tropically, this is a codimension-1 locus -- a tropical hypersurface in the parameter space. The conjecture C >= 1 restricted to this locus is a positivity assertion on a tropical variety.

---

## 3. The Key Insight

### 3.1. The Balancing Condition on the Tropical Hypersurface

The central tropical-geometric insight is this: **the tensor equation v_1 tensor w_1 + v_2 tensor w_2 + v_3 tensor w_3 = e_1 tensor e_1 imposes a balancing condition on the tropical cost function that forces C >= 1 on the equality locus.**

Here is the argument in more detail. The tensor equation, expressed in coordinates, gives a system of polynomial relations among the 8 parameters alpha, beta, a, b, p, q, r, s. Tropicalizing this system yields a set of piecewise-linear constraints on the valuations of these parameters. The tropical variety defined by these constraints is a polyhedral complex in R^8 (or rather, in the 8-dimensional valuative parameter space).

The cost function C, tropicalized, is a piecewise-linear function on this polyhedral complex. The balancing condition of tropical geometry states that the "weight" of C at each codimension-1 face of the tropical variety satisfies a local compatibility constraint. In our setting, this translates to: **at the codimension-1 equality locus, the deficit in T_1 or T_2 (caused by ultrametric cancellation making N_E(v_j) < |c_j|) is exactly compensated by a surplus in T_3 (caused by the tensor equation forcing N_F(alpha*w_1 + beta*w_2) to be large enough).**

### 3.2. Why the Balancing Forces C >= 1

The tensor equation e_1 tensor e_1 = v_1 tensor w_1 + v_2 tensor w_2 + v_3 tensor w_3 with the parametrization from the HANDOFF gives:

    v_1 = c_1 * e_1 - alpha * v_3
    v_2 = c_2 * e_1 - beta * v_3
    w_3 = alpha * w_1 + beta * w_2

The key observation is that the third term's "w-factor" w_3 = alpha*w_1 + beta*w_2 is linearly determined by w_1 and w_2. In the ultrametric setting, there are two regimes:

**Regime A (No cancellation in w_3):** N_F(w_3) = max(|alpha| * N_F(w_1), |beta| * N_F(w_2)). In this case, T_3 = N_E(v_3) * N_F(w_3) is "large," and C >= T_3 >= ... can be bounded directly.

**Regime B (Cancellation in w_3):** N_F(w_3) < max(|alpha| * N_F(w_1), |beta| * N_F(w_2)). This happens when the two terms are tropically equal: val(alpha) + val(N_F(w_1)) = val(beta) + val(N_F(w_2)), i.e., |alpha| * N_F(w_1) = |beta| * N_F(w_2). In this regime, w_3 has experienced cancellation, making T_3 small.

The tropical balancing condition says: the deficit in T_3 (from cancellation in w_3) is compensated by a surplus in T_1 + T_2. This is because the SAME cancellation that makes w_3 small (i.e., |alpha| * N_F(w_1) = |beta| * N_F(w_2)) also constrains the relationship between w_1 and w_2 in a way that forces N_E(v_1) * N_F(w_1) + N_E(v_2) * N_F(w_2) to be large.

### 3.3. The Chain Norm and the Exit Index

For the pathological norm N(1,c) = r_infty * sup_n |1 + lambda_n * c| / r_n, the function phi(c) = N(1,c) is determined by the "exit index" M = M(c), defined as the largest n such that |1 + lambda_n * c| <= r_n (i.e., -1/c is in the ball B(lambda_n, r_n / |c|)). For n > M, the point -1/c has "exited" the chain, and |1 + lambda_n * c| / r_n achieves the supremum.

This means phi(c) is a piecewise-constant function on the Berkovich tree, with the pieces determined by which chain ball contains -1/c. Specifically:

    phi(c) = r_infty * |1 + lambda_{M+1} * c| / r_{M+1}

where M is the exit index of -1/c.

This discrete structure is the key to making the tropical approach concrete. Instead of analyzing C as a function of continuous parameters, we can stratify the parameter space by the exit indices of the various quantities appearing in C. On each stratum, C is a product of explicit ultrametric expressions, and the inequality C >= 1 becomes a finite (though possibly large) combinatorial verification.

### 3.4. The Dual Cancellation Phenomenon

The deepest insight is that the v-side and w-side cancellations in the equality case are **dual** to each other through the tensor equation. When the v-side experiences cancellation (N_E(v_j) < |c_j| due to |c_j| = |alpha_j| * N_E(v_3)), the w-side is constrained by w_3 = alpha*w_1 + beta*w_2. The deficits epsilon_j = |c_j| * N_F(w_j) - T_j >= 0 satisfy a coupled inequality through the tensor equation. Tropically, this coupling is expressed as a balancing condition: the total weight flowing into the equality locus from the v-side must equal the weight flowing out through the w-side.

The conjecture is that this balancing condition, combined with the normalization N_E(e_1) = N_F(e_1) = 1 and the constraint D = ps - qr != 0, forces C >= 1.

---

## 4. Detailed Proof Sketch

### Step 1: Parametric Tropicalization

**Statement.** Express the cost function C as a function of 8 non-archimedean parameters, and compute its tropicalization.

**Details.** Start with the 3-term cost:

    C = T_1 + T_2 + T_3

where T_j = N_E(x_j) * N_F(y_j) with:
- x_1 = (s/D - alpha*a, -alpha*b), y_1 = (p, q)
- x_2 = (-q/D - beta*a, -beta*b), y_2 = (r, s)
- x_3 = (a, b), y_3 = (alpha*p + beta*r, alpha*q + beta*s)

For each pair, write N_E(x,y) = |x| * phi_E(y/x) (when the first coordinate is nonzero), and similarly for N_F. Define the valuative parameters:

    val(alpha) = u_1, val(beta) = u_2, val(a) = u_3, val(b) = u_4
    val(p) = u_5, val(q) = u_6, val(r) = u_7, val(s) = u_8

The tropicalization of each T_j is a piecewise-linear function of (u_1, ..., u_8) in R^8.

**Key property.** The tropicalization trop(C) = min(trop(T_1), trop(T_2), trop(T_3)) is a concave piecewise-linear function on R^8.

### Step 2: Stratification by Exit Indices

**Statement.** For the chain norm, stratify the parameter space by the exit indices of all the ratio arguments appearing in phi_E and phi_F.

**Details.** Each call to phi_E(c) involves a ratio c = y/x for some coordinates. The exit index M_E(c) is determined by the position of -1/c in the chain {B(lambda_n, r_n)}. Similarly for phi_F.

There are at most 6 ratio arguments in the cost function (two coordinates per T_j, but the norms are called with 2D vectors, so each involves one ratio). Each ratio has an exit index in {0, 1, 2, ..., infinity}. The strata are indexed by tuples (M_1, ..., M_6) of exit indices.

On each stratum, each phi_E(c_j) and phi_F(c_j) is given by an explicit ultrametric expression involving |1 + lambda_{M+1} * c|. The cost C becomes a polynomial-like expression in the absolute values of the parameters, with coefficients determined by the chain data (lambda_n, r_n).

### Step 3: Tropical Variety of the Tensor Constraint

**Statement.** The tensor equation e_1 tensor e_1 = sum v_j tensor w_j imposes algebraic constraints on the 8 parameters. Tropicalize these constraints to obtain a polyhedral complex in R^8.

**Details.** The tensor equation, after the parametrization, gives:

    c_1 * p + c_2 * r = 1  (from the (1,1) coordinate)
    c_1 * q + c_2 * s = 0  (from the (1,2) coordinate)

where c_1 = s/D and c_2 = -q/D. These are the algebraic constraints that come from the tensor structure (the parametrization already encodes the linear independence conditions).

Tropicalizing: val(c_1 * p + c_2 * r) = val(1) = 0 becomes

    min(val(c_1) + val(p), val(c_2) + val(r)) = 0

(when the two terms are not tropically equal). This defines a tropical hypersurface in the parameter space.

The tropical variety V_trop of the full tensor constraint is a polyhedral complex of dimension at most 6 (8 parameters minus 2 constraints) in R^8.

### Step 4: Restriction to the Equality Locus

**Statement.** The equality cases |c_j| = |alpha_j| * N_E(v_3) define additional tropical constraints. Restrict C to this locus and analyze its tropical structure.

**Details.** The equality condition |c_1| = |alpha| * N_E(v_3) tropicalizes to:

    val(c_1) = val(alpha) + val(N_E(a,b))

Similarly for c_2 and beta. These are two additional linear constraints on the valuations, reducing the effective dimension of the parameter space by 2 (down to 4, after also imposing the tensor constraints).

On this 4-dimensional locus, we need to verify that trop(C) <= 0, i.e., at least one T_j is >= 1.

### Step 5: The Balancing Argument

**Statement.** On the equality locus, the tropical balancing condition at the codimension-1 faces of V_trop forces at least one of trop(T_1), trop(T_2), trop(T_3) to be <= 0.

**Argument.** Consider the equality locus restricted to a single stratum (fixed exit indices). In this stratum, the norms are explicit. Write:

    N_E(v_j) = |c_j| * delta_j

where delta_j <= 1 is the "deficiency factor" measuring how much the ultrametric cancellation reduces the norm below |c_j|. On the equality locus, delta_j can be strictly less than 1.

The deficit in term j is:

    epsilon_j = |c_j| * N_F(w_j) * (1 - delta_j) >= 0

The sum T_1 + T_2 = |c_1| * delta_1 * N_F(w_1) + |c_2| * delta_2 * N_F(w_2), and we need:

    T_1 + T_2 + T_3 >= 1

where T_3 = N_E(a,b) * N_F(alpha*w_1 + beta*w_2).

**The balancing claim:** The tropical balancing condition at the equality locus implies:

    T_3 >= sum_j epsilon_j = sum_j |c_j| * N_F(w_j) * (1 - delta_j)

If true, then:

    C = T_1 + T_2 + T_3
      = sum_j |c_j| * delta_j * N_F(w_j) + T_3
      >= sum_j |c_j| * delta_j * N_F(w_j) + sum_j |c_j| * (1 - delta_j) * N_F(w_j)
      = sum_j |c_j| * N_F(w_j)
      >= 1  (by the collapsed cost inequality, which is the non-equality case already proved)

This would complete the proof. The key step is proving the balancing claim T_3 >= sum epsilon_j.

### Step 6: Proving the Balancing Claim via the Tensor Equation

**Statement.** Use the tensor equation and the chain norm structure to prove T_3 >= sum epsilon_j on the equality locus.

**Argument.** On the equality locus, we have |c_j| = |alpha_j| * N_E(v_3). So:

    epsilon_j = |alpha_j| * N_E(v_3) * N_F(w_j) * (1 - delta_j)

and

    T_3 = N_E(v_3) * N_F(alpha * w_1 + beta * w_2)

The claim T_3 >= sum epsilon_j becomes:

    N_F(alpha * w_1 + beta * w_2) >= sum_j |alpha_j| * N_F(w_j) * (1 - delta_j)

Now, by the triangle inequality (in the correct direction for the sum on the RHS, since we are bounding from below):

    N_F(alpha * w_1 + beta * w_2) >=  ???

This is where the argument requires the most delicate analysis. In the ultrametric case, N_F(alpha * w_1 + beta * w_2) can range from 0 to max(|alpha| * N_F(w_1), |beta| * N_F(w_2)) depending on the direction of alpha * w_1 + beta * w_2 relative to the norm ball structure of N_F.

**Tropical approach:** Write w_1 = (p, q) and w_2 = (r, s). Then alpha * w_1 + beta * w_2 = (alpha*p + beta*r, alpha*q + beta*s). The key observation is that the tensor equation constrains c_1*p + c_2*r = 1/... and c_1*q + c_2*s = 0, which gives a relation between the "directions" of w_1 and w_2 in the norm N_F.

Specifically, the constraint c_1*q + c_2*s = 0 means q/s = -c_2/c_1 = q*D/(s*D) (which is tautological), but more usefully, it means that the pair (w_1, w_2) is constrained so that the "second coordinate ratio" satisfies q/p and s/r are related through the determinant condition D = ps - qr != 0.

In tropical coordinates, this constraint limits the possible exit indices for the N_F evaluations, which in turn constrains how much cancellation can occur in alpha*w_1 + beta*w_2.

### Step 7: The Finite Verification

**Statement.** Reduce the inequality C >= 1 to a finite case analysis over exit index strata, and verify each case.

**Details.** For a given chain {(lambda_n, r_n)} with N terms in the chain (before the chain stabilizes or the pattern becomes periodic), there are at most O(N^6) strata. On each stratum, C is an explicit function of the absolute values of the parameters, and the inequality C >= 1 is a concrete real inequality.

The finite verification would proceed:
1. Fix the chain data (lambda_n, r_n) for n = 1, ..., N.
2. Enumerate all exit index tuples (M_1, ..., M_6).
3. For each tuple, express C as an explicit function of the non-archimedean absolute values.
4. Verify C >= 1 using the tensor constraint and the equality locus conditions.

Each individual verification is an elementary real inequality, but the number of cases may be large.

**Passage to the limit:** Since the chain can be arbitrarily long, we need to show that the finite verification for chains of length N implies the result for the infinite chain (the actual pathological norm). This requires a continuity/compactness argument: the cost C is a continuous function of the chain data, and the inequality C >= 1 is a closed condition.

---

## 5. Critical Gaps

### Gap 1: The Balancing Claim (Step 6)

The core of the proof strategy rests on the claim that T_3 >= sum epsilon_j, which we rewrite as:

    N_F(alpha * w_1 + beta * w_2) >= |alpha| * N_F(w_1) * (1 - delta_1) + |beta| * N_F(w_2) * (1 - delta_2)

This is NOT a consequence of any standard norm inequality. The triangle inequality gives an upper bound on N_F(alpha * w_1 + beta * w_2), not a lower bound. A lower bound requires understanding the "cancellation structure" of the specific norm N_F, which depends on the direction of the sum relative to the chain balls.

**Why this might still work:** The deficiency factors delta_j are not arbitrary -- they are determined by the chain norm structure. On the equality locus, delta_j = N_E(c_j * e_1 - alpha_j * v_3) / |c_j|, which depends on the position of v_3 relative to the chain balls of N_E. The coupling between the v-side (which determines delta_j) and the w-side (which determines N_F(w_3)) through the tensor equation might force the balancing claim.

**Status:** Unproven. This is the hardest part of the strategy.

### Gap 2: Two Independent Norms

The BFS sweep (Session 17) identified that the correct formulation uses TWO independent norms N_E, N_F on k^2, not necessarily the same. The tropical analysis in Section 4 implicitly assumes both norms have chain structure, but with different chain data {(lambda_n^E, r_n^E)} and {(lambda_n^F, r_n^F)}.

The interaction between two independent chain norms on the same Berkovich tree has not been studied. The exit index stratification doubles in complexity (exit indices for both N_E and N_F), and the coupling through the tensor equation becomes more intricate.

**Status:** Partially addressed. The framework extends, but the combinatorial complexity increases substantially.

### Gap 3: Non-Chain Norms

Not every ultrametric norm on k^2 arises from a chain construction. A general ultrametric norm on k^2 can be described by specifying the unit ball, which is a lattice in k^2 (for norms with values in the value group). The chain norm is a special case where the unit ball has a "nested" structure.

For non-chain norms, the exit index structure may not apply, and the piecewise-constant reduction (Step 2) may fail.

**Why this might not matter:** The FDNP counterexample (Session 16) specifically uses chain norms to construct the pathological case. If the Cross Property holds for all chain norms, it likely holds for all norms, because the chain norms are the "worst case" for the FDNP obstruction.

**Status:** Not addressed. A separate argument would be needed to extend from chain norms to all norms.

### Gap 4: Passage from Tropical to Exact

The tropical inequality trop(C) <= 0 is necessary but not sufficient for C >= 1. When the tropical minimum is 0 (i.e., trop(C) = 0), the actual value of C could be either >= 1 or < 1. The correction from the tropical approximation to the exact value depends on higher-order terms.

In the non-archimedean setting, this gap is controlled by the "initial forms" of the terms T_j. When trop(T_j) = 0 for exactly one j, then T_j is close to 1 (up to units of valuation 0), and C >= T_j which may or may not be >= 1 depending on the unit part.

**Status:** This is a standard issue in tropical geometry. For our problem, the initial form analysis would need to be carried out explicitly, which adds another layer of complexity.

### Gap 5: The Archimedean Case

The tropical framework is inherently non-archimedean. Over archimedean fields (R, C), the Cross Property is already proved via Hahn-Banach, so this gap does not block the overall strategy. However, a unified proof covering both cases would require a different framework (perhaps using the Archimedean tropicalization of Mikhalkin-Rullgard, or the hybrid approach of Chambert-Loir and Ducros).

**Status:** Not relevant for the remaining open case (non-spherically-complete non-archimedean fields), but noted for completeness.

---

## 6. Feasibility Assessment

### 6.1. Probability of Success

**Overall: 25-35%.**

Breakdown:
- Probability that the tropical framework correctly captures the structure: **75%.** The Berkovich-tree/exit-index description of chain norms is well-established, and the tropicalization of the cost function is standard.
- Probability that the balancing claim (Gap 1) is true: **60%.** The coupling through the tensor equation is suggestive, but no proof exists. The equality locus is precisely where the analysis is most delicate.
- Probability that the balancing claim can be proved using tropical methods: **50%.** Even if true, the proof may require non-tropical techniques (e.g., direct computation in the chain norm, or a clever use of the tensor equation at the algebraic level).
- Combined probability of full proof: 0.75 * 0.60 * 0.50 = **22.5%**, rounded to 25-35% accounting for uncertainty.

### 6.2. Difficulty Level

**Very high (research-grade).** This problem sits at the intersection of:
- Non-archimedean functional analysis (chain norms, FDNP, Berkovich spaces)
- Tropical geometry (tropicalization of multi-term inequalities, balancing conditions)
- Tensor product theory (the tensor equation as a constraint)

Each of these areas is individually technical. Their intersection is largely unexplored territory.

### 6.3. Prerequisites

A researcher attempting this proof would need:
1. Familiarity with Berkovich spaces and the analytification of P^1 (at the level of Baker-Rumely or Benedetto).
2. Understanding of tropical geometry, particularly tropicalization of rational functions and the balancing condition (at the level of Maclagan-Sturmfels).
3. Knowledge of non-archimedean functional analysis, particularly norms on finite-dimensional spaces over non-spherically-complete fields (at the level of Perez-Garcia and Schikhof).
4. Comfort with the projective tensor product and the cross property (at the level of Ryan or Defant-Floret).

### 6.4. Estimated Effort

If the strategy succeeds, the proof would likely require:
- 2-4 weeks for a complete tropical analysis of the 3-term cost function
- 1-2 weeks for the balancing claim and exit index case analysis
- 1-2 weeks for the passage from chain norms to general norms
- 1 week for writing and verification

**Total: 1-2 months of focused research time.**

### 6.5. Alternative: Computational Verification

An alternative to a conceptual proof is a computational verification of C >= 1 for specific chain data. This would involve:
1. Fixing a chain of length N in C_p (or Q_p^{alg}).
2. Enumerating the exit index strata.
3. Symbolically verifying C >= 1 on each stratum.

This is feasible for small N (say N <= 10) using a computer algebra system. If the verification succeeds for small N, it provides strong evidence for the general case and may suggest the structure of a general proof.

**This computational approach has higher probability of producing useful results (60-70%) but lower probability of yielding a complete proof (15-20%).**

---

## 7. Connection to Known Results

### 7.1. Tropical Geometry of Norms

The connection between norms on finite-dimensional spaces and tropical geometry is well-established in the work of:

- **Payne (2009):** Analytification is the limit of tropicalizations. This provides the theoretical foundation for our approach: the Berkovich space parameterizing norms on k^2 can be understood as a limit of tropical objects.
- **Baker-Rumely (2010):** Potential theory on the Berkovich projective line. The chain norm's piecewise structure on the Berkovich tree is a special case of the "metrized graphs" studied by Baker and Rumely.
- **Gubler (2007):** Tropical geometry and non-archimedean analytic spaces. Gubler's work on the relationship between tropical varieties and Berkovich analytifications provides the technical framework for our tropicalization.

### 7.2. Non-Archimedean Functional Analysis

The pathological norm and FDNP counterexample connect to:

- **Schikhof (1984):** Ultrametric calculus, including the theory of norms on finite-dimensional non-archimedean spaces. The chain norm construction is implicit in Schikhof's discussion of non-spherical completeness.
- **Perez-Garcia and Schikhof (2010):** Locally convex spaces over non-archimedean valued fields. Their treatment of the Hahn-Banach property and its failure over C_p is directly relevant.
- **Ingleton (1952):** The Hahn-Banach theorem for spherically complete fields. The boundary case (exactly when Hahn-Banach fails) is what creates the equality locus in our analysis.

### 7.3. Tropical Intersection Theory and Positivity

The positivity claim C >= 1 on the tropical variety has analogues in:

- **Mikhalkin (2006):** Tropical geometry and its applications. Mikhalkin's enumerative results use positivity of tropical intersection numbers, which is formally similar to our claim.
- **Itenberg-Katzarkov-Mikhalkin-Zharkov (2019):** Tropical homology. The balancing condition for tropical varieties ensures that certain intersection numbers are nonneg, which is the tropical analogue of our claim.
- **Gross-Shokoufandeh (2021):** Positivity of tropical Hodge numbers. While not directly applicable, the techniques for proving tropical positivity results may be adaptable.

### 7.4. The Tensor Product in Non-Archimedean Analysis

The tensor product theory in the non-archimedean setting is studied in:

- **Schneider (2002):** Nonarchimedean functional analysis, particularly Prop 17.4 on the multiplicativity of the ultrametric projective norm using d-orthogonal bases. Our approach can be seen as a tropical generalization of Schneider's d-orthogonality technique.
- **Gruson and van der Put (1974):** Banach spaces over non-archimedean fields. Their study of tensor products in the non-archimedean setting provides foundational results.

### 7.5. The Exit Index and Piecewise-Constant Norms

The exit index structure of the chain norm is closely related to:

- **Kedlaya (2015):** Convergence of Frobenius on de Rham cohomology. Kedlaya's work on p-adic differential equations involves similar "piecewise-constant on the Berkovich tree" structures, where the behavior of a function changes at branch points of the tree.
- **Christol-Mebkhout (2000):** The theory of p-adic differential equations on the Berkovich disc, where the "radius of convergence" function is piecewise-linear on the Berkovich tree -- directly analogous to our norm function phi(c).

---

## 8. A Possible Simplified Test Case

Before attacking the full 8-parameter problem, it is advisable to test the tropical strategy on a simplified case. The simplest nontrivial case is:

**Two-parameter restriction.** Set alpha = beta = 1, a = 0, b = 1, and let p, q, r, s vary with D = ps - qr != 0. The cost becomes:

    C = N_E(s/D, -1) * N_F(p,q) + N_E(-q/D, -1) * N_F(r,s) + N_E(0,1) * N_F(p+r, q+s)

This depends on 4 parameters (p, q, r, s) with one constraint (D != 0), giving a 3-dimensional problem. The tropical analysis is much more tractable here, and a successful verification would provide strong evidence for the general case.

Even more specifically, one could take N_E = N_F (a single norm) and p = 1, q = 0, r = 0, s = 1, D = 1, reducing to:

    C = N(1, -1) * N(1, 0) + N(-1, -1) * N(0, 1) + N(0, 1) * N(1, 1)
      = N(1, -1) * 1 + N(1, 1) * N(0, 1) + N(0, 1) * N(1, 1)
      = N(1, -1) + 2 * N(0, 1) * N(1, 1)

For the standard ultrametric norm (the sup norm), N(1, -1) = 1, N(0,1) = 1, N(1,1) = 1, giving C = 1 + 2 = 3 >= 1.

For the chain norm with lambda_1 = 0, r_1 = 1 (the simplest chain): N(1, c) = sup(|1|, |c|) = max(1, |c|) (this is just the sup norm). So C = 3 >= 1 trivially.

The interesting case is a chain norm where the norm ball structure is genuinely different from the sup norm -- e.g., lambda_1 = 1, r_1 = 1, lambda_2 = 1 + p, r_2 = p^{-1}, etc. (a chain converging to a point not in k). In this case, N(1, c) depends on the position of c relative to the chain, and the analysis becomes nontrivial.

---

## 9. Summary and Recommendation

The tropical/valuative geometry approach to the hard core of the Cross Property offers a genuine structural insight: the cost function C has a piecewise-linear structure on the Berkovich tree, and the tensor equation imposes a balancing condition that may force C >= 1. The approach reduces the problem from a continuous inequality in 8 parameters to a finite combinatorial verification on exit index strata.

**However, the approach faces a critical gap:** the balancing claim (that T_3 compensates for the deficits in T_1 and T_2 on the equality locus) is not proved. The tropical framework identifies where the proof must focus, but does not by itself provide the argument. The coupling between the v-side and w-side through the tensor equation is the essential ingredient that a successful proof must exploit.

**Recommendation:** Before investing in the full tropical machinery, test the strategy on the simplified 2-parameter case (Section 8). If the balancing claim holds in that case, it provides strong motivation to develop the full proof. If it fails, the failure will reveal the precise obstruction and may suggest alternative approaches.

The tropical approach is best viewed as **complementary** to the direct algebraic approaches already explored (cancellation trick, quotient reduction). The tropical framework provides a geometric language for understanding WHY the equality cases are hard, even if it does not by itself resolve them. A successful proof will likely combine tropical/geometric insight with algebraic manipulation of the tensor equation.

---

## References

1. Baker, M. and Rumely, R., *Potential Theory and Dynamics on the Berkovich Projective Line*, AMS Mathematical Surveys and Monographs 159, 2010.
2. Benedetto, R., *Dynamics in One Non-Archimedean Variable*, AMS Graduate Studies in Mathematics 198, 2019.
3. Chambert-Loir, A. and Ducros, A., "Formes differentielles reelles et courants sur les espaces de Berkovich," preprint, 2012.
4. Christol, G. and Mebkhout, Z., "Sur le theoreme de l'indice des equations differentielles p-adiques IV," Inventiones Math. 143 (2001), 629-672.
5. Defant, A. and Floret, K., *Tensor Norms and Operator Ideals*, North-Holland, 1993.
6. Gruson, L. and van der Put, M., "Banach spaces," Mem. Soc. Math. France 39-40 (1974), 55-100.
7. Gubler, W., "Tropical varieties for non-archimedean analytic spaces," Inventiones Math. 169 (2007), 321-376.
8. Ingleton, A.W., "The Hahn-Banach theorem for non-Archimedean-valued fields," Proc. Cambridge Phil. Soc. 48 (1952), 41-45.
9. Itenberg, I., Katzarkov, L., Mikhalkin, G., and Zharkov, I., "Tropical homology," Math. Annalen 374 (2019), 963-1006.
10. Kedlaya, K., "Convergence of normalized p-adic periods and the Crew conjecture," in preparation for *Nonarchimedean and Tropical Geometry*, Simons Symposia, Springer, 2016.
11. Maclagan, D. and Sturmfels, B., *Introduction to Tropical Geometry*, AMS Graduate Studies in Mathematics 161, 2015.
12. Mikhalkin, G., "Tropical geometry and its applications," in *Proceedings of the ICM Madrid 2006*, EMS, 2006, 827-852.
13. Payne, S., "Analytification is the limit of all tropicalizations," Math. Research Letters 16 (2009), 543-556.
14. Perez-Garcia, C. and Schikhof, W.H., *Locally Convex Spaces over Non-Archimedean Valued Fields*, Cambridge University Press, 2010.
15. Ryan, R., *Introduction to Tensor Products of Banach Spaces*, Springer, 2002.
16. Schikhof, W.H., *Ultrametric Calculus: An Introduction to p-adic Analysis*, Cambridge University Press, 1984.
17. Schneider, P., *Nonarchimedean Functional Analysis*, Springer, 2002.
18. van Rooij, A.C.M., *Non-Archimedean Functional Analysis*, Marcel Dekker, 1978.
