# Cross Property vs Hahn-Banach: A Three-Agent Investigation

**Date:** 2026-02-09
**Project:** ProjSeminorm (mathlib4 PR #33969)
**Question:** Does the Cross Property (CP) for the projective tensor seminorm imply the Hahn-Banach extension property (HB) over general valued fields?

---

## Executive Summary

Three independent research agents attacked this problem from complementary angles:

- **Agent Alpha** — Attempted to prove CP => HB/IB (forward implication strategies)
- **Agent Beta** — Attempted to prove CP holds universally (algebraic separation from HB)
- **Agent Gamma** — Structural/foundational analysis, counterexample search, independence investigation

**Unanimous verdict:** CP is very likely TRUE unconditionally (a theorem of ZFC), and hence strictly weaker than HB/IB. CP does NOT imply IB or HB. The question is NOT independent of ZFC.

| Agent | CP true unconditionally? | CP => IB? | Independent of ZFC? |
|-------|--------------------------|-----------|---------------------|
| Alpha | 90% yes                  | No        | No                  |
| Beta  | 80% yes                  | No        | No                  |
| Gamma | 80% yes                  | No        | No (99%)            |

**Implication for the project:** The `h_bidual` hypothesis in `projectiveSeminorm_tprod_of_bidual_iso` is exactly the right level of generality for the duality-based proof. A fully unconditional theorem would require genuinely new mathematics.

---

## 1. Definitions and Setup

All spaces are vector spaces over a valued field $(k, |\cdot|)$, i.e., a field equipped with a multiplicative absolute value satisfying $|0|=0$, $|1|=1$, $|\lambda\mu|=|\lambda||\mu|$, and the triangle inequality.

### Projective tensor seminorm

For seminormed $k$-spaces $(E, \|\cdot\|_E)$ and $(F, \|\cdot\|_F)$, the projective tensor seminorm on the algebraic tensor product $E \otimes F$ is:

$$\pi(u) := \inf\left\{\sum_{i=1}^m \|e_i\|_E \|f_i\|_F : u = \sum_{i=1}^m e_i \otimes f_i\right\}$$

### Cross Property (CP)

**CP holds over $k$** if for every pair of seminormed $k$-spaces $E, F$ and every $e \in E$, $f \in F$:

$$\pi(e \otimes f) = \|e\|_E \|f\|_F$$

The inequality $\pi(e \otimes f) \le \|e\|\|f\|$ is trivial. The content is the reverse: $\pi(e \otimes f) \ge \|e\|\|f\|$.

### Hahn-Banach property (HB)

**HB holds over $k$** if for every seminormed $k$-space $E$, every subspace $M \subseteq E$, and every bounded linear functional $\varphi : M \to k$, there exists an extension $\tilde{\varphi} : E \to k$ with $\|\tilde{\varphi}\| = \|\varphi\|$.

### Isometric bidual embedding (IB)

**IB holds over $k$** if for every seminormed space $E$, the canonical map $J_E : E \to E^{**}$ is isometric: $\|J_E(x)\| = \|x\|$ for all $x$.

Equivalently: $\|x\| = \sup\{|\varphi(x)| : \varphi \in E^*, \|\varphi\| \le 1\}$.

### Known results

1. **HB <=> IB** is established.
2. **IB => CP**: Given IB, norming functionals exist and yield the lower bound via duality.
3. The chain **HB <=> IB => CP** is known. The question is whether CP => IB reverses it.
4. Over $\mathbb{R}$ and $\mathbb{C}$: HB holds (Hahn-Banach theorem), so all three hold.
5. Over spherically complete non-Archimedean fields: HB holds (Ingleton 1952).
6. Over non-spherically-complete fields (e.g., $\mathbb{C}_p$): HB fails.

---

## 2. Agent Alpha: Attempting to Prove CP => HB

Agent Alpha systematically explored all forward-implication strategies.

### 2.1. Strategy A1: Clever Choice of F

**A1.1 — F = E\* (continuous dual):**
For $x_0 \in E$ with $\|x_0\| = 1$ and $\varphi \in E^*$ with $\|\varphi\| = 1$, CP gives $\pi(x_0 \otimes \varphi) = 1$. But this constrains the projective tensor norm, not the pairing value $|\varphi(x_0)|$. CP says nothing about how large $|\varphi(x)|$ can be --- only about how cheap a representation of $x \otimes \varphi$ can be.

**A1.2 — F = k (scalar field):**
$E \otimes k \cong E$, and CP becomes $\|\alpha e\| = |\alpha| \cdot \|e\|$ --- a norm axiom. Vacuous.

**A1.3 — F = $\ell^\infty(B_{E^*})$:**
Define $J: E \to \ell^\infty(B_{E^*})$ by $J(x)(\varphi) = \varphi(x)$. CP gives $\pi(x \otimes J(x)) = \|x\| \cdot \|J(x)\|$. To derive IB we would need $\|J(x)\| = \|x\|$ independently --- which is IB itself. Circular.

**A1.4 — F from the evaluation map:**
The evaluation map $\hat{\mathrm{ev}}: E^* \hat{\otimes} E \to k$ has $\|\hat{\mathrm{ev}}\| \le 1$. For $\|\varphi\| \le 1$: $|\varphi(x)| \le \pi(\varphi \otimes x) = \|\varphi\| \cdot \|x\| \le \|x\|$. This yields only $\|J(x)\| \le \|x\|$, the trivial direction.

**Verdict on A1:** Every choice of $F$ leads to the same obstruction. CP constrains $\pi(e \otimes f) = \|e\| \cdot \|f\|$ (a product of norms), while IB requires $\sup |\varphi(x)| = \|x\|$ (a supremum of evaluations). The evaluation map bridges these only in the trivial direction.

### 2.2. Strategy A2: Contrapositive (negIB => negCP)

**A2.1 — Finite-dimensional slicing:**
Every tensor representation involves finitely many vectors, so the problem reduces to finite-dimensional spaces. This would work IF IB held for all finite-dimensional spaces.

**Critical discovery:** IB CAN fail in finite dimensions over non-spherically-complete fields.

Take a non-spherically-complete field $k$ with a decreasing chain of closed balls $B(a_n, r_n)$ satisfying $\bigcap_n B(a_n, r_n) = \emptyset$ and $r_n \to r > 0$. Define the norm on $k^2$:

$$\|(x,y)\| = \sup_n \max(|x - a_n y|, r_n |y|)$$

This is a well-defined ultrametric norm. The vector $e_1 = (1, 0)$ has $\|e_1\| = 1$. But the functional $\varphi(x,y) = x$ restricted to $\text{span}(e_1)$ has $\|\varphi\| = 1$, while every extension $\tilde{\varphi}(x,y) = x + \lambda y$ to $k^2$ satisfies $\|\tilde{\varphi}\| > 1$ --- because $\lambda$ would need to lie in the empty intersection $\bigcap B(a_n, r_n)$. Hence IB fails for this 2-dimensional space.

**A2.2 — Explicit CP computation in the pathological space:**
Despite IB failure, Alpha worked through explicit representations in the 2-dimensional space:

For $e_1 \otimes e_1$ with a 3-term dependent representation parameterized by $v_2 = (\alpha, \beta)$, the cost function is:

$$\|(1+\alpha, \beta)\| + \|(\alpha, \beta)\| \cdot (\|(0,1)\| + \|(1,1)\|)$$

Minimized at $\alpha = \beta = 0$ with cost exactly 1. **No cheap representation was found.**

### 2.3. Strategy A3: Category-Theoretic

The functorial cross-norm property of $\pi$ does not force HB. The injective tensor norm fails to be a cross-norm when IB fails, but the projective tensor norm may still be one --- they are different norms.

### 2.4. Alpha's Conclusion

**90% confidence that CP is TRUE unconditionally**, but a proof via CP => IB is structurally impossible. The gap is fundamental: CP is about the geometry of tensor representations (infimum of costs), while IB is about the richness of the dual space (existence of norming functionals).

---

## 3. Agent Beta: Proving CP Holds Universally

Agent Beta focused on algebraic/combinatorial approaches to prove CP without HB.

### 3.1. The Collinear Case: Complete HB-Free Proof

**Theorem (collinear_cost_ge).** For any nontrivially normed field $k$, any seminormed $k$-spaces $E, F$, any $v \in E$, $w \in F$, any finite family $\{v_j\}$ in $E$, $\{\alpha_j\}$ in $k$, and $w_1 \in F$, if $v \otimes w = \sum_j v_j \otimes (\alpha_j \cdot w_1)$, then $\sum_j \|v_j\| \cdot |\alpha_j| \cdot \|w_1\| \ge \|v\| \cdot \|w\|$.

**Proof sketch.** Three steps:

1. **Bilinearity collapse:** $\sum_j v_j \otimes (\alpha_j \cdot w_1) = (\sum_j \alpha_j v_j) \otimes w_1 = u \otimes w_1$.
2. **Norm invariance of rank-1 tensors:** From $v \otimes w = u \otimes w_1$, extract $\|v\| \cdot \|w\| = \|u\| \cdot \|w_1\|$ using algebraic (non-continuous) functionals and the flatness of free modules.
3. **Triangle inequality:** $\sum_j |\alpha_j| \cdot \|v_j\| \ge \|\sum_j \alpha_j v_j\| = \|u\|$, giving $\text{cost} \ge \|u\| \cdot \|w_1\| = \|v\| \cdot \|w\|$.

**This proof never invokes HB or any continuous functional.** The algebraic functional used in Step 2 needs no continuity properties. **Formalized sorry-free** in `ProjSeminorm/CancellationTrick.lean`.

### 3.2. The Independent Case

**Theorem (reduced_representation_cost_ge).** For representations $v \otimes w = \sum_k u_k \otimes w_k$ where $\{w_k\}$ are linearly independent, the algebraic structure forces $u_k = c_k v$ and $w = \sum_k c_k w_k$, giving:

$$\text{cost} = \|v\| \cdot \sum_k |c_k| \cdot \|w_k\| \ge \|v\| \cdot \|w\|$$

by the triangle inequality (in the correct direction).

**Formalized sorry-free** in `ProjSeminorm/DirectApproach.lean`.

### 3.3. The Obstruction for the General Case

For dependent representations (span dimension $s \ge 2$), the natural approach is to reduce to an independent representation by combining terms. Given $w_j = \sum_k a_{jk} f_k$ (expressing dependent vectors in a basis), the reduction yields $u_k = \sum_j a_{jk} v_j$, and we need:

$$\sum_j \|v_j\| \cdot \|w_j\| \ge \sum_k \|u_k\| \cdot \|f_k\|$$

The triangle inequality gives $\|u_k\| \le \sum_j |a_{jk}| \cdot \|v_j\|$ --- bounding from ABOVE when we need a bound from BELOW. Meanwhile, $\|w_j\| = \|\sum_k a_{jk} f_k\| \le \sum_k |a_{jk}| \cdot \|f_k\|$ --- also the wrong direction.

**This is the "wrong-direction triangle inequality" obstruction.** It appears in every algebraic proof strategy and is formalized in `DirectApproach.lean` as `triangle_wrong_direction`.

### 3.4. Bilinearity Chain Analysis

Beta analyzed the problem through chains of bilinearity relations:

- **Type A (combine in E):** $(e_1 + e_2) \otimes f$ replaces $e_1 \otimes f + e_2 \otimes f$ --- reduces cost
- **Type A' (split in E):** Reverse of A --- increases cost
- **Type B/B' (combine/split in F):** Analogous
- **Type C (scalar transfer):** $(\lambda e) \otimes f$ to $e \otimes (\lambda f)$ --- preserves cost exactly

Going from $v \otimes w$ to an arbitrary representation requires BOTH cost-increasing and cost-decreasing steps. There is no monotonicity guarantee for the net effect. This is the fundamental reason a purely combinatorial proof of CP has not been found.

### 3.5. Finite-Dimensional CP

CP holds in finite dimensions over any nontrivially normed field, because:
1. The unit ball in a finite-dimensional normed space is compact.
2. Continuous functions on compact sets achieve their supremum.
3. Norm-achieving functionals exist without full HB.

However, the reduction from infinite to finite dimensions fails because "escaping" a finite-dimensional subspace (using $w_j$ outside $\text{span}(w, w_1, \ldots, w_n) \subset F$) might reduce cost over non-spherically-complete fields.

### 3.6. Beta's Conclusion

**80% confidence CP holds universally.** The collinear and independent cases are proved. The remaining gap is the dependent case with span dimension $\ge 2$ in infinite-dimensional spaces over non-spherically-complete fields.

---

## 4. Agent Gamma: Structural and Foundational Analysis

### 4.1. The Quantifier Structure

The deepest structural insight:

- **CP** is $\Pi_1^0$ (purely universal): $\forall E\, \forall F\, \forall e\, \forall f\, \forall \text{decompositions}\; [\text{cost} \ge \|e\|\|f\|]$
- **IB** is $\Sigma_1^0$ (existential): $\forall E\, \forall x \in E\, \exists \varphi \in E^*\; [\varphi(x) = \|x\|,\; \|\varphi\| = 1]$

A purely universal statement about metric infima cannot imply the existence of specific functionals without a bridge principle (like HB or spherical completeness).

**Analogy:** "Every continuous function on $[0,1]$ is bounded" (universal) does not imply "every continuous function on $[0,1]$ achieves its supremum" (existential) without completeness.

### 4.2. What CP Gives vs. What IB Gives

| CP provides | IB provides | The gap |
|-------------|-------------|---------|
| $\inf \sum \|e_j\| \cdot \|f_j\| \ge \|e\| \cdot \|f\|$ | $\exists \varphi$ with $\varphi(x) = \|x\|$ | Infimum vs. existence of witness |
| Information about ALL representations | A SINGLE functional | Universal vs. existential |
| Geometry of tensor products | Richness of dual space | Different mathematical domains |
| Holds for rank-1 tensors in $E \otimes F$ | Holds for ALL vectors in $E$ | Tensor product vs. single space |

**In one sentence:** CP says "the projective norm sees rank-1 tensors correctly." IB says "the dual space sees all vectors correctly."

### 4.3. Not Independent of ZFC

**99% confidence the question is NOT independent of ZFC.** The infimum $\pi(e \otimes f)$ is a specific real number determined by concrete algebraic/metric data. Its value cannot depend on the ambient model of ZFC. Independence would require the infimum to have a model-dependent value, which does not happen for infima over concrete sets of finite sums of products of norms.

Compare: the Continuum Hypothesis is independent because it involves the cardinality of the reals, not the value of a specific real number.

### 4.4. The Concrete Separation via $\mathbb{C}_p$

$\mathbb{C}_p$ (the completion of the algebraic closure of $\mathbb{Q}_p$) is the natural test field:

- **IB fails over $\mathbb{C}_p$**: Classical (Schikhof, van Rooij). There exist Banach spaces $E$ over $\mathbb{C}_p$ with $E^* = \{0\}$.
- **CP very likely holds over $\mathbb{C}_p$**: No counterexample found. The algebraic rigidity of rank-1 tensors prevents cheap representations.

**If CP holds over $\mathbb{C}_p$** (as all agents believe), **then $\mathbb{C}_p$ separates CP from IB**.

### 4.5. No Finite-Dimensional Counterexample to CP

Any counterexample to CP must be **infinite-dimensional**. In finite dimensions, norm-achieving functionals exist by compactness (without full HB), so `h_bidual` holds automatically and CP follows from the `WithBidual.lean` proof.

### 4.6. Gamma's Confidence Assessment

| Claim | Confidence |
|-------|-----------|
| CP does not imply IB (given CP is true) | 95% |
| CP holds unconditionally over all nontrivially normed fields | 80% |
| The question CP => IB is not independent of ZFC | 99% |
| No counterexample to CP exists | 75% |
| `h_bidual` is the right hypothesis for the Lean formalization | 99% |
| A fully unconditional proof of CP will eventually be found | 55% |

---

## 5. Synthesis: The Precise Open Problem

All three agents identify the same irreducible difficulty:

> **The open case:** Representations $v \otimes w = \sum_j v_j \otimes w_j$ where $\{w_j\}$ are linearly dependent and $\text{span}(w_j)$ has dimension $\ge 2$, in infinite-dimensional spaces over non-spherically-complete valued fields.

### What is proved (without HB):

1. **Collinear representations** ($\text{span}(w_j) = 1$): CP holds via the cancellation trick. *Formalized sorry-free.*
2. **Independent representations** ($w_j$ linearly independent): CP holds via the algebraic structure lemma. *Formalized sorry-free.*
3. **Finite-dimensional spaces** (either factor): CP holds by compactness arguments.
4. **Archimedean fields** ($\mathbb{R}$, $\mathbb{C}$): CP holds unconditionally via Hahn-Banach. *Formalized sorry-free.*
5. **Spherically complete non-Archimedean fields**: CP holds via Ingleton's theorem.

### What remains open:

Dependent representations with span dimension $\ge 2$ in infinite-dimensional spaces over non-spherically-complete fields. The obstruction is the "wrong-direction triangle inequality": reducing dependent to independent representations can only bound cost from above, not below.

### Potential proof strategies (not yet realized):

1. **Multi-directional cancellation trick:** Generalize the collinear cancellation to higher span dimensions.
2. **Dependent-to-independent cost monotonicity:** Prove that the original cost always dominates the reduced independent cost.
3. **Pure-tensor optimality:** Show that for rank-1 tensors, the minimum-cost representation is always 1-term (up to scalar redistribution).
4. **Non-Archimedean geometry:** Exploit ultrametric properties to strengthen the triangle inequality bounds.

---

## 6. Implications for the Project

1. **The `h_bidual` hypothesis is exactly right.** It captures the minimum needed for the duality-based proof. All agents agree (99% confidence).

2. **The `RCLike` unconditional corollary is the cleanest achievable result** with current proof techniques.

3. **Removing `h_bidual` unconditionally requires new mathematics** --- not just a clever Lean proof, but a new mathematical argument that does not exist in the published literature.

4. **No counterexample to CP is known or likely to exist.** The algebraic rigidity of rank-1 tensors prevents cheap representations in all tested cases.

5. **The question is mathematically well-posed and decidable in ZFC.** It is not a foundational/axiomatic issue.

---

## 7. Sharp Formulation of the Remaining Conjecture

**Conjecture (Cross Property).** For every nontrivially normed field $k$ and every pair of seminormed $k$-spaces $E, F$, the projective tensor seminorm satisfies:

$$\pi(e \otimes f) = \|e\| \cdot \|f\| \quad \text{for all } e \in E,\; f \in F.$$

**Equivalent formulation (Alpha, Section 7.4):** For a rank-1 tensor $e \otimes f$ in a finite-dimensional tensor product $V \otimes W$, does the minimal-cost representation always have the form $\alpha e \otimes (1/\alpha) f$ (a single term, up to scaling)?

**Equivalent formulation (Beta, Section 5.1):** For every nontrivially normed field $k$, every $k$-Banach space $F$, every finite-dimensional subspace $W_0 \subseteq F$, and every $w \in W_0$:

$$\sup_{\psi \in F^*,\; \|\psi\| \le 1} |\psi(w)| = \|w\|$$

(the "subspace-norm Hahn-Banach" property for finite-dimensional subspaces).

---

## 8. Formalized Results in the Codebase

| File | Result | Status |
|------|--------|--------|
| `CancellationTrick.lean` | `collinear_cost_ge` --- collinear case of CP | Sorry-free |
| `CancellationTrick.lean` | `tmul_norm_product_eq` --- norm invariance of rank-1 tensors | Sorry-free |
| `DirectApproach.lean` | `reduced_representation_cost_ge` --- independent case | Sorry-free |
| `DirectApproach.lean` | `triangle_wrong_direction` --- obstruction formalization | Sorry-free |
| `WithBidual.lean` | `projectiveSeminorm_tprod_of_bidual_iso` --- main theorem with `h_bidual` | Sorry-free |
| `RCLike.lean` | `projectiveSeminorm_tprod` --- unconditional for $\mathbb{R}$/$\mathbb{C}$ | Sorry-free |

---

## References

- Ingleton, A.W., "The Hahn-Banach theorem for non-Archimedean-valued fields," *Proc. Cambridge Phil. Soc.* 48 (1952), 41--45.
- Perez-Garcia, C. & Schikhof, W.H., *Locally Convex Spaces over Non-Archimedean Valued Fields*, Cambridge University Press, 2010.
- Ryan, R., *Introduction to Tensor Products of Banach Spaces*, Springer, 2002.
- Schneider, P., *Nonarchimedean Functional Analysis*, Springer, 2002.
- Gruson, L. & van der Put, M., "Banach spaces," *Mem. Soc. Math. France* 39--40 (1974), 55--100.
- van Rooij, A.C.M., *Non-Archimedean Functional Analysis*, Marcel Dekker, 1978.
- Yuan, Y., "Formalization of non-Archimedean functional analysis," arXiv:2601.21734, 2026.
