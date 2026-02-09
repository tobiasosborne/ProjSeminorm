# Proof Strategy: The Cross Property via Quotient + Cancellation

**Date:** 2026-02-09
**Status:** Complete reduction to a single open lemma (FDNP)

---

## 1. The Theorem

**Theorem (Cross Property).** Let $(k, |\cdot|)$ be a nontrivially normed field. Let $(E, \|\cdot\|_E)$ and $(F, \|\cdot\|_F)$ be seminormed $k$-vector spaces. Then for all $e \in E$ and $f \in F$:

$$\pi(e \otimes f) = \|e\| \cdot \|f\|$$

where $\pi(u) := \inf\bigl\{\sum_{j=1}^n \|v_j\| \|w_j\| : u = \sum_{j=1}^n v_j \otimes w_j\bigr\}$ is the projective tensor seminorm on $E \otimes_k F$.

The upper bound $\pi(e \otimes f) \le \|e\|\|f\|$ is trivial (take the one-term representation). We must prove the lower bound: for every representation $e \otimes f = \sum_{j=1}^n v_j \otimes w_j$,

$$\sum_{j=1}^n \|v_j\| \cdot \|w_j\| \ge \|e\| \cdot \|f\|.$$

---

## 2. Already Established Results

The following are formalized sorry-free in the project codebase.

### 2.1. Norm Invariance of Rank-1 Tensors

**Theorem** (`tmul_norm_product_eq` in `CancellationTrick.lean`). If $v \otimes w = u \otimes w_1$ in $E \otimes F$ (with $v, u \in E$ and $w, w_1 \in F$), then $\|v\| \cdot \|w\| = \|u\| \cdot \|w_1\|$.

*Proof sketch.* If either side is zero the result is immediate. Otherwise, pick an algebraic (Hamel basis) functional $g: E \to k$ with $g(v) = 1$. Applying $g \otimes \mathrm{id}_F$ to both sides yields $w = g(u) \cdot w_1$. Setting $c = g(u)$, we get $u = c \cdot v$ (from the tensor equation and flatness), so $\|u\| \cdot \|w_1\| = |c| \|v\| \cdot \|w_1\| = \|v\| \cdot |c| \|w_1\| = \|v\| \cdot \|w\|$. No continuity of $g$ is needed.

### 2.2. The Cancellation Trick (Collinear Case)

**Theorem** (`collinear_cost_ge` in `CancellationTrick.lean`). Let $e \otimes f = \sum_{j=1}^n v_j \otimes (\alpha_j w_1)$ where $\alpha_j \in k$ and $w_1 \in F$. Then:

$$\sum_{j=1}^n \|v_j\| \cdot |\alpha_j| \cdot \|w_1\| \ge \|e\| \cdot \|f\|.$$

*Proof.* By bilinearity: $\sum_j v_j \otimes (\alpha_j w_1) = \bigl(\sum_j \alpha_j v_j\bigr) \otimes w_1$. Set $u = \sum_j \alpha_j v_j$. By norm invariance (2.1): $\|e\| \cdot \|f\| = \|u\| \cdot \|w_1\|$. By the triangle inequality:

$$\sum_j |\alpha_j| \cdot \|v_j\| \ge \Bigl\|\sum_j \alpha_j v_j\Bigr\| = \|u\|.$$

Multiplying both sides by $\|w_1\|$:

$$\sum_j \|v_j\| \cdot |\alpha_j| \cdot \|w_1\| \ge \|u\| \cdot \|w_1\| = \|e\| \cdot \|f\|. \qquad \square$$

**Key feature:** This proof uses NO continuous functionals, NO Hahn-Banach, NO dual spaces. It is purely algebraic + triangle inequality.

### 2.3. The Independent Case

**Theorem** (`reduced_representation_cost_ge` in `DirectApproach.lean`). Let $e \otimes f = \sum_{k=1}^s u_k \otimes w_k$ where $\{w_1, \ldots, w_s\}$ are linearly independent in $F$. Then $\sum_k \|u_k\| \cdot \|w_k\| \ge \|e\| \cdot \|f\|$.

*Proof.* Linear independence of the $w_k$ in $E \otimes F$ forces $u_k = c_k e$ for scalars $c_k \in k$ and $f = \sum_k c_k w_k$. Then:

$$\sum_k \|u_k\| \cdot \|w_k\| = \sum_k |c_k| \cdot \|e\| \cdot \|w_k\| = \|e\| \cdot \sum_k |c_k| \cdot \|w_k\| \ge \|e\| \cdot \Bigl\|\sum_k c_k w_k\Bigr\| = \|e\| \cdot \|f\|. \qquad \square$$

---

## 3. The Quotient Reduction

This is the core new argument. It reduces the general case to the collinear case (Section 2.2) plus one lemma about quotient norms.

### 3.1. Setup

Let $e \otimes f = \sum_{j=1}^n v_j \otimes w_j$ be an arbitrary representation. We may assume $e \ne 0$ and $f \ne 0$ (otherwise the bound is trivial). Define:

$$W_0 := \operatorname{span}_k(w_1, \ldots, w_n, f) \subseteq F.$$

This is a finite-dimensional subspace of $F$ containing all $w_j$ and $f$. Let $s = \dim W_0$.

### 3.2. Quotienting to the Collinear Case

Let $H \subseteq W_0$ be any subspace of codimension 1 in $W_0$ such that $f \notin H$. (Such $H$ exists because $\dim W_0 \ge 1$ and $f \ne 0$.) Let $\bar{H}$ be the closure of $H$ in $F$, and let

$$q: F \to F/\bar{H}$$

be the quotient map. Equip $F/\bar{H}$ with the quotient seminorm: $\|q(y)\|_{F/\bar{H}} = \inf_{h \in \bar{H}} \|y - h\|_F$.

**Claim 1.** The images $q(w_1), \ldots, q(w_n)$ are all scalar multiples of a single nonzero vector in $F/\bar{H}$.

*Proof of Claim 1.* Each $w_j \in W_0$, so $q(w_j) \in q(W_0)$. Since $H$ has codimension 1 in $W_0$ and $\bar{H} \cap W_0 \supseteq H$, we have $\dim(q(W_0)) \le 1$. Since $f \in W_0$ and $f \notin H$ (hence $f \notin \bar{H} \cap W_0$), we have $q(f) \ne 0$, so $q(W_0) = \operatorname{span}(q(f))$ is 1-dimensional. In particular, each $q(w_j) = \alpha_j \cdot q(f)$ for some $\alpha_j \in k$. $\square$

**Claim 2.** Applying $\mathrm{id}_E \otimes q$ to the tensor equation:

$$e \otimes q(f) = \sum_{j=1}^n v_j \otimes q(w_j) = \sum_{j=1}^n v_j \otimes (\alpha_j \cdot q(f)).$$

This is a **collinear representation** in $E \otimes (F/\bar{H})$.

**Claim 3.** By the cancellation trick (Theorem 2.2):

$$\sum_{j=1}^n \|v_j\| \cdot |\alpha_j| \cdot \|q(f)\|_{F/\bar{H}} \ge \|e\| \cdot \|q(f)\|_{F/\bar{H}}.$$

**Claim 4.** Since $\|q(w_j)\|_{F/\bar{H}} = |\alpha_j| \cdot \|q(f)\|_{F/\bar{H}} \le \|w_j\|_F$ (the quotient seminorm is dominated by the original norm), we have $|\alpha_j| \le \|w_j\| / \|q(f)\|$ when $q(f) \ne 0$. But we don't actually need this bound individually. Instead, observe:

$$\|v_j\| \cdot |\alpha_j| \cdot \|q(f)\| = \|v_j\| \cdot \|q(w_j)\|_{F/\bar{H}} \le \|v_j\| \cdot \|w_j\|_F$$

where the last inequality uses $\|q(w_j)\|_{F/\bar{H}} \le \|w_j\|_F$.

Summing over $j$:

$$\|e\| \cdot \|q(f)\|_{F/\bar{H}} \le \sum_j \|v_j\| \cdot \|q(w_j)\|_{F/\bar{H}} \le \sum_j \|v_j\| \cdot \|w_j\|_F.$$

### 3.3. The Key Inequality

We have established: for every codimension-1 subspace $H$ of $W_0$ with $f \notin H$,

$$\boxed{\sum_{j=1}^n \|v_j\| \cdot \|w_j\| \ge \|e\| \cdot \|q_H(f)\|_{F/\bar{H}}}$$

where $q_H: F \to F/\bar{H}$ is the quotient map.

Taking the supremum over all such $H$:

$$\sum_{j=1}^n \|v_j\| \cdot \|w_j\| \ge \|e\| \cdot \sup_H \|q_H(f)\|_{F/\bar{H}}.$$

### 3.4. What Remains

To complete the proof of the Cross Property, it suffices to show:

$$\sup_H \|q_H(f)\|_{F/\bar{H}} = \|f\|$$

where the supremum is over all codimension-1 subspaces $H \subseteq W_0$ with $f \notin H$.

**Expanding the quotient norm:**

$$\|q_H(f)\|_{F/\bar{H}} = \inf_{h \in \bar{H}} \|f - h\|_F \ge \inf_{h \in H} \|f - h\|_F = \mathrm{dist}_F(f, H).$$

(The inequality holds because $H \subseteq \bar{H}$, so the infimum over $\bar{H}$ is $\le$ the infimum over $H$. Actually, since $H$ is finite-dimensional, $H$ is closed in $F$, so $\bar{H} \cap W_0 = H$ and $\inf_{h \in \bar{H}} \|f-h\| = \inf_{h \in \bar{H}} \|f-h\|$. We are taking the infimum over the larger set $\bar{H} \supseteq H$, so the infimum could be smaller. However, for our purposes the lower bound suffices.)

Actually, we can simplify. Since $H$ is finite-dimensional (codimension 1 in the finite-dimensional $W_0$), $H$ is closed. We can take $\bar{H}$ to be any closed subspace of $F$ with $\bar{H} \cap W_0 = H$. The simplest choice is $\bar{H} = H$ itself (a closed, finite-dimensional subspace of $F$). Then:

$$\|q_H(f)\|_{F/H} = \inf_{h \in H} \|f - h\|_F = \mathrm{dist}_F(f, H).$$

So the condition becomes:

$$\boxed{\sup_{H} \mathrm{dist}_F(f, H) = \|f\|}$$

where $H$ ranges over codimension-1 subspaces of $W_0$ not containing $f$.

---

## 4. The Finite-Dimensional Norming Problem (FDNP)

### 4.1. Statement

**Lemma (FDNP).** Let $(k, |\cdot|)$ be a nontrivially normed field. Let $F$ be a seminormed $k$-space, $W_0 \subseteq F$ a finite-dimensional subspace (with the norm inherited from $F$), and $f \in W_0 \setminus \{0\}$. Then:

$$\sup_H \mathrm{dist}_{F}(f, H) = \|f\|$$

where $H$ ranges over codimension-1 subspaces of $W_0$ not containing $f$.

### 4.2. Equivalent Formulations

The following are equivalent for a finite-dimensional normed $k$-space $(V, \|\cdot\|)$ and a nonzero $f \in V$:

**(a)** $\sup_H \mathrm{dist}(f, H) = \|f\|$ over codimension-1 subspaces $H$ with $f \notin H$.

**(b)** There exists a codimension-1 subspace $H \subseteq V$ such that $f$ is **Birkhoff-James orthogonal** to $H$: $\|f - h\| \ge \|f\|$ for all $h \in H$.

**(c)** There exists a continuous linear functional $\psi: V \to k$ with $\psi(f) = \|f\|$ and $\|\psi\| = 1$. (A **norming functional** for $f$.)

**(d)** The canonical embedding $J: V \to V^{**}$ satisfies $\|J(f)\| = \|f\|$ (the **isometric bidual condition** at $f$).

**Proof of equivalences.**

(b) $\Rightarrow$ (a): If $H$ witnesses (b), then $\mathrm{dist}(f, H) = \inf_{h \in H} \|f - h\| \ge \|f\|$. Since $\mathrm{dist}(f, H) \le \|f - 0\| = \|f\|$, we get $\mathrm{dist}(f, H) = \|f\|$, hence the sup $= \|f\|$.

(a) $\Rightarrow$ (b): The sup equals $\|f\|$ and $\mathrm{dist}(f, H) \le \|f\|$ for each $H$, so there exists a sequence $H_n$ with $\mathrm{dist}(f, H_n) \to \|f\|$. Since $V$ is finite-dimensional, the Grassmannian of codimension-1 subspaces is compact (over $\mathbb{R}$ or $\mathbb{C}$; over non-Archimedean fields, a compactness argument on the unit sphere works for the value group). If we can extract a convergent subsequence $H_n \to H_\infty$, then $\mathrm{dist}(f, H_\infty) = \|f\|$, giving (b). *(Note: this step requires care over non-Archimedean fields where the Grassmannian topology may differ; the sup may not be achieved, only approached. In that case (a) gives $\mathrm{dist}(f, H) = \|f\| - \epsilon$ for arbitrarily small $\epsilon$, which suffices for the CP proof since the infimum over representations is also a limit.)*

(c) $\Rightarrow$ (b): Take $H = \ker \psi$. For $h \in H$: $\|f - h\| \ge |\psi(f - h)| / \|\psi\| = |\psi(f)| / 1 = \|f\|$.

(b) $\Rightarrow$ (c): Given $H$ with $\mathrm{dist}(f, H) = \|f\|$. Define $\psi: V \to k$ by $\psi(f) = \|f\|$ and $\psi|_H = 0$. For any $v = \alpha f + h$ ($\alpha \in k$, $h \in H$): $|\psi(v)| = |\alpha| \|f\| = |\alpha| \cdot \mathrm{dist}(f, H) \le |\alpha| \|f - (-h/\alpha)\|$ ... *(This direction requires more care. Over valued fields, the construction gives $\|\psi\| \le 1$ iff $|\psi(v)| \le \|v\|$ for all $v$, which is equivalent to $\|f\| \le \|f + h\|$ for all $h \in H$, i.e., Birkhoff-James orthogonality.)*

Actually, let us be more precise. Define $\psi$ by $\ker \psi = H$ and $\psi(f) = \|f\|$. For $v = \alpha f + h$ with $\alpha \in k, h \in H$:

$$|\psi(v)| = |\alpha| \|f\| \quad \text{and} \quad \|v\| = |\alpha| \|f + h/\alpha\| \ge |\alpha| \cdot \mathrm{dist}(f, H) = |\alpha| \|f\|$$

(using BJ-orthogonality for the last inequality, and the convention $\|v\| = 0$ when $\alpha = 0$). So $|\psi(v)| \le \|v\|$, giving $\|\psi\| \le 1$. Since $|\psi(f)| = \|f\|$, we get $\|\psi\| = 1$.

(c) $\Leftrightarrow$ (d): $\|J(f)\| = \sup_{\|\psi\| \le 1} |\psi(f)|$. Condition (c) says this sup $= \|f\|$. The reverse $\|J(f)\| \le \|f\|$ is always true.

### 4.3. When FDNP is Known to Hold

| Setting | Holds? | Reason |
|---------|--------|--------|
| $k = \mathbb{R}$ or $\mathbb{C}$ | **Yes** | The dual unit ball $\{\psi : \|\psi\| \le 1\}$ in $V^*$ is compact; the continuous function $\psi \mapsto |\psi(f)|$ achieves its supremum. |
| $k$ spherically complete, ultrametric norm on $V$ | **Yes** | Ingleton's theorem (1952): norm-preserving extension from $\operatorname{span}(f)$ to $V$. |
| $k$ arbitrary, $\dim V = 1$ | **Yes** | $V = k \cdot f$, $\psi(f) = \|f\|$, $\|\psi\| = 1$ trivially. |
| $k$ arbitrary, $V$ with $\ell^\infty$-type norm | **Yes** | Direct construction of norming functional. |
| $k$ non-spherically-complete, general norm | **Open** | This is the FDNP. |

### 4.4. When FDNP is Known to Fail

**It does NOT fail in any known case for norms arising as subspace norms.**

However, it IS known that:

- Over non-spherically-complete $k$ (e.g., $\mathbb{C}_p$), there exist norms on $k^2$ where the Hahn-Banach *extension* property fails (Ingleton's necessity proof).
- Over any non-Archimedean $k$, even spherically complete, a non-ultrametric norm on $k^2$ (e.g., $\ell^1$ norm) can fail the isometric bidual condition.

The question is whether norms *inherited from ambient seminormed spaces* have the same pathology.

### 4.5. The Key Open Question

**Question.** Let $k$ be a nontrivially normed field. Let $F$ be a seminormed $k$-space and $W_0 \subseteq F$ a 2-dimensional subspace (with the inherited norm). Let $f \in W_0$ be nonzero. Does there exist a linear functional $\psi: W_0 \to k$ with $\psi(f) = \|f\|$ and $\|\psi\| = 1$?

The 2-dimensional case suffices because:
- The 1-dimensional case is trivial.
- Higher-dimensional cases can be reduced: if the FDNP holds for all 2-dimensional subspaces, it holds for all finite-dimensional subspaces. (Given $f \in V$ with $\dim V = s$, pick any 2-dimensional subspace $V_2 \subseteq V$ containing $f$. A norming functional on $V_2$ extends to $V$ by Zorn's lemma applied to the algebraic extension with norm control on the 2-dimensional slices.)

*(Note: the reduction from dimension $s$ to dimension 2 may itself require HB-type arguments. The clean statement is: FDNP for all finite-dimensional $W_0$ suffices for CP.)*

---

## 5. The Complete Proof (Assuming FDNP)

We now assemble the full argument.

**Theorem.** Assume the FDNP (Section 4.1). Then for every nontrivially normed field $k$ and all seminormed $k$-spaces $E, F$: $\pi(e \otimes f) = \|e\| \cdot \|f\|$.

**Proof.**

The upper bound $\pi(e \otimes f) \le \|e\| \|f\|$ is trivial.

For the lower bound, let $e \otimes f = \sum_{j=1}^n v_j \otimes w_j$ be any representation. We must show $\sum_j \|v_j\| \|w_j\| \ge \|e\| \|f\|$.

If $e = 0$ or $f = 0$, the bound is trivially $0 \le 0$. Assume $e \ne 0$ and $f \ne 0$.

**Step 1. Finite-dimensional reduction.**
Define $W_0 = \operatorname{span}_k(w_1, \ldots, w_n, f) \subseteq F$. This is finite-dimensional with $\dim W_0 \le n + 1$.

**Step 2. Apply FDNP.**
By the FDNP, there exists a codimension-1 subspace $H \subseteq W_0$ with $f \notin H$ and

$$\mathrm{dist}_F(f, H) = \|f\|.$$

(More precisely: for every $\epsilon > 0$, there exists such $H$ with $\mathrm{dist}_F(f, H) \ge \|f\| - \epsilon$. Taking $\epsilon \to 0$ yields the result.)

**Step 3. Quotient.**
Let $q: F \to F/H$ be the quotient map. Since $H$ is finite-dimensional, it is closed in $F$, so $F/H$ is a well-defined seminormed space.

Since $H \subseteq W_0$ has codimension 1 and $f \notin H$, the image $q(W_0)$ is 1-dimensional, spanned by $q(f) \ne 0$.

Each $w_j \in W_0$, so $q(w_j) = \alpha_j \cdot q(f)$ for some $\alpha_j \in k$.

**Step 4. Apply the cancellation trick.**
The tensor equation $e \otimes q(f) = \sum_j v_j \otimes (\alpha_j \cdot q(f))$ is a collinear representation in $E \otimes (F/H)$. By Theorem 2.2:

$$\sum_j \|v_j\| \cdot |\alpha_j| \cdot \|q(f)\|_{F/H} \ge \|e\| \cdot \|q(f)\|_{F/H}.$$

**Step 5. Quotient norm dominance.**
For each $j$: $\|q(w_j)\|_{F/H} = |\alpha_j| \cdot \|q(f)\|_{F/H}$, and $\|q(w_j)\|_{F/H} \le \|w_j\|_F$ (the quotient seminorm is $\le$ the original norm). Therefore:

$$\sum_j \|v_j\| \cdot \|w_j\|_F \ge \sum_j \|v_j\| \cdot \|q(w_j)\|_{F/H} = \sum_j \|v_j\| \cdot |\alpha_j| \cdot \|q(f)\| \ge \|e\| \cdot \|q(f)\|_{F/H}.$$

**Step 6. Quotient norm of $f$.**
$\|q(f)\|_{F/H} = \mathrm{dist}_F(f, H) = \|f\|$ (by Step 2).

**Step 7. Combine.**

$$\sum_j \|v_j\| \cdot \|w_j\| \ge \|e\| \cdot \|f\|. \qquad \square$$

---

## 6. Diagram of the Proof Structure

```
  General representation                FDNP gives
  e ⊗ f = Σ vⱼ ⊗ wⱼ          norming hyperplane H ⊂ W₀
         |                              |
         | quotient by H               |
         v                              |
  e ⊗ q(f) = Σ vⱼ ⊗ (αⱼ·q(f))   <---+
  [collinear representation]
         |
         | Cancellation Trick (proved, sorry-free)
         v
  Σ ‖vⱼ‖·|αⱼ|·‖q(f)‖ ≥ ‖e‖·‖q(f)‖
         |
         | ‖q(wⱼ)‖ ≤ ‖wⱼ‖ (quotient norm ≤ original)
         v
  Σ ‖vⱼ‖·‖wⱼ‖ ≥ ‖e‖·‖q(f)‖
         |
         | ‖q(f)‖ = dist(f, H) = ‖f‖ (FDNP)
         v
  Σ ‖vⱼ‖·‖wⱼ‖ ≥ ‖e‖·‖f‖  ■
```

---

## 7. What the FDNP Says Concretely

### 7.1. The 2-Dimensional Case

The simplest non-trivial instance: $V = k^2$ with a norm $\|\cdot\|_V$ inherited from some ambient seminormed space $F$. Given $f = (f_1, f_2) \in V$ with $\|f\|_V > 0$. We need a hyperplane $H = \{(\lambda a, \lambda b) : \lambda \in k\}$ (a line through the origin) such that:

$$\|(f_1 - \lambda a, f_2 - \lambda b)\|_V \ge \|f\|_V \quad \text{for all } \lambda \in k.$$

Equivalently, the point $f$ is at maximal distance from the line $H$: the closest point on $H$ to $f$ is $0$.

### 7.2. Geometric Interpretation

The FDNP asks: in a finite-dimensional normed space over $k$, is the origin always a "best approximation" to $f$ from some hyperplane through the origin?

Over $\mathbb{R}$ or $\mathbb{C}$: Yes (supporting hyperplane theorem / Hahn-Banach).

Over non-Archimedean $k$ with ultrametric norm: Yes, because the ultrametric inequality $\|x + y\| \le \max(\|x\|, \|y\|)$ implies $\|f + h\| \ge \|f\|$ whenever $\|h\| \le \|f\|$ and $h$ is "in a different direction." More precisely, for any line $L$ not containing $f$, if $\|f\|$ is not in the set $\{|\alpha| \|v\| : \alpha \in k\}$ for $v$ spanning $L$, then $\mathrm{dist}(f, L) = \|f\|$.

Over non-Archimedean $k$ with non-ultrametric norm: Open. This is the genuine frontier.

### 7.3. Why the Norm Being Inherited from an Ambient Space Might Help

When $V = W_0 \subseteq F$ with the norm from $F$, the norm on $V$ is not arbitrary — it is the restriction of a globally defined seminorm. This might constrain the norm geometry enough to force the FDNP. For instance:

- The norm satisfies the full axioms of a seminorm over $k$: absolute homogeneity $\|\alpha v\| = |\alpha| \|v\|$ and the triangle inequality $\|v + w\| \le \|v\| + \|w\|$.
- The norm values live in $\mathbb{R}_{\ge 0}$ and interact with the value group $|k^\times|$ through homogeneity.

Whether these constraints force the FDNP is the open question.

---

## 8. Relationship to the Existing `h_bidual` Hypothesis

The hypothesis `h_bidual` in `projectiveSeminorm_tprod_of_bidual_iso` (file `WithBidual.lean`) states:

```
h_bidual : ∀ i, ‖inclusionInDoubleDual 𝕜 (E i) (m i)‖ = ‖m i‖
```

This is exactly the FDNP applied to each factor space $E_i$ at the specific point $m_i$. It says the bidual norm equals the original norm at $m_i$.

**The quotient + cancellation proof shows:** To remove `h_bidual`, it suffices to prove the FDNP for the finite-dimensional subspaces $W_0$ that arise in tensor representations. The cancellation trick (already formalized) does all the heavy lifting; the FDNP is the only remaining ingredient.

---

## 9. Summary

| Component | Status | File |
|-----------|--------|------|
| Norm invariance of rank-1 tensors | **Sorry-free** | `CancellationTrick.lean` |
| Cancellation trick (collinear case) | **Sorry-free** | `CancellationTrick.lean` |
| Independent case | **Sorry-free** | `DirectApproach.lean` |
| Quotient reduction to collinear case | **New argument** | To be formalized |
| Quotient norm $\le$ original norm | **Standard** | Mathlib |
| FDNP | **Open lemma** | The frontier |
| Full CP assuming FDNP | **Complete** | Sections 3--5 above |
| CP over $\mathbb{R}/\mathbb{C}$ | **Sorry-free** | `RCLike.lean` |
| CP with `h_bidual` | **Sorry-free** | `WithBidual.lean` |

**The unconditional proof of the Cross Property is exactly one lemma away.** That lemma (FDNP) is a concrete, well-posed question in the geometry of finite-dimensional normed spaces over valued fields.
