---
title: A chain of lifts as a plain sum
lean:
  - New/UpperBound/Objects/LiftChains.lean
  - New/UpperBound/Objects/Columns.lean
  - New/UpperBound/Divisibility/ChainValuation.lean
decls:
  - New.classPoints
  - New.kernelProduct
  - New.kernelProduct_succ
  - New.sum_classPoints_succ
  - New.IsJointlyInvariant.sum_chain_eq_sum_kernelProduct
  - New.kernelProduct_induction
  - New.apply_kernelProduct_le_prod_mul
  - New.Data.chainCombination
  - New.Data.chainCombination_eq_sum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A chain of lifts as a plain sum

A theta lift is an integral over a finite set of double cosets, with weights $1/\#\mathrm{Aut}$. The weights are denominators, and a denominator can destroy a $p$-adic bound. This section proves that, for a jointly invariant combination of chains at free levels, all these weights are $1$. The value of the combination is then a plain sum, over tuples of double cosets, of products of kernels. Section 6 bounds each product by the gauge, and the ultrametric inequality bounds the sum.

[Chains of lifts and free levels](/chapter/upper-bound-objects/#chains-of-lifts-and-free-levels) proves a form of this result with the values in a set $A$ (`New.IsJointlyInvariant.sum_chain_mem_nsmul`). Here we need the identity itself, so we state and prove it.

### The setting

Fix a CM field $E$ and a tower of finite adelic unitary groups $G_j = \mathrm{U}(n_j)(\mathbb A_f)$, $j \in \mathbb N$, of the standard definite spaces. Let $\Gamma_j$ be the rational points of $G_j$ and $K_j$ a level of $G_j$. For each $j$, let $k_j$ be a theta kernel from stage $j$ to stage $j+1$ with data $S_j$, in the sense of [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). So $k_j$ has an action $\omega$ of $G_j \times G_{j+1}$ on $S_j$, and a jet map that sends $\Phi \in S_j$ to a linear map $J(\Phi)$ from the Weyl module $V_j$ of stage $j$ to $V_{j+1}$. The lift of a form $\varphi$ of stage $j$ with datum $\Phi$ is

$$(k_j.\mathrm{lift}\,\Phi\,\varphi)(h) = \int_{\Gamma_j \backslash G_j} J\big(\omega(g, h)\Phi\big)\,\varphi(g)\,dg,$$

where the integral is the class integral for the measure with $\mathrm{vol}(K_j) = 1$ ([Definition](/decl/New.Kernel.lift/)). If $K_j$ fixes the integrand under right translation, this integral equals the class sum

$$\sum_{c \in \Gamma_j \backslash G_j / K_j} \frac{F(g_c)}{\#(\Gamma_j \cap g_c K_j g_c^{-1})},$$

with chosen representatives $g_c$ ([Definition](/decl/New.classSum/), `New.classIntegral_eq_classSum`). The level $K_j$ is *free* if all the groups $\Gamma_j \cap g K_j g^{-1}$ are trivial. At a free level all the weights in the class sum are $1$.

The chain $\mathrm{chain}(\Phi)_m$ is the composite of the first $m$ lifts, with data $\Phi_0, \dots, \Phi_{m-1}$ ([Definition](/decl/New.chain/)). A family $(L_x, \Phi_x)_{x \in s}$, with $L_x : V_m \to M$ linear, is jointly invariant at stage $m$ if the tensor $\sum_x L_x \otimes \Phi_{x, m-1} \otimes \dots \otimes \Phi_{x,0}$ does not change when $a_j \in K_j$ moves each $\Phi_{x,j}$ by $\omega(a_j, a_{j+1})$, with $a_j = 1$ for $j \ge m$ ([Definition](/decl/New.IsJointlyInvariant/)). Here the test is made through every linear map $\beta$ from the tensor product to $V_m$.

### Kernel products

**Definition (Class points).** Let $c = (c_j)_{j < m}$ be a tuple of double cosets $c_j \in \Gamma_j \backslash G_j / K_j$, and let $g = (g_j)_{j \in \mathbb N}$ be points. The class points of $c$ and $g$ are the chosen representative of $c_j$ for $j < m$, and $g_j$ for $j \ge m$.

Lean: `New.classPoints` (New/UpperBound/Objects/LiftChains.lean).

**Definition (Kernel product).** For data $\Phi = (\Phi_j)$, a form $\varphi$ of stage $0$, points $g = (g_j)$ and $m \in \mathbb N$, the kernel product is

$$\mathrm{KP}(\Phi, \varphi, g, m) = J\big(\omega(g_{m-1}, g_m)\Phi_{m-1}\big) \circ \dots \circ J\big(\omega(g_0, g_1)\Phi_0\big)\,\varphi(g_0) \in V_m.$$

Lean: `New.kernelProduct` (New/UpperBound/Objects/LiftChains.lean).

**Lemma.** $\mathrm{KP}(\Phi, \varphi, g, m+1) = J(\omega(g_m, g_{m+1})\Phi_m)\,\mathrm{KP}(\Phi, \varphi, g, m)$.

Lean: `New.kernelProduct_succ` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* This is the definition of the composite of $m+1$ maps. $\square$

**Lemma.** For every function $F$ of tuples of points, and every $g$,

$$\sum_{c \in \prod_{j \le m} \Gamma_j\backslash G_j/K_j} F(\mathrm{cp}(c, g)) = \sum_{r \in \Gamma_m\backslash G_m/K_m}\; \sum_{c \in \prod_{j < m} \Gamma_j\backslash G_j/K_j} F\big(\mathrm{cp}(c, g[m \mapsto g_r])\big),$$

where $\mathrm{cp}$ is the class points and $g[m \mapsto g_r]$ is $g$ with the point $g_m$ replaced by the representative $g_r$ of $r$.

Lean: `New.sum_classPoints_succ` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* A tuple of $m+1$ classes is a tuple $c$ of $m$ classes followed by a last class $r$. The class points of the long tuple are those of $c$ below $m$, the point $g_r$ at $m$ and $g_j$ above $m$. These are the class points of $c$ and $g[m \mapsto g_r]$. $\square$

### The plain sum

**Theorem (A chain of lifts is a plain sum).** Let the family $(L_x, \Phi_x)_{x \in s}$ be jointly invariant at stage $m$. Let the levels $K_j$, $j < m$, be free. Let $\varphi$ be a form of stage $0$ fixed by $K_0$. Then for all points $g$,

$$\sum_{x \in s} L_x\big((\mathrm{chain}(\Phi_x)_m\,\varphi)(g_m)\big) = \sum_{c \in \prod_{j<m}\Gamma_j\backslash G_j/K_j}\; \sum_{x \in s} L_x\big(\mathrm{KP}(\Phi_x, \varphi, \mathrm{cp}(c, g), m)\big).$$

Lean: `New.IsJointlyInvariant.sum_chain_eq_sum_kernelProduct` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* We use induction on $m$, for all $g$ and all families $L$ at once.

For $m = 0$, the chain is the identity, there is one empty tuple $c$, the class points are $g$, and the kernel product is $\varphi(g_0)$. Both sides are $\sum_x L_x(\varphi(g_0))$.

Let the claim hold for $j$, and take $m = j + 1$. For $a \in G_j$ put

$$I_x(a) = J\big(\omega(a, g_{j+1})\Phi_{x,j}\big)\,\big(\mathrm{chain}(\Phi_x)_j\,\varphi\big)(a), \qquad F(a) = \sum_{x \in s} L_x(I_x(a)).$$

*Step 1.* The value of the last lift is the class integral of $I_x$. The class integral is linear for smooth left-invariant integrands (`New.classIntegral_sum`), and each $I_x$ is such an integrand (`New.Kernel.integrand_mem_smoothInvariants`). So the left side of the claim is the class integral of $F$ over $\Gamma_j \backslash G_j$.

*Step 2.* $K_j$ fixes $F$ under right translation. Let $b \in K_j$ and $a \in G_j$. Take $\beta$ to be a linear map that gives the value at $a$ of the chain of length $j$ ([Lemma](/decl/New.exists_linearMap_chain_eq_apply_pure/)). Let $T$ be the linear map that applies $\beta$ to the first $j$ factors of a tensor and then $J(\omega(a, g_{j+1})\,\cdot\,)$ with the last factor. Apply joint invariance to $T$ and to the tuple with $b$ in slot $j$ and $1$ elsewhere. This tuple moves $\Phi_{x,j-1}$ by $\omega(1, b)$ and $\Phi_{x,j}$ by $\omega(b, 1)$. By the equivariance of chains ([Lemma](/decl/New.chain_equivariant/)), the first move changes the value at $a$ of the short chain into its value at $ab$. Since $\omega(a, g_{j+1})\omega(b,1) = \omega(ab, g_{j+1})$, the second move changes the kernel at $a$ into the kernel at $ab$. So joint invariance says $F(ab) = F(a)$.

*Step 3.* By Step 2, the class integral of $F$ is its class sum. The level $K_j$ is free, so each weight is $1$, and the class integral is $\sum_r F(g_r)$ over the classes $r \in \Gamma_j\backslash G_j/K_j$.

*Step 4.* Fix $r$, and put $L'_x = L_x \circ J(\omega(g_r, g_{j+1})\Phi_{x,j})$, a linear map from $V_j$ to $M$. Then $F(g_r) = \sum_x L'_x\big((\mathrm{chain}(\Phi_x)_j\varphi)(g_r)\big)$. The family $(L'_x, \Phi_x)$ is jointly invariant at stage $j$: for a tuple $a$ with $a_i = 1$ for $i \ge j$ and a linear map $\beta$, apply the invariance of the old family to $a$ and to the map $T$ of Step 2 built from $g_r$ and $\beta$. The move of $\Phi_{x,j}$ is by $\omega(a_j, a_{j+1}) = \omega(1,1)$, so it is trivial. By the induction hypothesis at the points $g[j \mapsto g_r]$,

$$F(g_r) = \sum_{c \in \prod_{i<j}\Gamma_i\backslash G_i/K_i} \sum_x L'_x\big(\mathrm{KP}(\Phi_x, \varphi, \mathrm{cp}(c, g[j\mapsto g_r]), j)\big).$$

By the lemma on $\mathrm{KP}(\cdot, j+1)$, the term is $L_x(\mathrm{KP}(\Phi_x, \varphi, \mathrm{cp}(c, g[j\mapsto g_r]), j+1))$; the point at $j+1$ is $g_{j+1}$, unchanged. Sum over $r$, and use the lemma on sorting tuples by the last class. This gives the right side of the claim. $\square$

**Remark.** The proof uses joint invariance twice. In Step 2 it makes the integrand invariant, so that the integral is a class sum. In Step 4 it passes to the shorter chain. Freeness enters only in Step 3. Without it, the class sum has weights $1/\#(\Gamma_j \cap g_r K_j g_r^{-1})$, which divide the chosen group order of [chains of lifts and free levels](/chapter/upper-bound-objects/#chains-of-lifts-and-free-levels), and these can carry negative valuation at $p$.

**Remark (Formalization).** The class representatives $g_r$ are taken by `Quotient.out`. The statement holds for this choice. Joint invariance is what makes the two sides independent of it. The class integral is defined without measure theory, as a finite class sum divided by an index, as in [Hecke operators and class sums](/chapter/automorphic-forms/).

### Two consequences for kernel products

**Lemma.** Let $P_j(g, v)$ be a property of a point $g \in G_j$ and a vector $v \in V_j$. Suppose $P_0(g, \varphi(g))$ holds for all $g$. Suppose, for each $j < m$ and all $g, g', v$, that $P_j(g, v)$ implies $P_{j+1}(g', J(\omega(g, g')\Phi_j)v)$. Then $P_m(g_m, \mathrm{KP}(\Phi, \varphi, g, m))$ holds for all points $g$.

Lean: `New.kernelProduct_induction` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* Induction on $m$. For $m = 0$ it is the hypothesis on $\varphi$ at $g_0$. The step from $m$ to $m+1$ is the lemma on $\mathrm{KP}(\cdot, m+1)$ and the hypothesis at $j = m$. $\square$

**Lemma.** Let $\mathrm{size}_j(g, v)$ be a real size of $v \in V_j$ at $g \in G_j$, and let $r_j \ge 0$. Suppose, for $j < m$ and all $g, g', v$,

$$\mathrm{size}_{j+1}\big(g', J(\omega(g, g')\Phi_j)v\big) \le r_j\, \mathrm{size}_j(g, v),$$

and $\mathrm{size}_0(g, \varphi(g)) \le B$ for all $g$. Then, for all points $g$,

$$\mathrm{size}_m\big(g_m, \mathrm{KP}(\Phi, \varphi, g, m)\big) \le \Big(\prod_{j<m} r_j\Big) B.$$

Lean: `New.apply_kernelProduct_le_prod_mul` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* Apply the previous lemma to the property $\mathrm{size}_j(g, v) \le (\prod_{i<j} r_i)B$. The base is the bound on $\varphi$. For the step, $\mathrm{size}_{j+1} \le r_j\,\mathrm{size}_j \le r_j(\prod_{i<j}r_i)B$, since $r_j \ge 0$. $\square$

### The chain combination of the data

Now we return to the data $D$. The tower is $G_j = \mathrm{U}(X_j)(\mathbb A_f)$, with the levels $K_j$ of [columns and the composite lift](/chapter/upper-bound-objects/#columns-and-the-composite-lift) and the lift kernels $k_j$ of a twist $\vartheta$ ([Definition](/decl/New.Data.liftKernel/)). The data of $k_j$ are the finite parts of the Weil representation of $\mathrm{Hom}(X_j, X_{j+1})$.

**Definition (Chain combination).** Let $\Psi$ be a finitely supported function on tuples of translations, and let $\Phi_x = (\Phi_{x,i})_i$ be data for each tuple $x$. The chain combination is the linear map

$$\mathrm{CC}(\vartheta, \Psi, \Phi, j) = \sum_x \Psi(x)\,\mathrm{chain}(\Phi_x)_j$$

from forms on $X_0$ to forms on $X_j$.

Lean: `New.Data.chainCombination` (New/UpperBound/Objects/Columns.lean).

The restricted chain of [columns and the composite lift](/chapter/upper-bound-objects/#columns-and-the-composite-lift) is $\mathrm{res}\circ\mathrm{CC}(\vartheta, \Psi, v, m)$ on source forms, where $v_{x,j}$ is the translated datum.

**Theorem.** Let $\Phi$ be data such that the family $(\Psi(x)\cdot\mathrm{id}, \Phi_x)_{x \in \mathrm{supp}\,\Psi}$ is jointly invariant at stage $m$ for the kernels $k_j$. Let $\varphi$ be a source form, and $g = (g_j)$ points. Then

$$\big(\mathrm{CC}(\vartheta, \Psi, \Phi, m)\,\varphi\big)(g_m) = \sum_{c \in \prod_{j<m} \Gamma_j\backslash G_j/K_j}\; \sum_{x \in \mathrm{supp}\,\Psi} \Psi(x)\, \mathrm{KP}(\Phi_x, \varphi, \mathrm{cp}(c, g), m).$$

Lean: `New.Data.chainCombination_eq_sum` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* For $j < m$, the level $K_j$ lies in the chosen level, and the rank of $X_j$ is $n_j \le n_m$. So $K_j$ is free by the lemma on free levels of [chains of lifts and free levels](/chapter/upper-bound-objects/#chains-of-lifts-and-free-levels) ([Lemma](/decl/New.Data.classAut_eq_bot_of_le_chosenLevel/)). A source form is fixed by $K_0$. The value of $\mathrm{CC}$ at $g_m$ is $\sum_{x \in \mathrm{supp}\,\Psi} \Psi(x)(\mathrm{chain}(\Phi_x)_m\varphi)(g_m)$. Apply the theorem on plain sums with $L_x = \Psi(x)\cdot\mathrm{id}$. $\square$
