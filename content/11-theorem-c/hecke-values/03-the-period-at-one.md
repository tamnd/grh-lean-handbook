---
title: The period at one
lean:
  - New/OneLift/HeckeValues/PeriodAtOne.lean
decls:
  - New.Rows.detKernel
  - New.Rows.detPeriod
  - New.Rows.prod_range_corank_one_sub_q_pow
  - New.Rows.liftFn_charOfTamePart_det_eq_residueDatum
  - New.Rows.residueDatum_singleton_mul
  - New.Rows.detKernel_stdEmbFin_mul
  - New.Rows.detPeriod_eq_stdClassSum_sum
  - New.Rows.stdLevel_le_rightStabilizer_detKernel
  - New.Rows.sum_heckePolyCoeff_smul_modDatum_eq_modDatum
  - New.Rows.detPeriod_insert
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The period at one

A critical pair $p = (\nu, z)$ with $z = 1$ has no lift of rank $2z \geq 4$, so the lifts of [character-lifts](/chapter/character-lifts/) do not apply. Volume 12 ([twist measures](/chapter/twisting-theorem/#twist-measures-of-critical-pairs)) treats this case with a period of a theta kernel for the pair $(V, V)$, with $V$ the standard definite space of rank $N$. This section defines the period and proves its one structural property: adding a prime $v$ to the modulus multiplies the period by an explicit Euler factor. The proof is a Hecke computation at $v$ and the $q$-binomial theorem.

### Notation

$E$ is a CM field with its Weil data. $n$ is a finite index set, $N = \#n$, and $V = $ `stdSpace E n` is the standard definite space, with finite adelic group $G_f = U(V)(\mathbb{A}_f)$ and the stabiliser $K = $ `stdLevel E n` of the standard lattice. A modulus $\mathfrak{m}$ is a nonzero ideal of $\mathcal{O}_E$ that is never divisible by both $w$ and $\bar w$. Its set of primes is $\mathfrak{m}.\mathrm{places}$. For a family $\psi = (\psi_w)$ of characters of the residue fields, $\chi_\psi = $ `𝔪.charOfTamePart ψ` is the character modulo $\mathfrak{m}$ with components $\psi_w$. $\alpha$ is an automorphic character of $U(1)$, and `α.HasWeight e ψ` says that $\alpha$ has weight $e$ and tame part $\psi$ ([characters and twists](/chapter/fields-places-twists/#characters-twists-and-m-fold-twists)). For a finite place $v$ of norm $q$, `α.frobValue n v` is $\chi(\varpi)\,q^{N/2}$, where $\chi = $ `α.spaceChar N` and $\varpi$ is a uniformiser at $v$. Finally

$$\mathrm{qPochhammer}(q, N, X) = \prod_{l<N}(1 - q^lX).$$

The theta kernel `modKernelStdSpace` of [theta kernels and gauges](/chapter/theta-kernels-gauges/) takes a space, two characters, a modulus, a finite datum $\Psi$ on matrices modulo $\mathfrak{m}$, a polynomial in the matrix variables at the infinite places, and two points.

### The kernel and the period

**Definition (Determinant kernel).** For $c : \Phi \to \mathbb{N}$ and a datum $\Psi$ on $\mathrm{Mat}_n(\mathcal{O}/\mathfrak{m})$,

$$\mathrm{detKernel}(\Psi)(g) = \mathrm{modKernelStdSpace}\Big(V, \alpha, \alpha, \mathfrak{m}, \Psi, \prod_\tau\det(Z_\tau)^{c_\tau}\Big)(1, g),$$

with $Z_\tau$ the matrix of variables at $\tau$ (`variableMinor τ id id`). Both characters are $\alpha$, so the factor $\alpha(\det g)$ is part of the kernel.

Lean: `New.Rows.detKernel` (New/OneLift/HeckeValues/PeriodAtOne.lean).

**Definition (Period).** $\mathrm{detPeriod}(n, \alpha, c, \mathfrak{m}, \psi)$ is the class sum at the level $K$ of $\mathrm{detKernel}$ for the datum $x \mapsto \chi_\psi(\det x)$:

$$\mathrm{detPeriod} = \sum_{[g] \in G(E)\backslash G_f/K}\frac{\mathrm{detKernel}(\chi_\psi\circ\det)(g)}{\#\mathrm{Aut}(g)}.$$

Lean: `New.Rows.detPeriod` (New/OneLift/HeckeValues/PeriodAtOne.lean).

**Remark (Formalization).** The file sets `attribute [local instance low] Fintype.ofFinite`. The class sums are over finite types whose finiteness is known only as `Finite`, and this instance turns it into a `Fintype` for the sums. It is a local instance of low priority, so it does not change the meaning of any sum. The definition of the period does not assume that $\alpha$ has weight $-c$, and it does not assume that $\psi$ is trivial off $\mathfrak{m}$. Without these hypotheses the class sum is still a number, but the summand need not be invariant, and no result of this section applies.

### Three local lemmas

**Lemma (The corank product).** For $x \in \mathrm{Mat}_n(k_v)$ with $k_v$ of $q$ elements,

$$\prod_{l < N - \mathrm{rank}\,x}(1 - q^l) = \mathbf{1}(\det x),$$

the trivial character of $k_v$ at $\det x$. So the product is $1$ if $x$ is invertible and $0$ otherwise.

Lean: `New.Rows.prod_range_corank_one_sub_q_pow` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* If $x$ is invertible, the rank is $N$, the product is empty, and $\det x$ is a unit, so both sides are $1$. If $x$ is not invertible, its kernel is not $0$, so $N - \mathrm{rank}\,x > 0$ and the factor at $l = 0$ is $1 - 1 = 0$. A character of $k_v$ vanishes at non-units by convention (`MulChar.map_nonunit`), so the right side is $0$ too. $\square$

**Lemma (Lift of the determinant character).** For a modulus $\mathfrak{n}$, the lift `liftFn` to finite adelic matrices of $x \mapsto \chi_\psi(\det x)$ is the residue datum that sends a matrix integral at all primes of $\mathfrak{n}$ to $\prod_{w}\psi_w(\det S_w)$, with $S_w$ its reduction at $w$, and every other matrix to $0$.

Lean: `New.Rows.liftFn_charOfTamePart_det_eq_residueDatum` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* The reduction modulo $\mathfrak{n}$ is the product of the reductions at its primes, the determinant commutes with reduction (`map_det`), and $\chi_\psi$ is the product of the $\psi_w$. Apply `liftFn_eq_residueDatum`. $\square$

**Lemma (One more prime).** Let $v \notin \mathfrak{m}.\mathrm{places}$ and $\mathfrak{m}'.\mathrm{places} = \{v\}\cup\mathfrak{m}.\mathrm{places}$. Then the residue datum of $S \mapsto \prod_{w\mid\mathfrak{m}'}\psi_w(\det S_w)$ is the product of the residue datum of $\psi_v\circ\det$ at $v$ and the residue datum of $S \mapsto \prod_{w\mid\mathfrak{m}}\psi_w(\det S_w)$.

Lean: `New.Rows.residueDatum_singleton_mul` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* A matrix is integral at the primes of $\mathfrak{m}'$ if and only if it is integral at $v$ and at the primes of $\mathfrak{m}$. Where it is integral, the finite product over the primes of $\mathfrak{m}'$ splits off the factor at $v$, since $v \notin \mathfrak{m}.\mathrm{places}$ (`finprod_mem_insert`). Elsewhere both sides are $0$. $\square$

### Invariance

From here on $\alpha$ has weight $-c$ and tame part $\psi$, and $\psi_w = 1$ for $w \notin \mathfrak{m}.\mathrm{places}$.

**Lemma (Left invariance).** For every datum $\Psi$, every rational point $\gamma$ of $U(V)$ and every $g$, $\mathrm{detKernel}(\Psi)(\gamma g) = \mathrm{detKernel}(\Psi)(g)$.

Lean: `New.Rows.detKernel_stdEmbFin_mul` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* Let $Q = \prod_\tau\det(Z_\tau)^{c_\tau}$. Translation of the kernel by $\gamma$ on the left equals the factor $\prod_\tau\tau(\det\gamma)^{c_\tau}$ times the kernel for the polynomial $Q$ with the variables substituted by $\gamma^{-1}$ (`modKernelStdSpace_embFin_mul`). This is where the weight $-c$ of $\alpha$ enters. The substitution of $\gamma^{-1}$ in a product of determinants multiplies it by $\prod_\tau(\tau(\det\gamma)^{c_\tau})^{-1}$ (`twoSidedSubst_stackedDetProd`). The kernel is linear in the polynomial. The two factors cancel, since $\det\gamma \neq 0$. $\square$

**Lemma (Right invariance).** The kernel for the datum $\chi_\psi\circ\det$ is invariant under right translation by $K$.

Lean: `New.Rows.stdLevel_le_rightStabilizer_detKernel` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* Right translation by $k \in K$ replaces the datum by $y \mapsto \alpha(\det k)\,\chi_\psi(\det(\bar k^{-1}y))$, with $\bar k$ the reduction modulo $\mathfrak{m}$ (`modKernel_mul_stdLevel_right`). Since $\psi$ is trivial off $\mathfrak{m}$, $\alpha(\det k) = \chi_\psi(\det\bar k)$ (`apply_det_eq_charOfTamePart`). The determinant is multiplicative, so the datum is $\chi_\psi\circ\det$ again. $\square$

**Proposition (The period as a sum over GL).** With $\mathbf{1}_1 = $ `Pi.single 1 1` the indicator of the unit matrix and `liftMod y` a lift of $y$ to $K$,

$$\mathrm{detPeriod} = \sum_{[g]}\frac{1}{\#\mathrm{Aut}(g)}\sum_{y\in\mathrm{GL}_n(\mathcal{O}/\mathfrak{m})}\mathrm{detKernel}(\mathbf{1}_1)(g\cdot\mathrm{liftMod}\,y).$$

Lean: `New.Rows.detPeriod_eq_stdClassSum_sum` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* $\chi_\psi\circ\det = \sum_{y\in\mathrm{GL}_n}\chi_\psi(\det y)\,\mathbf{1}_y$, since $\chi_\psi(\det x) = 0$ when $x$ is not invertible. By the computation in the proof of right invariance, $\mathrm{detKernel}(\mathbf{1}_1)(g\cdot\mathrm{liftMod}\,y) = \chi_\psi(\det y)\,\mathrm{detKernel}(\mathbf{1}_y)(g)$. The kernel is linear in the datum (`modKernelBilin_apply`). $\square$

### The Hecke step

For a subspace $U$ of $k_v^n$ of dimension $i$, put $\mathrm{heckePolyCoeff}(X, U) = (-X)^i q^{\binom i2}$, and let $\gamma_U$ be the transposed Hecke coset representative `basicCosetRep U`, placed at the split place $v$ by `ofSplitPlace`. These are the terms of the Hecke polynomial of [Hecke polynomials of lifts](/chapter/character-lifts/#hecke-polynomials-of-lifts).

**Lemma (Hecke sum of the datum).** Let $v \notin \mathfrak{m}.\mathrm{places}$ be split, $\mathfrak{m}'.\mathrm{places} = \{v\}\cup\mathfrak{m}.\mathrm{places}$, $X = (\mathrm{frobValue}\,v)^{-1}$, and let $P$ be a model of the vacuum. Let $f_{\mathfrak{m}}$ be the theta datum `modDatum` for $\mathfrak{m}$, the datum $\chi_\psi\circ\det$ and $P$. Then

$$\sum_U\mathrm{heckePolyCoeff}(X, U)\cdot\omega\big((1,1), (1, \gamma_U)\big)f_{\mathfrak{m}} = f_{\mathfrak{m}'}.$$

Lean: `New.Rows.sum_heckePolyCoeff_smul_modDatum_eq_modDatum` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* Step 1. The places of $\mathfrak{m}'$ are disjoint from their conjugates, because $\mathfrak{m}'$ is a modulus. The base change of $\alpha$ is unramified at $v$, because $\psi_v = 1$.

Step 2. The datum $f_{\mathfrak{m}}$ is the vacuum at $v$: its projection to $\{v\}$ is itself, since $v$ is not in the conjugate closure of $\mathfrak{m}.\mathrm{places}$ (`projOn_schrodingerOp_vacElem`).

Step 3. For an unramified character and the vacuum at a split place, the Hecke sum of translates puts in at $v$ the function $x \mapsto \mathrm{qPochhammer}(q, N - \mathrm{rank}\,x, X\cdot\mathrm{frobValue})$ of the reduction $x$ (`sum_heckePolyCoeff_smul_pairWeil`, from [split places](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials)). With $X = \mathrm{frobValue}^{-1}$ this is $\prod_{l<N-\mathrm{rank}\,x}(1 - q^l)$, which by the corank lemma is $\mathbf{1}(\det x) = \psi_v(\det x)$.

Step 4. The datum at $v$ and the datum at the primes of $\mathfrak{m}$ are Schwartz-Bruhat at disjoint sets, and the Schrodinger operator of a union is the product (`schrodingerOp_union`). By the lemma on one more prime and the lemma on the lift of the determinant character, the product is the datum for $\mathfrak{m}'$. $\square$

**Theorem (Adding a prime).** Let $\alpha$ have weight $-c$ and tame part $\psi$ with $\psi_w = 1$ off $\mathfrak{m}$. Let $v \notin \mathfrak{m}.\mathrm{places}$ and $\mathfrak{m}'.\mathrm{places} = \{v\}\cup\mathfrak{m}.\mathrm{places}$, and let $q$ be the norm of $v$. Then

$$\mathrm{detPeriod}(n, \alpha, c, \mathfrak{m}', \psi) = \mathrm{qPochhammer}\big(q, N, \mathrm{frobValue}(v)^{-1}\big)\cdot\mathrm{detPeriod}(n, \alpha, c, \mathfrak{m}, \psi).$$

Lean: `New.Rows.detPeriod_insert` (New/OneLift/HeckeValues/PeriodAtOne.lean).

*Proof.* Step 1 ($v$ is split). If $\bar v = v$, then $v$ and $\bar v$ both lie in $\mathfrak{m}'.\mathrm{places}$, which contradicts that $\mathfrak{m}'$ is a modulus.

Step 2 (the kernels). Apply the theta functional to the identity of the Hecke step. It gives, for every $g$,

$$\mathrm{detKernel}_{\mathfrak{m}'}(g) = \sum_U\mathrm{heckePolyCoeff}(X, U)\cdot\mathrm{detKernel}_{\mathfrak{m}}(g\gamma_U).$$

Step 3 (class sums are integrals). Both kernels are invariant on the right under $K$ by right invariance, and on the left under the rational points by left invariance. So their class sums are class integrals (`classIntegral_eq_classSum`), and a class integral does not change under right translation by $\gamma_U$ (`classIntegral_sum`). So $\mathrm{detPeriod}_{\mathfrak{m}'} = (\sum_U\mathrm{heckePolyCoeff}(X, U))\cdot\mathrm{detPeriod}_{\mathfrak{m}}$.

Step 4 (the $q$-binomial theorem). The number of subspaces of $k_v^n$ of dimension $i$ is the Gaussian binomial $\binom Ni_q$, and $\sum_i\binom Ni_q(-X)^iq^{\binom i2} = \prod_{l<N}(1 - q^lX)$ (`q_binomial_submodule`). $\square$

**Example (Rank two).** For $N = 2$ the factor is $(1 - X)(1 - qX)$. Volume 12 uses this case for the critical pairs with $z = 1$: it applies the theorem to the character $\nu\vartheta\upsilon$ on $U(2)$, and the two factors are the Euler factors at $v$ of the twisted $L$-value at $s = 1$ and of its neighbour. See [twist measures](/chapter/twisting-theorem/#twist-measures-of-critical-pairs).

**Remark (Formalization).** The hypothesis that $v$ is split is not stated. It follows from the definition of `Modulus`, which asks that the set of places be disjoint from its conjugate. The value `frobValue` is not $0$, since $\chi(\varpi)$ is a unit and $q > 0$; the proof of the Hecke step uses this to cancel $X\cdot\mathrm{frobValue} = 1$. The theorem is an identity of complex numbers and does not claim that the periods are nonzero.
