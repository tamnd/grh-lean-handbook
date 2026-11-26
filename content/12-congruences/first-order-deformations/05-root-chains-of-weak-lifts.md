---
title: Root chains of weak lifts
lean:
  - New/Congruences/FirstOrder/HeckeStrings.lean
decls:
  - New.Selmer.exists_diagonal_mem_norm_ge
  - New.Selmer.pow_finrank_le_nnnorm_det
  - New.Selmer.exists_integral_multiple_eval_one
  - New.Selmer.exists_one_le_nnnorm_one_sub_pow_mul_root
  - New.Selmer.exists_eventually_one_le_norm_eval_charpoly
  - New.Selmer.isRoot_hecke_chain
  - New.Selmer.eventually_exists_hasRootChain
  - New.Selmer.orthogonal_mem_invtSubmodule_heckePolyOnForms
  - New.Selmer.le_of_isotypic_mem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Root chains of weak lifts

The operator at an auxiliary place, built in the next section, needs one fact about each form that it must not move: at the place, the Hecke polynomial of the form has a full chain of roots, and the rest of the polynomial is integral with value $1$ at $1$ after a normalization. This section proves that fact for weak lifts, the second main result of the chapter. It also proves three small tools of $\ell$-adic linear algebra and two facts on Hecke-stable spaces of forms, which [the bound for denominators](/chapter/denominator-bound/) uses.

Norms are $\ell$-adic. We fix the isomorphism $\iota \colon \mathbb{C} \to \overline{\mathbb{Q}}_\ell$ of [building the representations](/chapter/building-representations/), and we read complex numbers in $\overline{\mathbb{Q}}_\ell$ through it. Two polynomials over $\overline{\mathbb{Q}}_\ell$ are *congruent* if each coefficient of their difference has norm less than $1$, that is, lies in the maximal ideal of the integers.

### Three tools

**Lemma (Integral combination).** Let $Z$ be a complex space with a basis $b_1, \dots, b_m$. Let $\mathcal{G}$ be a set of operators on $Z$ that contains $\sum_p \iota^{-1}(d_p) G_p$ for all $G_1, \dots, G_m \in \mathcal{G}$ and all $d_p$ with $\|d_p\| \leq 1$. For each $k$ let the operator that is diagonal in $b$ with eigenvalues $l_{k1}, \dots, l_{km}$ lie in $\mathcal{G}$. Then some operator of $\mathcal{G}$, diagonal in $b$ with eigenvalues $\mu_1, \dots, \mu_m$, has $\|\mu_k\| \geq \|l_{kk}\|$ for every $k$.

Lean: `New.Selmer.exists_diagonal_mem_norm_ge` (New/Congruences/FirstOrder/HeckeStrings.lean), with `New.Selmer.exists_integral_combination_norm_ge` for the choice of the $d_p$.

*Proof.* Consider the linear forms $F_k = \sum_p l_{pk} X_p$. The residue field of $\overline{\mathbb{Q}}_\ell$ is infinite, so finitely many hyperplanes do not cover the residue space. This gives integral $d_p$ at which each $F_k$ has norm at least the norm of each of its coefficients, in particular of $l_{kk}$. The combination $\sum_p \iota^{-1}(d_p) G_p$ of the given diagonal operators is diagonal with eigenvalues $F_k(d)$. $\square$

**Lemma (Determinant).** Let $\Lambda$ be an operator on a complex space $Z$ of dimension $N$, and let $c \in \overline{\mathbb{Q}}_\ell$. If $\|c\, \iota(\mu)\| \geq \varepsilon$ for every eigenvalue $\mu$ of $\Lambda$, then $\|c^N \iota(\det \Lambda)\| \geq \varepsilon^N$.

Lean: `New.Selmer.pow_finrank_le_nnnorm_det` (New/Congruences/FirstOrder/HeckeStrings.lean).

*Proof.* Over $\mathbb{C}$ the determinant is the product of the $N$ roots of the characteristic polynomial, with multiplicity. Each factor $c\,\iota(\mu)$ has norm at least $\varepsilon$. $\square$

**Lemma (Integral divisor).** Let $B$ be monic, let $C$ have integral coefficients, and let $AB \equiv C \equiv A'B$, with $\|A'(1)\| \geq 1$. Then $A$ divides an integral polynomial $e$ with $e(1) = 1$.

Lean: `New.Selmer.exists_integral_multiple_eval_one` (New/Congruences/FirstOrder/HeckeStrings.lean).

*Proof.* The coefficients of $AB$ are integral, since $AB \equiv C$. By Gauss's lemma for the monic factor $B$, the coefficients of $A$ are bounded by those of $AB$, so $A$ is integral. In the same way $(A - A')B \equiv 0$ gives $A \equiv A'$, so $A(1) \equiv A'(1)$ and $\|A(1)\| \geq 1$. Put $e = A / A(1)$. It is integral, and $e(1) = 1$. $\square$

### Frobenius elements where $1 - u$ is a unit

**Lemma.** Let $p \neq 0$ be a polynomial over $\overline{\mathbb{Q}}_\ell$, and let $\|y^j - 1\| = 1$ for $1 \leq j \leq \deg p$. Then there is $i$ with $\|1 - y^i \mu\| \geq 1$ for every root $\mu$ of $p$.

Lean: `New.Selmer.exists_one_le_nnnorm_one_sub_pow_mul_root` (New/Congruences/FirstOrder/HeckeStrings.lean).

*Proof.* Suppose that each $i \leq \deg p$ has a root $\mu_i$ with $y^i \mu_i \equiv 1$. Then $y^i \mu_i$ is a unit. If $\mu_i = \mu_j$ with $i < j$, then $(1 - y^i \mu_i) - (1 - y^j \mu_j) = y^i \mu_i (y^{j-i} - 1)$ is a unit, but it is a difference of two elements of the maximal ideal. So the $\deg p + 1$ roots $\mu_i$ are distinct, which is impossible. $\square$

**Lemma.** Let $T$ be a continuous map from $G$ to $n \times n$ matrices over $\overline{\mathbb{Q}}_\ell$. Let $\delta_0, \delta_1, \dots \in G$ with $T(\delta_i) = y^i A$ for a fixed matrix $A$, and let $\|y^j - 1\| = 1$ for $1 \leq j \leq 4n + 2$. Then there is $i$ such that $\|\det(1 - T(\varphi))\| \geq 1$ for all $\varphi$ near $\delta_i$.

Lean: `New.Selmer.exists_eventually_one_le_norm_eval_charpoly` (New/Congruences/FirstOrder/HeckeStrings.lean).

*Proof.* Apply the last lemma to the characteristic polynomial of $A$. Then $\det(1 - y^i A) = \prod_\mu (1 - y^i \mu)$ has norm at least $1$. The set where $\|\det(1 - T(\varphi))\| < 1$ is closed, because $T$ is continuous and the open unit ball is closed. So its complement is a neighborhood of $\delta_i$. $\square$

The proof uses the hypothesis on $y^j$ only for $j \leq n$. The source states it up to $4n + 2$, the range in which [the bound for denominators](/chapter/denominator-bound/) has it.

### The chain of roots

Now fix a descent pair: a hermitian space $W$ of rank $r$ beside the definite space $V$ of rank $n > r$, and $t = n - r$. Let $f \neq 0$ be a form on $V$ of the weight of the pair, in an isotypic space $x$, with Galois representation $\rho_x$. Let $\chi$ be the $\ell$-adic character attached through $\iota$ to the Hecke character of $W$, and let $u = \chi \otimes \rho_x$ be the *normalized representation*. The form is a *weak lift* if $\det(1 - u(g)) = 0$ for every $g \in G$. The character $\chi$ and the twist $u$ are defined in [the main summands of the attached Galois representations](/chapter/main-summands/), which is a later chapter. The source file of this section imports them from there.

At a split place $w \nmid \ell$ of norm $q$, write $X_0$ for the value of the Hecke character of $W$ at $w$, read in $\mathbb{C}$. If $\varphi$ is a geometric Frobenius element at $w$, then $\chi(\varphi) = \iota(X_0)^{-1}$.

**Theorem (Root chain).** Let $f$ be a weak lift, and let $w \nmid \ell$ be a split place of norm $q$ where $f$ has the Hecke polynomial $S$. Then $X_0 q^i$ is a root of $S$ for every $i < t$.

Lean: `New.Selmer.isRoot_hecke_chain` (New/Congruences/FirstOrder/HeckeStrings.lean), with `New.Selmer.normalizingAvatar_eq_of_isFrob` for the value of $\chi$.

*Proof.* Let $\varphi$ be a geometric Frobenius element at $w$. By local-global compatibility at split places ([building the representations](/chapter/building-representations/)), the image of $S$ under $\iota$ kills $\rho_x(\varphi)$. The weak lift condition gives an eigenvalue $1$ of $u(\varphi) = \chi(\varphi) \rho_x(\varphi)$, so $\iota(X_0)$ is an eigenvalue of $\rho_x(\varphi)$, and $X_0$ is a root of $S$. The Hecke character of $W$ has $|X_0|^2 = q^r$, so $|X_0|^2 q^t = q^n$. The local representation at $w$ is unitary and spherical, and [the chain lemma](/decl/New.Patching.isRoot_chain_of_norm/) gives the roots $X_0, X_0 q, \dots, X_0 q^{t-1}$. $\square$

Since the powers $q^i$ are distinct, the factors $X - q^i$ are coprime, and so $\prod_{i<t}(X - q^i)$ divides $S(X_0 X)$ (`New.Selmer.prod_X_sub_C_dvd_comp_of_hasHeckePolyAt`).

Recall that $S$ has a *root chain of length $t$ at $d$ with cofactor dividing $e$* if $S(dX) = \prod_{i<t}(X - q^i) \cdot T$ and $T$ divides $e$ ([the definition](/decl/New.Patching.HasRootChain/)). Write $\mathrm{cyc}^{-1}$ for the inverse cyclotomic character. At a geometric Frobenius element $\varphi$ at $w$, $\mathrm{cyc}^{-1}(\varphi) = q$.

**Theorem (Root chains at most Frobenius elements).** Let $f$ be a weak lift, and let the characteristic polynomials of all $u(g)$ have integral coefficients. Then for most Frobenius data $(w, \varphi)$ the following holds. Let $S$ be a polynomial over $\overline{\mathbb{Q}}_\ell$ with $\|S(1)\| \geq 1$, and let
$$\det(X - u(\varphi)) \equiv S \cdot \prod_{i<t} \bigl(X - \mathrm{cyc}^{-1}(\varphi)^i\bigr).$$
Then there is a polynomial $e$ with $\ell$-adically integral coefficients and $e(1) = 1$ such that the Hecke polynomial $H_w$ of $x$ has a root chain of length $t$ at $\iota^{-1}(\chi(\varphi))^{-1}$ with cofactor dividing $e$.

Lean: `New.Selmer.eventually_exists_hasRootChain` (New/Congruences/FirstOrder/HeckeStrings.lean).

Here "most Frobenius data" is the filter of [what attached means](/chapter/attached-representations/): every nonempty open subset of $G$ has a nonempty open part on which the statement holds at almost all places.

*Proof.* Take the Frobenius data at which $\rho_x$ is attached within $1/2$ to the Hecke polynomials, at which $x$ is an eigenspace, and whose place is split and off $\ell$. These are most Frobenius data. By the root chain, $H_w(X_0 X) = T \cdot \prod_{i<t}(X - q^i)$. Apply $\iota$, and write $B = \prod_{i<t}(X - \mathrm{cyc}^{-1}(\varphi)^i)$, the image of the chain. The character $\chi$ has values of norm $1$. Rescaling by $\chi(\varphi)$ keeps the congruence of the attached representation (`New.Selmer.norm_coeff_comp_sub_charpoly_smul_lt_one`), so
$$\chi(\varphi)^n\, \iota(T)\, B \equiv \det(X - u(\varphi)) \equiv S\, B.$$
The middle term is integral by hypothesis. The lemma on integral divisors, with $A = \chi(\varphi)^n \iota(T)$ and $A' = S$, gives $e$. Then $T$ divides $e$ after $\iota^{-1}$. $\square$

The polynomial $S$ is the part of the characteristic polynomial away from the chain. The condition $\|S(1)\| \geq 1$ says that $1$ is not a root of $S$ modulo $\ell$. The lemma on Frobenius elements where $1 - u$ is a unit is how [the bound for denominators](/chapter/denominator-bound/) finds Frobenius elements with this property.

**Example.** Let $n = 2$ and $r = 1$, so $t = 1$. The chain is the one root $X_0$, and $B = X - 1$. If $u(\varphi)$ has eigenvalues $1$ and $\beta$, then $S = X - \beta$ and $\|S(1)\| = \|1 - \beta\|$. The theorem says: if $\beta \not\equiv 1$, then $H_w(X_0 X) = (X - 1) T$ with $T$ a divisor of an integral $e$ with $e(1) = 1$. Here $T$ is linear, $T = \lambda(X - \beta')$ with $\iota(\beta') \equiv \beta$, and $e = (X - \beta')/(1 - \beta')$.

### Hecke-stable spaces of forms

Let $\mathrm{Forms}$ be the space of forms of the level and weight of the descent pair, with its inner product. For a split place $w$ off the places of the pair and their conjugates, write $H_w(X)$ for the Hecke polynomial $\sum_i (-X)^i q^{i(i-1)/2} T_{w,i}$ as an operator, for $X \in \mathbb{C}$.

**Lemma.** Let $Z \subseteq \mathrm{Forms}$ be stable under all $H_w(X)$. Then so is its orthogonal complement.

Lean: `New.Selmer.orthogonal_mem_invtSubmodule_heckePolyOnForms` (New/Congruences/FirstOrder/HeckeStrings.lean).

*Proof.* The adjoint of $H_w(X)$ is $H_{\bar w}(\bar X)$, and $Z$ is stable under it. $\square$

**Lemma.** Let $Z, N \subseteq \mathrm{Forms}$, and let $Z$ be stable under all $H_w(X)$. If every nonzero form of $Z$ that lies in an isotypic space lies in $N$, then $Z \subseteq N$.

Lean: `New.Selmer.le_of_isotypic_mem` (New/Congruences/FirstOrder/HeckeStrings.lean).

*Proof.* The forms of $Z$ are spherical off the places of the pair. The operators that keep $Z$ form a subspace that contains every $H_w(X)$, so it contains each Hecke operator $T_{w,i}$. A space of spherical forms that is stable under the Hecke operators off a finite set is spanned by eigenforms, and each eigenform lies in an isotypic space. $\square$
