---
title: Heights over the isomorphisms with the l-adic numbers
lean:
  - New/Reduction/Lattices/Heights.lean
  - Lib/General/NumberTheory/PadicLimitsValuation.lean
decls:
  - New.PrimePadicIso
  - New.HeightLe
  - New.HeightLe.mono
  - New.HeightLe.rpow_mul
  - New.HeightLe.of_mul_le
  - New.HeightLe.of_le
  - New.HeightLe.inv_const
  - New.HeightLe.mul
  - New.HeightLe.prod
  - New.HeightLe.pow
  - New.log_product_formula
  - New.HeightLe.norm_algebraMap_norm_gen_le
  - New.isAlgebraic_of_norm_complexToCp_le
  - New.HeightLe.nonneg_of_one
  - New.HeightLe.neg_le_of_norm_map_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Heights over the isomorphisms with the l-adic numbers

The lower bound of Section 2 came from the product formula in a number field. In the source the numbers are complex numbers, such as Gram determinants, and no number field is fixed. The source replaces the places of a number field by the automorphisms $\sigma$ of $\mathbb{C}$ and the isomorphisms $\iota\colon \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$. Bounds for all $\sigma H$ and all $\iota H$ are bounds at all places of every number field that contains $H$.

### The isomorphisms

**Definition (Prime with an isomorphism).** A *prime with an isomorphism* $\iota$ is a pair of a prime $\ell$ and an isomorphism of fields $\iota\colon \mathbb{C} \to \bar{\mathbb{Q}}_\ell$, where $\bar{\mathbb{Q}}_\ell$ is an algebraic closure of $\mathbb{Q}_\ell$. We write $\iota \mid \ell$.

Lean: `New.PrimePadicIso` (New/Reduction/Lattices/Heights.lean).

Such isomorphisms exist, because $\mathbb{C}$ and $\bar{\mathbb{Q}}_\ell$ are algebraically closed fields of characteristic $0$ with the same uncountable cardinality. The proof uses the axiom of choice. The source never uses a particular $\iota$.

The norm $\|\cdot\|$ on $\bar{\mathbb{Q}}_\ell$ is the unique extension of the $\ell$-adic absolute value. For a number field $K \subset \mathbb{C}$, the map $x \mapsto \|\iota x\|$ on $K$ is the absolute value $|\cdot|_v$ of a place $v \mid \ell$, normalized as in Section 2. Every place $v \mid \ell$ comes from some $\iota$, because every embedding $K \to \bar{\mathbb{Q}}_\ell$ extends to an isomorphism $\mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ (`New.exists_ringEquiv_extend` in the source).

### The algebraicity criterion

The source does not assume that the numbers it bounds are algebraic. It derives this from the bounds.

**Theorem (Algebraicity from l-adic bounds).** Let $\ell$ be a prime, let $x \in \mathbb{C}$, and let $c \in \mathbb{R}$. Suppose that $\|\iota x\| \leq c$ for every isomorphism $\iota\colon \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$, where the norm is taken in $\mathbb{C}_\ell$ after the isometric embedding $\bar{\mathbb{Q}}_\ell \subset \mathbb{C}_\ell$. Then $x$ is algebraic over $\mathbb{Q}$.

Lean: `New.isAlgebraic_of_norm_complexToCp_le` (Lib/General/NumberTheory/PadicLimitsValuation.lean).

*Proof.* Suppose $x$ is transcendental. The algebraic elements of $\bar{\mathbb{Q}}_\ell$ form a countable set, so the transcendental elements are dense. Take a transcendental $y$ with $\|y\| > c$. The field isomorphism $\mathbb{Q}(x) \cong \mathbb{Q}(y)$ with $x \mapsto y$ extends to an isomorphism $\iota\colon \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ (`New.exists_ringEquiv_extend`). Then $\|\iota x\| = \|y\| > c$, a contradiction. $\square$

### Heights of families

**Definition (Height at most c).** Let $y = (y_\iota)$ be a family of complex numbers, with one member for each prime with an isomorphism $\iota$. Let $c \in \mathbb{R}$. The family $y$ has *height at most $c$* if there are a number $H \in \mathbb{C}$, $H \neq 0$, a real number $\alpha$, and real numbers $h(\ell) \geq 0$ for $\ell \in \mathbb{N}$, such that:

1. $|\sigma H| \leq e^{\alpha}$ for every automorphism $\sigma$ of $\mathbb{C}$;
2. $\|\iota(H y_\iota)\| \leq \ell^{h(\ell)}$ for every $\iota \mid \ell$;
3. $\alpha + \sum_{\ell \in U} h(\ell) \log \ell \leq c$ for every finite set $U$ of primes.

Lean: `New.HeightLe` (New/Reduction/Lattices/Heights.lean).

The multiplier $H$ clears the denominators of $y$, and $\alpha$ charges its archimedean size to $c$. The numbers $h(\ell)$ bound the denominators that remain at $\ell$. The family may depend on $\iota$, but the multiplier may not. Section 6 needs this: there $y_\iota$ is a Gram determinant for a twist $\xi_\iota$ that depends on $\iota$.

**Example (The constant family 1/2).** Let $y_\iota = 1/2$ for all $\iota$. Take $H = 1$, $\alpha = 0$, $h(2) = 1$ and $h(\ell) = 0$ for $\ell \neq 2$. Then $\|\iota(1/2)\| = 2$ for $\iota \mid 2$, and $\|\iota(1/2)\| = 1$ for $\iota \mid \ell$ with $\ell$ odd. So $y$ has height at most $\log 2$. The corollary at the end of this section shows that $y$ has no height bound $c < \log 2$.

A height bound can be negative. For the constant family $2$, take $H = 1/2$, $\alpha = -\log 2$ and $h = 0$: the bound is $-\log 2$.

**Remark (Comparison with the Weil height).** For $z \neq 0$ in a number field $K$ of degree $d$, the textbook height is $h(z) = d^{-1} \sum_v n_v \log^+ |z|_v$ over all places of $K$ (Bombieri and Gubler, *Heights in Diophantine Geometry*, Chapter 1). Take $H = 1$, $\alpha = 0$ and $h(\ell) \log \ell = \max_{v \mid \ell} \log^+ |z|_v$. Since $n_v \geq 1$, the constant family $z$ has height at most $d \cdot h_{\mathrm{fin}}(z)$, with $h_{\mathrm{fin}}$ as in Section 2. The notion of the source is not normalized by the degree, and it is a bound, not a value.

**Remark (Formalization).** Condition 3 is a bound over every finite set of primes. It is not a bound for the infinite sum $\sum_\ell h(\ell) \log \ell$. In Mathlib the infinite sum of a family that is not summable has the junk value $0$, and a bound for it would say nothing. Since all $h(\ell) \geq 0$, condition 3 says that the series converges and that $\alpha$ plus its sum is at most $c$. The values $h(\ell)$ for $\ell$ not prime enter nowhere.

### The calculus of heights

The following lemmas combine height bounds.

**Lemma (Monotonicity).** If $y$ has height at most $c$, $c \leq c'$, and $\|\iota y'_\iota\| \leq \|\iota y_\iota\|$ for every $\iota$, then $y'$ has height at most $c'$.

Lean: `New.HeightLe.mono` (New/Reduction/Lattices/Heights.lean).

*Proof.* Keep $H$, $\alpha$ and $h$. $\square$

**Lemma (Factors prime to the prime).** Let $y$ have height at most $c \leq c'$. For each $\iota \mid \ell$ let $N_\iota \in \mathbb{N}$ be prime to $\ell$, and let $e_\iota \in \mathbb{Q}$. Then the family $N_\iota^{e_\iota} y_\iota$, with the positive real power, has height at most $c'$.

Lean: `New.HeightLe.rpow_mul` (New/Reduction/Lattices/Heights.lean).

*Proof.* Write $e_\iota = a/b$ with $b \geq 1$. Then $(N_\iota^{e_\iota})^b = N_\iota^a$ has norm $1$ under $\iota$, since $N_\iota$ is an $\ell$-adic unit. So $\|\iota N_\iota^{e_\iota}\| = 1$. Apply monotonicity. $\square$

**Lemma (Bounds of any sign).** Let $H \neq 0$ with $|\sigma H| \leq e^\alpha$ for all $\sigma$. Let $e(\ell) \in \mathbb{R}$, of any sign, with $\|\iota(H y_\iota)\| \leq e^{e(\ell)}$ for every $\iota \mid \ell$, and $\alpha + \sum_{\ell \in U} e(\ell) \leq c$ for every finite set $U$ of primes. Then $y$ has height at most $c$.

Lean: `New.HeightLe.of_mul_le` (New/Reduction/Lattices/Heights.lean).

*Proof.* Take $h(\ell) = \max(e(\ell), 0) / \log \ell$ for $\ell$ prime. The sum of $\max(e(\ell), 0)$ over $U$ is the sum of $e(\ell)$ over the part of $U$ where $e(\ell) \geq 0$, which is again a finite set of primes. $\square$

**Lemma (No multiplier).** If $\sum_{\ell \in U} e(\ell) \leq c$ for every finite set $U$ of primes and $\|\iota y_\iota\| \leq e^{e(\ell)}$ for every $\iota \mid \ell$, then $y$ has height at most $c$.

Lean: `New.HeightLe.of_le` (New/Reduction/Lattices/Heights.lean).

*Proof.* Take $H = 1$ and $\alpha = 0$ in the previous lemma. $\square$

**Lemma (Inverses).** If $H \neq 0$ and $|\sigma H| \leq e^c$ for all $\sigma$, then the constant family $H^{-1}$ has height at most $c$.

Lean: `New.HeightLe.inv_const` (New/Reduction/Lattices/Heights.lean).

*Proof.* Take the multiplier $H$, so that $H \cdot H^{-1} = 1$, and $e = 0$. $\square$

**Lemma (Products and powers).** If $y$ and $y'$ have height at most $c$ and $c'$, then the family $y_\iota y'_\iota$ has height at most $c + c'$. If $y^{(i)}$ has height at most $c_i$ for each $i$ in a finite set $s$, then $\prod_{i \in s} y^{(i)}$ has height at most $\sum_{i \in s} c_i$. If $y$ has height at most $c$, then $y^n$ has height at most $nc$.

Lean: `New.HeightLe.mul`, `New.HeightLe.prod`, `New.HeightLe.pow` (New/Reduction/Lattices/Heights.lean).

*Proof.* For the product, take the multiplier $HH'$, the bound $\alpha + \alpha'$, and $h + h'$. The other two statements follow by induction. The empty product is the constant family $1$, which has height at most $0$ with $H = 1$. $\square$

### The product formula

The source proves the product formula only for $\mathbb{Q}$. It reaches number fields through the norm.

**Theorem (Product formula for the rationals).** Let $q \in \mathbb{Q}$, and let $B \in \mathbb{N}$ exceed both the absolute value of the numerator of $q$ and its denominator. Then
$$\log |q| + \sum_{p < B,\ p \text{ prime}} \log |q|_p = 0.$$

Lean: `New.log_product_formula` (New/Reduction/Lattices/Heights.lean).

*Proof.* If $q = 0$, every term is $\log 0 = 0$. Otherwise write $|q| = a/b$ with $a, b$ positive integers less than $B$. Factor $a$ and $b$ into primes less than $B$. The term of $p$ in $\log a - \log b$ is $(v_p(a) - v_p(b)) \log p$, and $\log |q|_p = -(v_p(a) - v_p(b)) \log p$. $\square$

**Remark (Formalization).** In Mathlib $\log 0 = 0$, and $\log x = \log |x|$ for real $x$. So the formula holds for $q = 0$ as a statement about junk values. The source applies it only to $q \neq 0$.

**Lemma (Norms of algebraic numbers).** Let $F$ be an algebraically closed normed field of characteristic $0$ with the cardinality of $\mathbb{C}$. Let $H \in \mathbb{C}$ be algebraic of degree $n$, and let $b \in \mathbb{R}$ with $\|\iota H\| \leq e^b$ for every isomorphism of fields $\iota\colon \mathbb{C} \cong F$. Then the norm $N(H) \in \mathbb{Q}$ of $H$ from $\mathbb{Q}(H)$ to $\mathbb{Q}$ satisfies $\|N(H)\|_F \leq e^{nb}$.

Lean: `New.HeightLe.norm_algebraMap_norm_gen_le` (New/Reduction/Lattices/Heights.lean).

*Proof.* In $F$, the norm $N(H)$ is the product of the images of $H$ under the $n$ embeddings $\mathbb{Q}(H) \to F$. Each embedding extends to an isomorphism $\iota\colon \mathbb{C} \cong F$. So each factor has norm at most $e^b$. $\square$

The lemma is applied with $F = \mathbb{C}$, where the isomorphisms are the automorphisms $\sigma$, and with $F = \bar{\mathbb{Q}}_\ell$.

**Theorem (The height of 1).** If the constant family $1$ has height at most $c$, then $c \geq 0$.

Lean: `New.HeightLe.nonneg_of_one` (New/Reduction/Lattices/Heights.lean).

*Proof.* Take $H$, $\alpha$ and $h$ from the definition. Condition 2 says $\|\iota H\| \leq \ell^{h(\ell)} = e^{h(\ell)\log\ell}$ for every $\iota \mid \ell$. At $\ell = 2$ the bound does not depend on $\iota$. So $H$ is algebraic, by the algebraicity criterion. Let $n = [\mathbb{Q}(H) : \mathbb{Q}]$ and $q = N(H) \in \mathbb{Q}$. Then $q \neq 0$, since $H \neq 0$. The lemma on norms gives
$$\log |q| \leq n\alpha, \qquad \log |q|_\ell \leq n\, h(\ell) \log \ell \text{ for every prime } \ell.$$
Let $B = |\mathrm{num}(q)| + \mathrm{den}(q) + 1$, and let $U$ be the set of primes less than $B$. By the product formula,
$$0 = \log |q| + \sum_{\ell \in U} \log |q|_\ell \leq n \Big( \alpha + \sum_{\ell \in U} h(\ell) \log \ell \Big) \leq nc.$$
Since $n \geq 1$, $c \geq 0$. $\square$

This step replaces Liouville's "a nonzero integer has absolute value at least $1$".

**Corollary (A nonzero number is not small everywhere).** Let $z \in \mathbb{C}$, $z \neq 0$. Suppose that the constant family $z$ has height at most $c$, and that $|\sigma z| \leq e^{c'}$ for every automorphism $\sigma$ of $\mathbb{C}$. Then $-c \leq c'$.

Lean: `New.HeightLe.neg_le_of_norm_map_le` (New/Reduction/Lattices/Heights.lean).

*Proof.* The constant family $z^{-1}$ has height at most $c'$, by the lemma on inverses. So the constant family $z^{-1} z = 1$ has height at most $c' + c$. Apply the theorem on the height of $1$. $\square$

For $z = 1/2$, with $c = \log 2$ and $c' = -\log 2$, the corollary is an equality. So the bound $\log 2$ in the example is the least one.

**Remark (Formalization).** The source works with all automorphisms of $\mathbb{C}$ and all isomorphisms $\mathbb{C} \cong \bar{\mathbb{Q}}_\ell$, and never with the places of a fixed number field. The cost is the axiom of choice and the step at $\ell = 2$ in the proof above, which derives that $H$ is algebraic. The gain is that the Gram determinants of the source need no field of definition. The textbook product formula over a number field (Neukirch, *Algebraic Number Theory*, Chapter III, §1) is not used. The norm to $\mathbb{Q}$ takes its place.
