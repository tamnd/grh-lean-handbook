---
title: The model case
lean:
  - New/Reduction/Lattices/Heights.lean
decls:
  - New.log_product_formula
  - New.HeightLe.nonneg_of_one
  - New.HeightLe.neg_le_of_norm_map_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The model case

Every lower bound in Volume 11 comes from one fact: a nonzero algebraic number cannot be small at every place. This section states the fact in the textbook form, then in the form of the source, and proves the second form. The rest of the volume produces one nonzero number, a Gram determinant, and bounds it at every place.

### A nonzero algebraic integer

Let $\alpha \neq 0$ be an algebraic integer of degree $n$, with conjugates $\alpha_1, \dots, \alpha_n$ in $\mathbb{C}$. The norm $N(\alpha) = \alpha_1 \cdots \alpha_n$ is a nonzero rational integer. So $|N(\alpha)| \geq 1$, and

$$\sum_{i=1}^n \log|\alpha_i| \geq 0.$$

So the conjugates cannot all be small. If $|\alpha_i| \leq e^{c'}$ for every $i$, then $n c' \geq 0$, so $c' \geq 0$. This is Liouville's argument in its simplest form.

Now let $\alpha \neq 0$ be algebraic, but not integral. Suppose that $H\alpha$ is integral for a nonzero integer $H$, and that $|\alpha_i| \leq e^{c'}$ for every $i$. Then $H\alpha$ is a nonzero algebraic integer whose conjugates are at most $|H| e^{c'}$. So $\log|H| + c' \geq 0$. The denominator $H$ pays for the smallness. In the language of heights: if the denominators of $\alpha$ cost at most $h$, then $-h \leq c'$.

The argument needs integrality at every prime at once. The source asks for less: at each prime $\ell$ it gives a bound for $\alpha$ in an $\ell$-adic absolute value, and the bounds at different primes may come from different arguments. The product formula joins them.

### The product formula

The textbook form is this. Let $K$ be a number field and $\alpha \in K^\times$. For each place $v$ of $K$ let $|\cdot|_v$ be the normalized absolute value. Then $|\alpha|_v = 1$ for all but finitely many $v$, and $\prod_v |\alpha|_v = 1$. This is the product formula of Neukirch, *Algebraic Number Theory*, Chapter III, §1, and of Bombieri and Gubler, *Heights in Diophantine Geometry*, Section 1.4. The source uses only the case $K = \mathbb{Q}$. It reduces a number of higher degree to $\mathbb{Q}$ by the norm.

**Theorem (The product formula for the rationals).** Let $q \in \mathbb{Q}$, and let $M \in \mathbb{N}$ exceed the absolute value of the numerator of $q$ and the denominator of $q$. Then

$$\log|q| + \sum_{p < M,\ p \text{ prime}} \log|q|_p = 0.$$

Lean: `New.log_product_formula` (New/Reduction/Lattices/Heights.lean).

*Proof.* Factor the numerator and the denominator into primes. All their prime factors are less than $M$. The term of $p$ in $\log|q|$ is $v_p(q)\log p$, and $\log|q|_p = -v_p(q)\log p$. The terms cancel. $\square$

**Remark (Formalization).** The statement holds for all $q$, also for $q = 0$. In Lean $\log 0 = 0$, and $|0|_p = 0$, so every term is $0$. This is a junk value. The source never applies the formula to $0$: it applies it to the norm of a number that it has shown to be nonzero.

### Heights of families

The source does not work with one algebraic number. It works with a family $y = (y_\iota)$ of complex numbers, one for each pair $\iota$ of a prime $\ell$ and an isomorphism of fields $\iota\colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$. A family has [height at most $c$](/decl/New.HeightLe/) if there are $H \in \mathbb{C}$ with $H \neq 0$, a real number $\alpha$, and real numbers $h(\ell) \geq 0$ such that $|\sigma H| \leq e^\alpha$ for every automorphism $\sigma$ of $\mathbb{C}$, $\|\iota(H y_\iota)\| \leq \ell^{h(\ell)}$ for every $\iota$ above $\ell$, and $\alpha + \sum_{\ell \in T} h(\ell)\log\ell \leq c$ for every finite set $T$ of primes. The definition is in [the chapter on twisted lattices](/chapter/twisted-lattices/).

The point of the family is that $y_\iota$ may depend on $\iota$. In Theorem C, $y_\iota$ is a ratio $Z(1)/Z(\xi_\iota)$ for a twist $\xi_\iota$ chosen at the prime of $\iota$. One multiplier $H$ serves all $\iota$ at once. So a height bound is a statement about all primes together, although each prime has its own witness.

**Theorem (The height of 1).** If the constant family $1$ has height at most $c$, then $0 \leq c$.

Lean: `New.HeightLe.nonneg_of_one` (New/Reduction/Lattices/Heights.lean).

*Proof.* Take $H$, $\alpha$ and $h$ from the definition. The bound $\|\iota H\| \leq \ell^{h(\ell)}$ at every $\iota$ above $\ell$ shows that $H$ is algebraic (the theorem on algebraicity from $\ell$-adic bounds in [twisted lattices](/chapter/twisted-lattices/)). Let $n$ be its degree and $q \in \mathbb{Q}$ its norm from $\mathbb{Q}(H)$. Then $q \neq 0$. At every place $q$ is a product of $n$ conjugates of $H$. So $\log|q| \leq n\alpha$, and $\log|q|_\ell \leq n\,h(\ell)\log\ell$ for each prime $\ell$. Take $M$ larger than the numerator and the denominator of $q$. The product formula for the rationals gives $0 \leq n\alpha + \sum_{\ell < M} n\,h(\ell)\log\ell \leq n c$. As $n \geq 1$, $c \geq 0$. $\square$

**Theorem (A nonzero number is not small everywhere).** Let $z \in \mathbb{C}$ with $z \neq 0$. Suppose that the constant family $z$ has height at most $c$, and that $|\sigma z| \leq e^{c'}$ for every automorphism $\sigma$ of $\mathbb{C}$. Then $-c \leq c'$.

Lean: `New.HeightLe.neg_le_of_norm_map_le` (New/Reduction/Lattices/Heights.lean).

*Proof.* The constant family $z^{-1}$ has height at most $c'$ ([the lemma on inverses](/decl/New.HeightLe.inv_const/)). The product of two families has height at most the sum of the heights ([products and powers](/decl/New.HeightLe.mul/)). So the constant family $z^{-1}z = 1$ has height at most $c' + c$. The height of 1 gives $0 \leq c' + c$. $\square$

This is the model case in the form that Theorem C uses. The number $z$ is a Gram determinant $G(1)$ of a basis. The archimedean bound $c'$ comes from Hadamard's inequality and the lengths of the vectors. The height bound $c$ comes from the integrality of the vectors after the twists $\xi_\iota$. The conclusion $-c \leq c'$ is the lower bound.

**Remark (Formalization).** The hypothesis $z \neq 0$ is needed. The constant family $0$ has height at most every $c$: take $H = 1$, $\alpha = c$ and $h = 0$. Then $\|\iota(H\cdot 0)\| = 0$. So a height bound for a family that may be $0$ gives no information. This is why the nonvanishing results of Section 5 matter: each lower bound in the volume needs a number that is proved to be nonzero.

### A determinant version

Here is the model case with a lattice. Let $y_1, \dots, y_d \in \mathbb{Q}^d$ be linearly independent. Suppose that $\|y_i\|^2 \leq e^{h}$ for every $i$, and that $Q y_i \in \mathbb{Z}^d$ for an integer $Q \geq 1$. The Gram determinant $G = \det(\langle y_i, y_k\rangle)$ is a nonzero rational number. Hadamard's inequality gives $G \leq e^{dh}$. Integrality gives $Q^{2d} G \in \mathbb{Z}$, so the constant family $G$ has height at most $2d\log Q$. The last theorem gives $-2d\log Q \leq dh$. With $c = dh$ as the covolume and $\delta = d\log Q$ as the index, this reads $0 \leq c + 2\delta$.

In the target lattice there are two changes. First, the integrality of a target form $y$ at $\iota$ is a condition on its twisted lifts $\Theta_\xi y$ for the twists $\xi$ allowed at the prime of $\iota$. Second, the lift $\Theta_\xi$ changes the volume by the factor $Z(\xi) = \det(\Theta_\xi^*\Theta_\xi)$. So the Gram determinant at $\iota$ is computed after a lift whose volume is $Z(\xi_\iota)$, and the model inequality gains the term $b_{\mathrm{volume}}$, a bound for the height of $Z(1)/Z(\xi_\iota)$. If this height is negative, then $c + 2\delta$ must be positive and large. Theorem C makes this precise.
