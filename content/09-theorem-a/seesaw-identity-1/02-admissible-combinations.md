---
title: Admissible combinations
lean:
  - New/UpperBound/Seesaw/AdmissibleCombinations.lean
decls:
  - New.Seesaw.integralAway
  - New.Seesaw.IsAdmissibleCoeffs
  - New.Seesaw.IsAdmissibleCombination
  - New.Seesaw.IsAdmissibleCombination.of_sum
  - New.Seesaw.IsAdmissibleCombination.single
  - New.Seesaw.IsAdmissibleCombination.bind
  - New.Seesaw.IsAdmissibleCombination.map
  - New.Seesaw.IsAdmissibleCombination.smul
  - New.Seesaw.IsAdmissibleCombination.of_eq_isOfFinOrder_smul
  - New.Seesaw.IsAdmissibleCombination.map_bilinear
  - New.Seesaw.IsAdmissibleCombination.pure
  - New.Seesaw.IsAdmissibleCombination.smul_mem
  - New.Seesaw.IsAdmissibleCombination.normUnit_smul
  - New.Seesaw.weightedTranslations
  - New.Seesaw.translations
  - New.Seesaw.isAdmissibleCombination_weil_vacElem
  - New.Seesaw.isAdmissibleCombination_schrodingerOp
  - New.Seesaw.div_mem_integralAway
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Admissible combinations

The end product of the seesaw is a vector of the form $\sum_x r(x)\, v(x)$: a finite combination of translated vacua, with coefficients that have a bounded denominator and a bounded sum of absolute values at every complex conjugate. Theorem A needs both bounds. The denominator enters the divisibility prime by prime, and the size enters the archimedean bound. This section sets up the bookkeeping. It defines admissible combinations, proves that they are stable under substitution, linear maps, bilinear maps and tensor products, and shows that the two basic operations of the finite Weil representation produce them.

### Integrality away from $n$

**Definition (Integral away from $n$).** For a natural number $n$, let $\mathcal{O}_{(n)} \subseteq \mathbb{C}$ be the set of complex numbers $z$ such that $\|\iota z\|_l \leq 1$ for every prime $l$ coprime to $n$ and every ring homomorphism $\iota : \mathbb{C} \to \mathbb{C}_l$.

Lean: `New.Seesaw.integralAway` (New/UpperBound/Seesaw/AdmissibleCombinations.lean).

It is a subring of $\mathbb{C}$, because each $\iota$ is a ring homomorphism and the norm of $\mathbb{C}_l$ is ultrametric. An algebraic integer lies in $\mathcal{O}_{(n)}$ for every $n$. A rational number $a/b$ in lowest terms lies in $\mathcal{O}_{(n)}$ if and only if every prime factor of $b$ divides $n$. A transcendental number lies in no $\mathcal{O}_{(n)}$, since a field automorphism can send it to $1/l$ for any prime $l$ and $\mathbb{C} \cong \mathbb{C}_l$.

**Lemma.** If $c \mid d\, q^k$ for natural numbers $c, d, q, k$, then $d/c \in \mathcal{O}_{(q)}$.

Lean: `New.Seesaw.div_mem_integralAway`.

*Proof.* Write $d q^k = c e$. Then $d/c = e / q^k$, and $1/q$ is an $l$-adic unit for each prime $l$ coprime to $q$. $\square$

### Admissible coefficients and combinations

**Definition (Admissible coefficients).** Let $A$ be a set, $n, d \in \mathbb{N}$, $p$ a proposition and $B \in \mathbb{R}$. A finitely supported function $r : X \to \mathbb{C}$ is *admissible* for $(A, n, d, p, B)$ if:

1. the support of $r$ lies in $A$;
2. $d\, r(x) \in \mathcal{O}_{(n)}$ for every $x$;
3. if $p$ holds, then $\sum_x |\sigma(r(x))| \leq B$ for every field automorphism $\sigma$ of $\mathbb{C}$.

Lean: `New.Seesaw.IsAdmissibleCoeffs`.

**Definition (Admissible combination).** Let $v : X \to Z$ be a family of vectors in a complex vector space. A vector $z$ is an *admissible combination of the $v(x)$, $x \in A$, with denominator $d$ away from $n$ and size $B$ under $p$* if $z = \sum_x r(x)\, v(x)$ for an admissible $r$.

Lean: `New.Seesaw.IsAdmissibleCombination`.

The size is measured at all conjugates $\sigma$ at once. In the application the coefficients are algebraic, and $\sigma$ runs through the archimedean embeddings of the field they generate. The size bound then holds at every archimedean place, as part (a) of Theorem A needs.

**Remark (Formalization).** Three features of the definition are conventions. The denominator $d = 0$ is allowed, and then condition 2 says nothing, since $0 \in \mathcal{O}_{(n)}$; every statement of the chapter that clears a denominator assumes $d \neq 0$. The size bound is conditional on $p$. In the seesaw $p$ is the proposition $\vartheta.Q = \emptyset$, that the twist is unramified: for ramified twists the source tracks only the denominator, and the size $B$ is then arbitrary. Finally, an automorphism $\sigma$ of $\mathbb{C}$ need not be continuous; the definition quantifies over all of them, which is what makes the size bound hold at every conjugate of an algebraic coefficient.

**Example.** Let $v(1) = (1, 0)$ and $v(2) = (0, 1)$ in $\mathbb{C}^2$, and let $z = (\tfrac{1}{2}, \tfrac{\sqrt{2}}{2})$. Then $z = \tfrac12 v(1) + \tfrac{\sqrt 2}{2} v(2)$ is an admissible combination with denominator $2$ away from $1$ and size $\tfrac{1 + \sqrt 2}{2}$ under $p = \mathrm{True}$. The conjugate $\sigma(\sqrt 2) = -\sqrt 2$ gives the same sum of absolute values. With $n = 2$ the denominator can be taken to be $1$, since $1/2 \in \mathcal{O}_{(2)}$.

The first facts are immediate from the definition.

**Lemma.** Let $s$ be a finite set and $c : s \to \mathbb{C}$. If $d\, c(i) \in \mathcal{O}_{(n)}$ for $i \in s$, and $\sum_{i \in s} |\sigma(c(i))| \leq B$ under $p$ for every $\sigma$, then $\sum_{i\in s} c(i)\, v(i)$ is an admissible combination of the $v(i)$, $i \in s$, with denominator $d$ and size $B$. Each $v(x)$ with $x \in A$ is an admissible combination of size $1$ for every denominator.

Lean: `New.Seesaw.IsAdmissibleCombination.of_sum`, `New.Seesaw.IsAdmissibleCombination.single`.

*Proof.* For the first claim take $r = c$ extended by $0$; distinct indices $i$ give distinct points, so the sum over the support is at most the sum over $s$. For the second take $r = \delta_x$, with $d \cdot 1 \in \mathcal{O}_{(n)}$ and $|\sigma(1)| = 1$. $\square$

### Substitution

The main rule says that a combination of combinations is a combination, with the denominators and the sizes multiplied.

**Theorem (Substitution).** Let $z$ be an admissible combination of the $v(x)$, $x \in A$, with denominator $d$ and size $B$. Suppose that each $v(x)$, $x \in A$, is an admissible combination of the $v'(y)$, $y \in A'$, with denominator $d'$ and size $B'$. Let $d d' \mid e$, and let $B |B'| \leq C$ under $p$. Then $z$ is an admissible combination of the $v'(y)$, $y \in A'$, with denominator $e$ and size $C$.

Lean: `New.Seesaw.IsAdmissibleCombination.bind`.

*Proof.* Write $z = \sum_x c(x) v(x)$ with $c$ admissible, and for each $x$ in the support of $c$ choose admissible coefficients $r_x$ with $v(x) = \sum_y r_x(y) v'(y)$. Put $t = \sum_x c(x)\, r_x$, a finitely supported function on the index set of $v'$. Then $z = \sum_y t(y)\, v'(y)$ by linearity. We check the three conditions for $t$.

*Support.* If $t(y) \neq 0$, then $r_x(y) \neq 0$ for some $x$, so $y \in A'$.

*Denominator.* Write $e = d d' k$. Then $e\, t(y) = \sum_x k \cdot (d\, c(x)) \cdot (d'\, r_x(y))$, a sum of products of elements of the ring $\mathcal{O}_{(n)}$.

*Size.* Fix $\sigma$ and assume $p$. By the triangle inequality,

$$\sum_y |\sigma(t(y))| \leq \sum_y \sum_x |\sigma(c(x))|\, |\sigma(r_x(y))| = \sum_x |\sigma(c(x))| \sum_y |\sigma(r_x(y))| \leq \sum_x |\sigma(c(x))|\, |B'| \leq B |B'| \leq C. \quad \square$$

**Remark (Formalization).** The size is $B |B'|$, not $B B'$. When $p$ fails, the sizes are arbitrary real numbers, and $B'$ may be negative; the absolute value makes the bound correct in the second inequality, where $\sum_y |\sigma(r_x(y))| \leq B' \leq |B'|$. The sum over $y$ in the proof runs over the support of $t$, which is a subset of the union of the supports of the $r_x$. The choice of $r_x$ is made with `choose!`, which is harmless: any admissible $r_x$ works.

Five rules follow from substitution.

**Corollary.** Let $z$ be an admissible combination of the $v(x)$, $x \in A$, with denominator $d$ and size $B$.

1. For a linear map $L$, $L z$ is an admissible combination of the $L v(x)$ with the same data.
2. If $c \in \mathcal{O}_{(n)}$ and $|\sigma(c)| \leq 1$ for all $\sigma$ under $p$, then $c z$ is an admissible combination with the same data.
3. If each $v(x)$, $x \in A$, is $\zeta\, v'(y)$ for a root of unity $\zeta$ and some $y \in A'$, then $z$ is an admissible combination of the $v'(y)$, $y \in A'$, with the same data.
4. For a bilinear map $b$ and an admissible combination $z'$ of the $v'(y)$, $y \in A'$, with denominator $d'$ and size $B'$, the vector $b(z, z')$ is an admissible combination of the $b(v(x), v'(y))$, $(x, y) \in A \times A'$, with denominator $d d'$ and size $B|B'|$.
5. For a prime $l$ coprime to $n$ and a module $M$ over the ring of complex numbers that are integral under the chosen $\iota : \mathbb{C}\to\mathbb{C}_l$, if $v(x) \in M$ for all $x \in A$, then $d z \in M$.

Lean: `New.Seesaw.IsAdmissibleCombination.map`, `New.Seesaw.IsAdmissibleCombination.smul`, `New.Seesaw.IsAdmissibleCombination.of_eq_isOfFinOrder_smul`, `New.Seesaw.IsAdmissibleCombination.map_bilinear`, `New.Seesaw.IsAdmissibleCombination.smul_mem`.

*Proof.* (1) Apply $L$ to $z = \sum r(x) v(x)$. (2) By (1) with $L = c\cdot$, the vector $cz$ is a combination of the $c\, v(x)$; each $c\, v(x)$ is a combination of $v(x)$ with denominator $1$ and size $1$, and substitution gives the claim. (3) Each $v(x) = \zeta v'(y)$ is a combination of $v'(y)$ with coefficient $\zeta$; a root of unity is an algebraic integer, and $|\sigma(\zeta)| = 1$. Substitute. (4) Write $z' = \sum_y r'(y) v'(y)$. By (1) applied to the linear map $b(\cdot, z')$, the vector $b(z, z')$ is a combination of the $b(v(x), z')$. Each $b(v(x), z') = \sum_y r'(y)\, b(v(x), v'(y))$ is a combination of the $b(v(x), v'(y))$, $(x, y) \in \{x\} \times A'$, with denominator $d'$ and size $B'$. Substitute. (5) $d z = \sum_x (d r(x))\, v(x)$, and $d r(x)$ is integral under $\iota$ because $l$ is coprime to $n$. $\square$

**Theorem (Pure tensors).** For $i < m$ let $f_i$ be an admissible combination of the vectors $v_i(s, t)$, $(s, t) \in A_{2i} \times A_{2i+1}$, with denominator $d$ and size $B$, where the $A_j$ are additive groups. Then the pure tensor $f_{m-1}\otimes\cdots\otimes f_0$ is an admissible combination of the pure tensors $\bigotimes_{i<m} v_i(y_{2i}, y_{2i+1})$, over the families $y$ with $y_j \in A_j$ for all $j$, with denominator $d^m$ and size $|B|^m$.

Lean: `New.Seesaw.IsAdmissibleCombination.pure`.

*Proof.* Induction on $m$. For $m = 0$ the empty tensor is $1$, the value at the family $y = 0$; here the $A_j$ must contain $0$, which is why they are groups. For the step, rule (4) of the corollary, with $b$ the tensor product, gives $f_m \otimes (f_{m-1}\otimes\cdots\otimes f_0)$ as a combination indexed by pairs (a family $s$, a pair $t$), with denominator $d^m d$ and size $|B|^m |B|$. Merge the pair into the family, replacing the coordinates $2m$ and $2m+1$ of $s$ by $t$; the first $m$ factors do not see them. Rule (3) with $\zeta = 1$ ends the proof. $\square$

### Clearing the denominator

At the end of the seesaw the coefficients are rescaled to clear the denominator. The rescaling factor is a unit.

**Proposition (Clearing the denominator).** Let $d \neq 0$, $C, a \in \mathbb{C}$, and let $z$ be an admissible combination of the $C\, v(x)$, $x \in A$, with denominator $d$ and size $B$. Let $u = \mathrm{normUnit}(aC/d)$, that is, $u = d/(aC)$ if $aC \neq 0$ and $u = 1$ if $aC = 0$. Then $u\, a\, z$ is an admissible combination of the $v(x)$, $x \in A$, with denominator $1$ and size $dB$.

Lean: `New.Seesaw.IsAdmissibleCombination.normUnit_smul`.

*Proof.* Write $z = \sum_x r(x)\, C\, v(x)$ and $z_0 = \sum_x r(x) v(x)$. Then $u a z = (u a C)\, z_0$. The coefficients $d\, r$ show that $d z_0$ is a combination of the $v(x)$ with denominator $1$ and size $dB$, since $d\, r(x) \in \mathcal{O}_{(n)}$ and $\sum |\sigma(d r(x))| = d \sum |\sigma(r(x))|$. If $aC \neq 0$, then $u a C = d$ and $u a z = d z_0$. If $aC = 0$, then $u a z = 0 = 0 \cdot (d z_0)$, which is a combination by rule (2) with $c = 0$. $\square$

**Remark (Formalization).** On a field, $\mathrm{normUnit}(x) = x^{-1}$ for $x \neq 0$ and $\mathrm{normUnit}(0) = 1$. The proposition has content only when $aC \neq 0$. When $aC = 0$ it says that $0$ is a combination. In [part 2](/chapter/seesaw-identity-2/) this proposition is applied with $a = c_0$, the constant of the unfolding, and with $d = R^{2m}$, $R = M^{f n_m^2}$; the seesaw constant is $u^{-1}$, which is $c_0 C/d$ if $c_0 C \neq 0$ and $1$ otherwise. The remark on the seesaw constant in [Theorem A and its plan](/chapter/theorem-a-plan/) discusses the case $c_0 C = 0$.

### Translations

The vectors $v(x)$ of the seesaw are translates of a vacuum by finite adelic vectors $x$ with bounded denominators.

**Definition (Translations).** For $q \in \mathbb{N}$ and a family $d = (d_i)$ of finite adeles, the group of *weighted translations* consists of the finite adelic vectors $x$ such that $d_i x_i$ is integral at every finite place $w \nmid q$, for every $i$. There is no condition at the places above $q$. For a constant family $d_i = d$ it is the group of *translations* $\mathrm{Tr}(q, d)$.

Lean: `New.Seesaw.weightedTranslations`, `New.Seesaw.translations`.

The first source of admissible combinations is the Weil action of a finite unitary point on a translated vacuum. Let $V$ be a hermitian space with Weil representation $\omega$ on $\mathcal{S}(V)$, vacuum $\phi_0$ and finite Heisenberg operators $\rho(x)$ (Lean: `New.Space.finHeisenbergOp`), as in [the Weil representation](/chapter/weil-representation/). For $g$ in the finite unitary group, the multiplier is $\Delta(g) = \upsilon(\det u)|\det u|^{-1/2}$ with $u\hat{\mathcal{O}}^n = \hat{\mathcal{O}}^n \cap g^{-1}\hat{\mathcal{O}}^n$ (Lean: `New.finMultiplier`).

**Theorem (Moved vacua).** Let $g$ be a finite adelic unitary matrix and write $\Delta(g) = cC$. Let $A$ contain $g(x + \lambda)$ for every $\lambda \in \hat{\mathcal{O}}^n$. If $d\, c/|\Delta(g)|^2 \in \mathcal{O}_{(q)}$, then $\omega(1, g)\rho(x)\phi_0$ is an admissible combination of the vectors $C\rho(y)\phi_0$, $y \in A$, with denominator $d$ away from $q$ and size $1$ under any $p$ for which $|\sigma(c)| \leq 1$ for all $\sigma$.

Lean: `New.Seesaw.isAdmissibleCombination_weil_vacElem`.

*Proof.* Let $L = \hat{\mathcal{O}}^n$ and let $H = L \cap g^{-1}L$, a subgroup of $L$ of index $|\Delta(g)|^2$ (Lean: `New.norm_finMultiplier_sq`). The action of $g$ on the vacuum is a multiple of the sum of the translates of $\phi_0$ by $g\lambda$ over $\lambda \in L/H$, with the factor $\Delta(g)/[L : H]$ (Lean: `New.Space.omega_vacElem_sum`). Moving $\rho(x)$ through $\omega(1, g)$ and multiplying the Heisenberg operators gives

$$\omega(1, g)\rho(x)\phi_0 = \sum_{\lambda \in L/H} \frac{c}{|\Delta(g)|^2}\, \zeta(\lambda)\, C\, \rho\bigl(g(x + \lambda)\bigr)\phi_0,$$

with roots of unity $\zeta(\lambda)$, values of the self-dual additive character. The coefficient $a = c/|\Delta(g)|^2$ satisfies $d a \in \mathcal{O}_{(q)}$ by hypothesis. The number $|\Delta(g)|^2 = [L : H]$ is a positive integer, fixed by every $\sigma$, so $\sum_\lambda |\sigma(a)| = [L:H]\cdot |\sigma(c)|/[L:H] = |\sigma(c)| \leq 1$. So the sum is a combination of the $\zeta(\lambda) C\rho(g(x+\lambda))\phi_0$ with denominator $d$ and size $1$, and rule (3) removes the roots of unity. $\square$

The second source is the operator $\Psi\otimes$ of a function $\Psi$ on vectors modulo a modulus $\mathfrak{m}$ (Lean: `New.Space.schrodingerOp`), which is a combination of Heisenberg operators composed with the projection $\mathrm{proj}_{\mathfrak{m}}$ onto the vectors fixed by the integral translations at the places of $\mathfrak{m}$ (Lean: `New.Space.projOn`). [The objects of the upper bound](/chapter/upper-bound-objects/) builds the columns of the diagrams from these operators.

**Theorem (Values of $\Psi\otimes$).** Let $\mathfrak{m}$ be a modulus of $E$ with $g q \in \mathfrak{m}$ for some $g \in \mathcal{O}_E$ and $q \in \mathbb{N}$. Let $\Psi$ be a function on $(\mathcal{O}_E/\mathfrak{m})^n$ with values in $\mathcal{O}_{(q)}$, and let $\sum_x |\sigma(\Psi(x))| \leq B$ for all $\sigma$ under $p$. Let $v = \mathrm{proj}_{\mathfrak{m}}(u)$. Then $(\Psi\otimes)(u)$ is an admissible combination of the $\rho(y)v$, $y \in \mathrm{Tr}(q, \bar g)$, with denominator $N(g)^n$ away from $q$ and size $B$ under $p$.

Lean: `New.Seesaw.isAdmissibleCombination_schrodingerOp`.

*Proof.* Let $\delta_a$ be the point mass at a class $a$, so that $\Psi = \sum_a \Psi(a)\delta_a$ and $(\Psi\otimes)(u) = \sum_a \Psi(a)\,(\delta_a\otimes)(u)$. This is an admissible combination of the vectors $(\delta_a\otimes)(u)$ with denominator $1$ and size $B$, since $\Psi(a) \in \mathcal{O}_{(q)}$. Choose for each class $b$ an integral vector $z_b$ in it and put $y_b = \overline{\varpi^{-1} z_b}$ at the places of $\mathfrak{m}$ and $0$ elsewhere, with $\varpi$ the chosen generator of $\mathfrak{m}$. The operator of a point mass is a mean of translates (Lean: `New.Modulus.schrodingerOp_single_eq_mean_translate_projOn`):

$$(\delta_a\otimes)(u) = \frac{1}{|(\mathcal{O}_E/\mathfrak{m})^n|}\sum_b \psi'(-a\cdot b)\,\rho(y_b)\, v,$$

with roots of unity $\psi'(-a\cdot b)$. Since $gq \in \mathfrak{m}$, the vector $\bar g\, y_b$ is integral away from $q$ (Lean: `New.Seesaw.star_idem_smul_mem_translations`), so $y_b \in \mathrm{Tr}(q, \bar g)$. The number of vectors divides $N(g)^n q^k$ for some $k$ (Lean: `New.Seesaw.card_residueRing_pi_dvd`), so $N(g)^n/|(\mathcal{O}_E/\mathfrak{m})^n| \in \mathcal{O}_{(q)}$ by the lemma on $d/c$. The mean has $|(\mathcal{O}_E/\mathfrak{m})^n|$ terms, each with coefficient of absolute value $|(\mathcal{O}_E/\mathfrak{m})^n|^{-1}$ at every conjugate. So $(\delta_a\otimes)(u)$ is an admissible combination of the $\rho(y)v$ with denominator $N(g)^n$ and size $1$, after rule (3) removes the roots of unity. Substitution gives denominator $1\cdot N(g)^n$ and size $B\cdot 1$. $\square$

**Remark (Formalization).** The operator $\Psi\otimes$ is defined with coefficients chosen by `choose` from an existence statement for a generalized inverse (Lean: `New.Space.schrodingerOp`). The proof uses only the formula for point masses, which the source proves for the chosen operator. The theorem is the case $d = g$ of `New.Seesaw.isAdmissibleCombination_schrodingerOp_of_reduction`, which allows any integral $d$ with $dq \equiv 0 \bmod \mathfrak{m}$ and gives translations in $\mathrm{Tr}(q, \bar d)$.
