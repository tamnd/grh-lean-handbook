---
title: Shintani lifting in prime degree
lean:
  - Lib/LocalGL/Shintani/CosetRootChoice.lean
  - Lib/LocalGL/Shintani/CosetDescent.lean
  - Lib/LocalGL/Shintani/LiftingGreenCharacters.lean
decls:
  - New.GalSemidirect
  - New.galActionGL
  - New.HasFixedField
  - New.DescendsOnCoset
  - New.DescendsTo
  - New.HasCommonLift
  - New.Lift
  - New.IsRootChoice
  - New.exists_isRootChoice_GL
  - New.IsRootChoice.index_mul_finMean_eq_classInner
  - New.hasFixedField_iff_ne_one
  - New.DescendsTo.card_mul_classInner
  - New.DescendsTo.iff_comp_inl_eq_evalGL
  - New.Lift.mul
  - New.Lift.sub
  - New.Lift.mulMoebius
  - New.Lift.rankPart_mulMoebius_mul_constOne
  - New.Lift.evalGL_mem_virtualChars
  - New.Lift.exists_lift_of_descendsTo
  - New.induceClassFn
  - New.DescendsOnCoset.induce
  - New.exists_norm_char_semidirect
  - New.exists_torus_induced_descendsTo
  - New.exists_lift_brauerLift
  - New.IsIrreducibleChar.extend_semidirect
  - New.lift_detChar
  - New.evalGL_labelChar_map
  - New.exists_isChar_descendsTo_labelChar
  - New.shintani_lift_labelChar
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Shintani lifting in prime degree

Let $k'/k$ be an extension of finite fields with Galois group $\Gamma$. Shintani (J. Math. Soc. Japan 28 (1976), 396 to 414) proves that the norm map gives a bijection between the $\Gamma$-stable irreducible characters of $\mathrm{GL}_n(k')$ and the irreducible characters of $\mathrm{GL}_n(k)$. A stable character extends to $\mathrm{GL}_n(k') \rtimes \Gamma$, and on the coset of a generator of $\Gamma$ the extension is the corresponding character of $\mathrm{GL}_n(k)$ at the norm. The source proves one direction of this for the characters $\Xi_c$ of Section 5, when $[k' : k]$ is prime. This section also supplies the virtual lifts that Section 5 uses.

### Descent along a coset

Let $n$ be a finite set. The group $\Gamma$ acts on $\mathrm{GL}_n(k')$ entrywise. Let $E = \mathrm{GL}_n(k') \rtimes \Gamma$, with the product $(g, \sigma)(h, \tau) = (g \, \sigma(h), \sigma\tau)$, and let $\pi(g, \sigma) = \sigma$. Write $g$ for $(g, 1)$. For $s = (g, \sigma)$ and $\ell = \operatorname{ord} \sigma$, the power $s^\ell = (g \, \sigma(g) \cdots \sigma^{\ell - 1}(g), 1)$ is the classical norm.

**Definition (Descent and lifts).** Let $k_0$ be a field with a map to $k'$, either $k$ or $k'$. An element $\sigma \in \Gamma$ has *fixed field* $k_0$ if the image of $k_0$ is the set of elements of $k'$ fixed by $\sigma$. A function $\Phi : E \to \mathbb{C}$ *descends* to $X \in \mathcal{H}(k_0)$ if, for every $\sigma$ with fixed field $k_0$, every $s \in E$ with $\pi(s) = \sigma$ and every $\gamma \in \mathrm{GL}_n(k_0)$ with $s^{\operatorname{ord}\sigma} = \gamma$, we have $\Phi(s) = X([\gamma])$. Let $Z$ be a commutative semiring with a map to $\mathbb{C}$. Then $F \in \mathcal{H}(k)$ *lifts* to $F' \in \mathcal{H}(k')$ over $Z$ if, for every $m \geq 0$, some $Z$-combination $\Phi$ of characters of $\mathrm{GL}_m(k') \rtimes \Gamma$ descends both to $F$ and to $F'$.

Lean: `New.galActionGL`, `New.GalSemidirect`, `New.HasFixedField`, `New.DescendsOnCoset`, `New.DescendsTo`, `New.HasCommonLift`, `New.Lift` (Lib/LocalGL/Shintani/CosetDescent.lean, Lib/LocalGL/Shintani/CosetRootChoice.lean).

So $\Phi$ is $F'$ on $\mathrm{GL}_m(k')$, and $F$ at the norm on the cosets of the generators of $\Gamma$. With $Z = \mathbb{N}$, $\Phi$ is a character.

### Descent keeps inner products

**Theorem (Descent keeps inner products).** Let $\sigma \in \Gamma$ have fixed field $k_0$, and put $G_0 = \mathrm{GL}_n(k_0)$ and $G' = \mathrm{GL}_n(k')$.

1. There is a map $r : G_0 \to E$ with these properties: $\pi(r(\gamma)) = \sigma$ and $r(\gamma)^{\operatorname{ord}\sigma} = \gamma$; $r(v\gamma v^{-1}) = v \, r(\gamma) \, v^{-1}$ for $v \in G_0$; every $x \in G'$ with $x \, r(\delta) \, x^{-1} = r(\gamma)$ lies in $G_0$; and the matrix part of $r(\gamma)$ lies in every $k'$-subalgebra of matrices that contains $\gamma$.
2. Let $h, h' : E \to \mathbb{C}$ be invariant under conjugation by $G'$, and let them descend on the coset of $\sigma$ to $f, f'$ on $G_0$. Then $|\Gamma|$ times the mean over $E$ of $\overline{h(s)} \, h'(s)$, taken as $0$ off the coset of $\sigma$, is $\langle f, f' \rangle_{G_0}$.
3. Let $[k' : k]$ be prime. Then $\sigma$ has fixed field $k$ if and only if $\sigma \neq 1$. If class functions $\Phi, \Psi$ on $E$ descend to $F, G \in \mathcal{H}(k)$, then
$$|\Gamma| \, \langle \Phi, \Psi \rangle_E = \langle \Phi|_{G'}, \Psi|_{G'} \rangle_{G'} + (|\Gamma| - 1) \langle F, G \rangle_{|n|}.$$

Lean: `New.IsRootChoice`, `New.exists_isRootChoice`, `New.exists_isRootChoice_GL`, `New.IsRootChoice.exists_conj_eq_of_map_eq`, `New.IsRootChoice.index_mul_finMean_eq_classInner`, `New.hasFixedField_iff_ne_one`, `New.DescendsTo.card_mul_classInner` (Lib/LocalGL/Shintani/CosetRootChoice.lean, Lib/LocalGL/Shintani/CosetDescent.lean, Lib/LocalGL/Shintani/LiftingGreenCharacters.lean).

*Proof.* 1. Let $\ell = \operatorname{ord}\sigma$ and $N = |G_0|$. Let $R = k'[C_N]$ be the group algebra of a cyclic group with generator $c$, with $\sigma$ acting on the coefficients. The unit $c$ is fixed by $\sigma$, and a norm theorem for finite rings gives a unit $z \in R$ with $z \, \sigma(z) \cdots \sigma^{\ell-1}(z) = c$. Evaluate at $c \mapsto \gamma$, and put $r(\gamma) = (z(\gamma), \sigma)$. Since $\gamma$ has entries in $k_0$, $\sigma(z(\gamma))$ is $(\sigma z)(\gamma)$, so $r(\gamma)^\ell = (\gamma, 1)$. The element $z(\gamma)$ is a polynomial in $\gamma$. This gives the equivariance and the last property. If $x \, r(\delta) \, x^{-1} = r(\gamma)$, then the $\ell$-th powers give $x \delta x^{-1} = \gamma$, so $x \, z(\delta) \, x^{-1} = z(\gamma)$. The first components give $x \, z(\delta) \, \sigma(x)^{-1} = z(\gamma)$. So $\sigma(x) = x$, and $x$ has entries in $k_0$.

2. Fix representatives $x$ of the cosets $x G_0$ in $G'$. The map $(x, \gamma) \mapsto x \, r(\gamma) \, x^{-1}$ into the coset of $\sigma$ is injective by the third property of $r$ and by $\ell$-th powers. Both sets have $|G'|$ elements, so it is a bijection. The value of $\overline{h} h'$ at $x \, r(\gamma) \, x^{-1}$ is $\overline{f(\gamma)} f'(\gamma)$. So the sum over the coset is $[G' : G_0] \sum_\gamma \overline{f(\gamma)} f'(\gamma)$. Divide by $|E| = |\Gamma| \, |G'|$.

3. In prime degree the only fields between $k$ and $k'$ are $k$ and $k'$. Split the mean over $E$ into the $|\Gamma|$ cosets. The coset of $1$ gives the first term. Each other coset gives $\langle F, G \rangle_{|n|}$ by 2. $\square$

### Closure of lifts

**Theorem (Closure of lifts).** Let $k'/k$ be an extension of finite fields, $Z$ a commutative semiring and $R$ a commutative ring, both with maps to $\mathbb{C}$.

1. A function $\Phi$ on $\mathrm{GL}_n(k') \rtimes \Gamma$ descends to $F' \in \mathcal{H}(k')$ if and only if $\Phi = F'$ on $\mathrm{GL}_n(k')$.
2. Over $Z$, $\mathbb{1}$ lifts to $\mathbb{1}$, the unit $1$ lifts to $1$, and if $F, G$ lift to $F', G'$, then $F * G$ lifts to $F' * G'$.
3. Over $R$, if $F, G$ lift to $F', G'$, then $F - G$ lifts to $F' - G'$, $F\mu$ lifts to $F'\mu$, and $(-1)^m [F\mu * \mathbb{1}]_m$ lifts to $(-1)^m [F'\mu * \mathbb{1}]_m$.
4. If one $Z$-combination of characters in rank $m$ descends to $F$ and to $F'$, then $[F]_m$ lifts to $[F']_m$.
5. If, for every $m$, some $Z$-combination of characters of $\mathrm{GL}_m(k') \rtimes \Gamma$ descends to $F$, then $F$ lifts to some $F' \in \mathcal{H}(k')$.
6. If $F$ lifts to some $G$ along the trivial extension $k/k$, then $F$ on $\mathrm{GL}_n(k)$ is a $Z$-combination of characters, for every $n$.

Lean: `New.DescendsTo.iff_comp_inl_eq_evalGL`, `New.Lift.lift_constOne`, `New.Lift.one`, `New.Lift.mul`, `New.Lift.sub`, `New.Lift.mulMoebius`, `New.Lift.rankPart_mulMoebius_mul_constOne`, `New.Lift.rankPart_of_hasCommonLift`, `New.Lift.exists_lift_of_descendsTo`, `New.Lift.evalGL_mem_virtualChars`, `New.induceClassFn`, `New.DescendsOnCoset.induce`, `New.DescendsTo.induceClassFn_parabolic` (Lib/LocalGL/Shintani/CosetDescent.lean, Lib/LocalGL/Shintani/CosetRootChoice.lean).

*Proof.* 1. Only $\sigma = 1$ has fixed field $k'$.

2. The trivial character descends to $\mathbb{1}$. For the product, fix $m$ and $a \leq m$. Let $P_a \subseteq E$ be the elements whose matrix part is block upper triangular with blocks of sizes $a$ and $m - a$. It contains $(1, \sigma)$ for every $\sigma$. The diagonal blocks map $P_a$ to the groups of the blocks. Pull back the lifts of $F$ in rank $a$ and of $G$ in rank $m - a$, multiply them, and induce from $P_a$ to $E$. Frobenius reciprocity shows that induction keeps $Z$-combinations of characters. Descent commutes with induction. The proof uses a root choice $r$ for $E$ and its restriction to $P_a$. The roots of block triangular elements are block triangular, by the last property of $r$, since block triangular matrices form a subalgebra. On $\mathrm{GL}_m(k)$, the parabolic induction from the blocks gives $[F]_a * [G]_{m-a}$. Sum over $a$, the dimension of the stable subspace.

3. A difference of combinations descends to the difference. The function $J_N = \mu - (1 - \mathbb{1})^N \mu$ satisfies $J_0 = 0$ and $J_{N+1} = J_N - (\mathbb{1} * J_N - 1)$, so it lifts to itself by 2 and induction. It agrees with $\mu$ in dimension less than $N$, since $(1 - \mathbb{1})^N$ vanishes there. So $\mu$ lifts to $\mu$. Products of characters are characters, and descent is pointwise, so $F\mu$ lifts to $F'\mu$. For the last claim use $-X = X - X - X$ when $m$ is odd.

4. In rank $m$ use the given combination, and in the other ranks use $0$.

5. The restriction of the combination $\Phi_m$ to $\mathrm{GL}_m(k')$ is a class function. Let $F'$ be this function on the classes of dimension $m$, for each $m$.

6. A combination $\Phi$ that descends to $F$ along $k/k$ is $F$ on $\mathrm{GL}_n(k)$, by 1. $\square$

### Virtual lifts of eigenvalue sums

**Theorem (Lifts of eigenvalue sums).** Let $k'/k$ be an extension of finite fields of any degree, $K$ an algebraically closed field over $k'$, and $\theta$ a multiplicative character of $K$.

1. Let $S$ be a finite monoid, let $\Gamma$ act on $S^\times$, and let $\nu : S \to \mathbb{C}$ be multiplicative. Then $\vartheta(s) = \prod_{\tau \in \Gamma} \nu(\tau(s_1))$ on $S^\times \rtimes \Gamma$, with $s_1$ the component in $S^\times$, is a character. If $\sigma$ has fixed field $k$, $\pi(s) = \sigma$ and $s^{\operatorname{ord}\sigma} = u \in S^\times$, then $\vartheta(s) = \nu(u)$.
2. Let $L$ be a finite field over $k$ with $[L : k] = m$, and $\varphi : k' \otimes_k L \to K$ a $k'$-algebra map. There is a character $\Phi$ of $\mathrm{GL}_m(k') \rtimes \Gamma$ that descends to $C_\theta \mu$ over $k$. It also descends to every $X \in \mathcal{H}(k')$ with
$$\langle X, Y \rangle_m = \frac{1}{|A^\times|} \sum_{t \in A^\times} \overline{\theta\big(\varphi(\textstyle\prod_{\tau} (\tau \otimes 1)(t))\big)} \, Y([m_t]) \quad \text{for all } Y \in \mathcal{H}(k'), \qquad A = k' \otimes_k L.$$
3. The eigenvalue sum $\beta_\theta$ over $k$ lifts over $\mathbb{Z}$ to some $B \in \mathcal{H}(k')$.

Lean: `New.exists_norm_char_semidirect`, `New.simClassOf_leftMulMatrix`, `New.exists_torus_induced_descendsTo`, `New.exists_lift_brauerLift` (Lib/LocalGL/Shintani/CosetDescent.lean).

*Proof.* 1. The twist in $(a, \sigma)(b, \tau) = (a \, \sigma(b), \sigma\tau)$ only permutes the factors, so $\vartheta$ is a homomorphism to $\mathbb{C}^\times$. If $\sigma$ has fixed field $k$, then $\sigma$ generates $\Gamma$, and the product over $\tau$ is the product over $\sigma^i$, $i < \operatorname{ord}\sigma$. That is $\nu$ of the first component of $s^{\operatorname{ord}\sigma}$.

2. A basis of $L$ over $k$ is a basis of $A$ over $k'$. The matrix of left multiplication embeds $A^\times \rtimes \Gamma$ in $\mathrm{GL}_m(k') \rtimes \Gamma$, and $\Gamma$ acts on the coordinates. Let $\Phi$ be the character induced from $\vartheta$ of 1, with $\nu = \theta \circ \varphi$. If $\sigma$ has fixed field $k$, the units of $A$ fixed by $\sigma$ are $L^\times$. By 1 and the commutation of descent with induction, $\Phi$ descends to the function on $\mathrm{GL}_m(k)$ induced from $\theta \circ \varphi$ on the torus $L^\times$. By [the theorem on the inner product with $B\mu$](/decl/New.rankInner_greenCuspidal_mulMoebius/), and since $\mu$ is real, this is $C_\theta\mu$ in rank $m$. On $\mathrm{GL}_m(k')$, $\Phi$ is induced from $t \mapsto \theta(\varphi(\prod_\tau (\tau \otimes 1)(t)))$ on $A^\times$, and its pairings are the means of the hypothesis.

3. By 2 with $L$ of degree $m + 1$ in each rank $m + 1$, and since $C_\theta$ vanishes in rank $0$, part 5 of the closure theorem gives a lift $I$ of $C_\theta\mu$. Recall that $C_\theta = (\beta_\theta\mu) * \mathbb{1}$ and $C_\theta * \mathbb{1} = -\beta_\theta$, by [the cuspidality theorem](/decl/New.Hall.greenCuspidal_mul_constOne/). Put $J_0 = \mathbb{1}$ and
$$J_{N+1} = \big(C_\theta \mu - (J_N * \mathbb{1} - J_N)\mu\big) * \mathbb{1}.$$
Each $J_N$ lifts, by the closure theorem and the lift $I$. By induction, $C_\theta + J_N$ vanishes in dimension less than $N$. Indeed, if this holds for $N$, then $(C_\theta + J_N) * (1 - \mathbb{1})$ vanishes in dimension less than $N + 1$, and this product is $C_\theta + J_N + \beta_\theta - J_N * \mathbb{1}$. So $C_\theta + J_{N+1} = ((\beta_\theta + C_\theta + J_N - J_N * \mathbb{1})\mu) * \mathbb{1}$ vanishes there too. In rank $m$, the lift of $J_{m+1}$ descends to $-C_\theta$. So $-C_\theta$ lifts, by part 5, and $\beta_\theta = (-C_\theta) * \mathbb{1}$ lifts. $\square$

### Extension of a stable character

**Theorem (Extension of a stable character).** Let $G$ and $\Gamma$ be finite groups with an action of $\Gamma$ on $G$. Let $Y$ be an irreducible character of $G$ in the sense of [Section 5](/decl/New.IsLabel.isIrreducibleChar_labelChar/), with $Y(\sigma(g)) = Y(g)$. Let $\Phi$ be a $\mathbb{Z}$-combination of characters of $G \rtimes \Gamma$ and $m \in \mathbb{Z}$, with
$$|\Gamma| \, \langle \Phi, \Phi \rangle = \langle \Phi|_G, \Phi|_G \rangle + |\Gamma| - 1, \qquad \langle Y, \Phi|_G \rangle = 1 + |\Gamma| \, m.$$
Then the function $f$ equal to $Y$ on $G$ and to $\Phi$ off $G$ is an irreducible character of $G \rtimes \Gamma$.

Lean: `New.IsIrreducibleChar.extend_semidirect`, `New.finMean_ite` (Lib/LocalGL/Shintani/CosetRootChoice.lean).

*Proof.* For a function equal to $u$ on $G$ and $w$ off $G$, the mean over $G \rtimes \Gamma$ is the mean of $w$ plus $|\Gamma|^{-1}$ times the difference of the means of $u$ and $w$ over $G$. So
$$\langle f, f \rangle = \langle \Phi, \Phi \rangle + \frac{1 - \langle \Phi|_G, \Phi|_G \rangle}{|\Gamma|} = 1.$$
The function $f$ is a class function, since $Y$ is stable. Write $f = \sum_\chi a_\chi \chi$ over the irreducible characters $\chi$ of $G \rtimes \Gamma$. Let $I$ be $Y$ on $G$ and $0$ off $G$. Then $\langle \chi, I \rangle = \langle \chi|_G, Y \rangle / |\Gamma|$ and $\langle f, I \rangle = 1/|\Gamma| \neq 0$.

Let $\chi$ meet $Y$, that is, $\langle \chi|_G, Y \rangle \neq 0$. Since $Y$ is stable under conjugation in $G \rtimes \Gamma$, Clifford's theorem (Isaacs, *Character Theory of Finite Groups*, Theorem 6.2) gives $\chi|_G = N Y$ with $N \in \mathbb{N}$. Then
$$a_\chi = \langle \chi, f \rangle = \langle \chi, \Phi \rangle + \frac{N - N(1 + |\Gamma| m)}{|\Gamma|} = \langle \chi, \Phi \rangle - N m \in \mathbb{Z}.$$
Since $\langle f, I \rangle \neq 0$, some $\chi$ that meets $Y$ has $a_\chi \neq 0$. Then $|a_\chi| \geq 1$, and $\sum |a_\chi|^2 = 1$ gives $f = \pm\chi$. Since $f(1) = Y(1) > 0$, $f = \chi$. The other clauses follow as in Section 5. The source proves $\chi|_G = N Y$ from clause 3 for $Y$. $\square$

### The lift of Green's characters

**Theorem (Shintani lift).** Let $k'/k$ be an extension of finite fields, and let $(K, T)$ be faithful, with $k \subseteq k' \subseteq K$.

1. Let $\chi, \chi'$ be characters of $k^\times$ and $k'^\times$ whose names agree, $x_{\chi'} = x_\chi$. Then $\chi \circ \det$ lifts to $\chi' \circ \det$ over $\mathbb{N}$.
2. Let $\sigma \in \Gamma$ and let $c$ be a label over $k'$. Then $\Xi_c(\sigma(g)) = \Xi_{\sigma(c)}(g)$ for $g \in \mathrm{GL}_n(k')$.
3. Let $[k' : k]$ be prime, and let $c$ be a label over $k$. Then $\Xi_c$ lifts over $\mathbb{N}$ to $\Xi_c$ formed over $k'$.

Lean: `New.lift_detChar`, `New.evalGL_detChar`, `New.evalGL_labelChar_map`, `New.natDegree_dvd_iff_of_common_root`, `New.exists_rankInner_labelChar_eq_finMean`, `New.exists_isChar_descendsTo_labelChar`, `New.shintani_lift_labelChar` (Lib/LocalGL/Shintani/LiftingGreenCharacters.lean).

*Proof.* 1. Let $x = x_\chi$ and $\nu(g) = \theta_x(\det g)$, with $\theta_x$ formed with $q$. Part 1 of the theorem on eigenvalue sums gives a character that descends to $\chi \circ \det$ over $k$. On $\mathrm{GL}_m(k')$ its value is $\theta_x$ at the norm of $\det g$, which is $\theta_x$ formed with $|k'|$ at $\det g$, by [the rules for names](/decl/New.thetaChar_eq_apply_norm_pow/). That is $\chi'(\det g)$.

2. View $k'$ as an extension of itself through $\sigma$, with trivial Galois group. An induction over the factors of $c$ lifts $\Xi_{\sigma(c)}$ to $\Xi_c$, and the values at $\sigma(g)$ give the claim.

3. Lifts multiply, so it suffices to treat an irreducible label $P$ of degree $d$. If $P = X - 1$, then $\Xi_P = [\mathbb{1} \circ \det]_1$ by [orthonormality](/decl/New.rankInner_labelChar/), and 1 with part 4 of the closure theorem applies. Otherwise $P(1) \neq 0$. Let $x$ be a root of $P$, $\theta = \theta_x$ formed with $q^d$, and $Y = \Xi_P = (-1)^d [C_\theta]_d$ by [the theorem on $\tau_P$](/decl/New.greenTau_eq/). Let $Y' = \Xi_P$ over $k'$. It is an irreducible character, and it is $\Gamma$-stable by 2, since $\sigma$ fixes $P$.

Over $k'$, $P$ splits into irreducible factors with roots $x^{q^{a_j}}$, and $k' \otimes_k L$ is a product of copies of $k'(x)$, for $L$ of degree $d$. The mean of Section 4, applied to each factor, has the form in part 2 of the theorem on eigenvalue sums. This gives a character $J$ of $\mathrm{GL}_d(k') \rtimes \Gamma$ that descends to $C_\theta\mu$ over $k$ and to $(-1)^d Y'\mu$ over $k'$. Let $\beta$ be a combination that descends to $\beta_\theta$ and to its lift $B$. Let $\Phi$ descend to $(-1)^d[\beta_\theta\mu * \mathbb{1}]_d = Y$ and to $C = (-1)^d [B\mu * \mathbb{1}]_d$, by the closure theorem. Put $N = \langle J, \beta \rangle \in \mathbb{Z}$.

Part 2 of orthonormality, with $P(1) \neq 0$, gives $\langle C_\theta\mu, \beta_\theta \rangle_d = (-1)^d \langle Y, \beta_\theta\mu * \mathbb{1} \rangle_d = \langle Y, Y \rangle_d = 1$, and likewise $\langle (-1)^d Y'\mu, B \rangle_d = \langle Y', C \rangle_d$. The inner product formula for $J$ and $\beta$ gives $|\Gamma| N = \langle Y', C \rangle_d + |\Gamma| - 1$. So
$$\langle Y', \Phi|_{\mathrm{GL}_d(k')} \rangle = 1 + |\Gamma| (N - 1).$$
The same formula for $\Phi$ with itself gives $|\Gamma| \langle \Phi, \Phi \rangle = \langle \Phi|, \Phi| \rangle + |\Gamma| - 1$, since $\langle Y, Y \rangle_d = 1$. The extension theorem gives an irreducible character $\Psi$, equal to $Y'$ on $\mathrm{GL}_d(k')$ and to $\Phi$ off it. On the cosets of $\sigma \neq 1$, which have fixed field $k$, $\Psi = \Phi$ descends to $Y$. So $[Y]_d = Y$ lifts to $[Y']_d = Y'$ by part 4 of the closure theorem. $\square$

**Remark (Formalization).** The degree $[k' : k]$ must be prime. Only the $\Xi_c$ with squarefree labels and the characters $\chi \circ \det$ are lifted. The statement $\mathrm{Lift}\ \mathbb{N}$ gives a character in each rank, possibly of the zero representation, and it records neither irreducibility nor a bijection. In the ranks other than $\deg c$, the lift is the zero character. The lift $B$ of $\beta_\theta$ is not identified with the eigenvalue sum over $k'$. In a degree that is not prime, descent says nothing on the cosets of the $\sigma$ whose fixed field lies strictly between $k$ and $k'$. The source writes induction with conjugation by $\mathrm{GL}_n(k')$ only, divided by the index of the kernel of $\pi$ in the subgroup. For a subgroup that meets every coset of $\mathrm{GL}_n(k')$, this is the usual induced class function.
