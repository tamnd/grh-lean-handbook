---
title: Coefficients at indices that are not negative
lean:
  - New/Determinant/Exchange/NegativeIndices.lean
decls:
  - New.Exchange.exists_unitary_mulVec_eq_single
  - New.Exchange.exists_unit_dotProduct_col_eq_zero
  - New.Exchange.exists_mem_maxCompactU_eq_rotation
  - New.Exchange.realPairWeil_rotation_polyVector
  - New.Exchange.eval_eq_zero_of_rotation_fixed
  - New.Exchange.apply_eq_zero_of_forall_fixed_eq_zero
  - New.Exchange.eq_zero_of_stabilizer_fixes_polyVector
  - New.Exchange.exists_isometry_fock_functional_eq_zero
  - New.Exchange.realPairWeil_mulSingle_mem_map_homogeneousSubmodule
  - New.Exchange.haar_map_mul_right_of_isCompact
  - New.Exchange.homSlice_pairWeil_stabilizer_mul
  - New.Exchange.integral_theta_pairWeil_stabilizer_eq_zero
  - New.Exchange.centreCoeff_eq_zero_of_not_representedBy
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Coefficients at indices that are not negative

Case (b) of a self-dual test pair asks for the vanishing of a coefficient at an index $T$ that the space $V'$ cannot represent at some real place. For the theta integrals of this chapter, $V'$ is negative definite at every real place. This section proves that a coefficient of a theta integral vanishes at every invertible $T$ that is not negative definite at some real place. The reason is a weight argument at that place: the stabiliser of a frame with Gram matrix $T$ contains a circle that acts on the Fock space with only positive weights.

Notation. For signs $s \colon n \to \{\pm 1\}$, $\operatorname{neg}(s)$ is the number of $k$ with $s_k = -1$. $U(s)$ is the unitary group of the diagonal form with entries $s$, and $K(s)$ is its maximal compact subgroup, the elements of $U(s)$ that are also unitary for the standard form. A matrix $T$ over the adeles is *represented by* signs $t'$ if at every real place it equals $c^* \operatorname{diag}(t') c$ for some $c$. The Fock space and the real Weil representation of the pair are those of [Volume 6](/chapter/weil-representation/), and the polynomial vectors are dense in it.

### Linear algebra at a real place

**Lemma.** Let $s_i = 1$, and let $x$ be a complex $n \times b$ matrix whose Gram matrix $x^* \operatorname{diag}(s) x$ is not of the form $-c^*c$. Then there are $u \in U(s)$ and a vector $v$ with $u x v = e_i$.

Lean: `New.Exchange.exists_unitary_mulVec_eq_single` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* The hermitian matrix $G = x^* \operatorname{diag}(s) x$ is not negative semidefinite, since a negative semidefinite hermitian matrix is $-c^*c$. So $v^* G v > 0$ for some $v$, and after scaling, $v^* G v = 1$. Then $xv$ and $e_i$ are vectors of length $1$ for $\operatorname{diag}(s)$, as $s_i = 1$. By Witt's theorem some $u \in U(s)$ maps $x v$ to $e_i$. $\square$

**Lemma.** Let $s_i = 1$ and $\operatorname{card} b + \operatorname{neg}(t) = \operatorname{neg}(s)$. Let $x v = e_i$, and let $y$ be any $n \times a$ matrix. There is a vector $r$ with $r \cdot r^{*} = 1$, $r_k = 0$ when $s_k \neq -1$, $r x = 0$, and $r y_j = 0$ for every column $j$ with $t_j = -1$.

Lean: `New.Exchange.exists_unit_dotProduct_col_eq_zero` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* The vectors supported on the negative signs form a space $N$ of dimension $\operatorname{neg}(s)$. On $N$ the conditions are $\operatorname{card} b$ equations $r x_j = 0$ and $\operatorname{neg}(t)$ equations $r y_j = 0$. They are not independent on $N$: for $r \in N$ the combination $\sum_j v_j\, r x_j = r e_i = r_i$ is $0$, as $s_i = 1$. So the equations have rank at most $\operatorname{card} b + \operatorname{neg}(t) - 1 < \operatorname{neg}(s)$, and the solution space in $N$ is not $0$. Normalize a nonzero solution. $\square$

**Lemma (Rotations).** Let $r$ be a unit vector supported on the negative signs of $s$, and $|\eta| = 1$. Then $c = 1 + (\bar\eta - 1)\, r^* r$ lies in $K(s)$.

Lean: `New.Exchange.exists_mem_maxCompactU_eq_rotation` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* $P = r^* r$ is a hermitian projection, and $\operatorname{diag}(s) P = P \operatorname{diag}(s) = -P$, as $r$ is supported on the negative signs. For a form $J$ with $JP = PJ = \varepsilon P$, expand $c^* J c$ with $c^* = 1 + (\eta - 1) P$. The terms in $P$ add up to $\varepsilon\,(\eta - 1 + \bar\eta - 1 + (\eta - 1)(\bar\eta - 1)) P = \varepsilon(\eta\bar\eta - 1) P = 0$. Apply this to $J = \operatorname{diag}(s)$ with $\varepsilon = -1$ and to $J = 1$ with $\varepsilon = 1$. $\square$

### The weight argument

The Fock space of the pair at the real places has polynomial vectors $\operatorname{vec}(P)$ for polynomials $P$ in variables $X_{w,k,j}$, with $w$ an infinite place, $k \in n$ and $j \in a$. An element of $K(s)$ at a place $\tau$ acts on them by a scalar times a linear substitution, by [the Fock model](/chapter/weil-representation/).

**Lemma.** Let $\mu_\tau + N = \operatorname{neg}(-t)$, the number of positive signs of $t$. Let $r$ and $c$ be as in the lemma on rotations. Then $c$, placed at $\tau$, maps $\operatorname{vec}(P)$ to $\eta^N \operatorname{vec}(P \circ \sigma)$, where $\sigma$ fixes the variables at the places $w \neq \tau$, and adds to $X_{\tau,k,j}$ the term $(\bar\eta - 1) r_k \sum_i \bar r_i X_{\tau,i,j}$ if $t_j = -1$, and the term $(\eta - 1)\bar r_k \sum_i r_i X_{\tau,i,j}$ if $t_j = 1$.

Lean: `New.Exchange.realPairWeil_rotation_polyVector` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* The block of $c$ on the positive signs is $1$, and the block on the negative signs is $1 + (\bar\eta - 1) P$, of determinant $1 + (\bar\eta - 1) = \bar\eta = \eta^{-1}$ by the formula for a rank one update. The scalar of the Fock model is a product of powers of these determinants and the weight factor; it is $\eta^N$. A variable moves by a column of $c$ if $s_k = t_j$, and by a row of $c^{-1} = 1 + (\eta - 1)P$ otherwise. This gives $\sigma$. $\square$

**Lemma.** Let $\mu_\tau < \operatorname{neg}(-t)$ and $r$ a unit vector supported on the negative signs of $s$. If all rotations $1 + \delta\, r^* r$ in $K(s)$, placed at $\tau$, fix $\operatorname{vec}(P)$, then $P(z) = 0$ at every point $z$ with $\sum_k \bar r_k z_{\tau,k,j} = 0$ for all $j$ with $t_j = -1$.

Lean: `New.Exchange.eval_eq_zero_of_rotation_fixed` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* Write $N = M + 1$. At such a point $z$, the substitution $\sigma$ moves $z$ to $z + (\eta - 1) z'$, where $z'$ is $0$ at the variables with $w \neq \tau$ or $t_j = -1$, since those added terms contain the vanishing sums. The fixed vector gives $P = \eta^{N} P \circ \sigma$, so $P(z) = g(\eta)$ for every $\eta$ on the unit circle, where $g(\eta) = \eta^{M+1} P(z + (\eta - 1) z')$ is a polynomial in $\eta$. The mean of $g$ over the unit circle is $g(0) = 0$, by the mean value property. The mean of the constant $P(z)$ is $P(z)$. So $P(z) = 0$. $\square$

**Lemma.** Let a compact group $G$ act by bounded operators $\rho(g)$ on a Banach space $V$. Let $W$ be a stable subspace of finite dimension in which only $0$ is fixed. Then an invariant bounded functional $l$ vanishes at every $v \in W$ with continuous orbit.

Lean: `New.Exchange.apply_eq_zero_of_forall_fixed_eq_zero` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* Let $m = \int_G \rho(g) v\, dg$ for the Haar probability measure. It lies in $W$, which is closed and convex. It is fixed, by the invariance of the measure. So $m = 0$, and $l(v) = \int l(\rho(g) v)\, dg = l(m) = 0$. $\square$

**Proposition.** Let $\mu_\tau < \operatorname{neg}(-t)$, $s_i = 1$, $\operatorname{card} b + \operatorname{neg}(t) = \operatorname{neg}(s)$ and $x v = e_i$. If every $c \in K(s)$ with $c x = x$, placed at $\tau$, fixes $\operatorname{vec}(P)$, then $P = 0$. Consequently, if the Gram matrix of $x$ is not of the form $-c^*c$, there is $u \in U(s)$ such that every functional on the Fock space invariant under the stabiliser of $u x$ in $K(s)$ at $\tau$ is $0$.

Lean: `New.Exchange.eq_zero_of_stabilizer_fixes_polyVector`, `New.Exchange.realPairWeil_mulSingle_mem_map_homogeneousSubmodule`, `New.Exchange.exists_isometry_fock_functional_eq_zero` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* Fix a point $z$. Apply the second lemma with $y_{kj} = \overline{z_{\tau,k,j}}$; it gives $r$. Every rotation $1 + \delta\, r^* r$ fixes $x$, since $r x = 0$, so by hypothesis it fixes $\operatorname{vec}(P)$. The choice of $r$ is the condition of the previous lemma at $z$, so $P(z) = 0$. As $z$ is arbitrary, $P = 0$. For the second statement choose $u$ by the first lemma, so $u x v = e_i$. The stabiliser $C$ of $u x$ in $K(s)$ is compact. Each $c \in C$ maps homogeneous polynomial vectors of degree $d$ to homogeneous ones of degree $d$, as a substitution by linear forms keeps the degree. By the first part, only $0$ is fixed in this finite dimensional space. The previous lemma kills $l$ on it. The polynomial vectors are sums of homogeneous ones and are dense, so $l = 0$. $\square$

### The vanishing of the coefficient

**Lemma.** Right translation by an element of a compact subgroup keeps the left Haar measure of a locally compact group.

Lean: `New.Exchange.haar_map_mul_right_of_isCompact` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* The translate is a left Haar measure, so it is a multiple of the Haar measure. The multiple is the modular function at the element, a continuous homomorphism to the positive reals. Its image on a compact subgroup is a compact subgroup of the positive reals, which is $\{1\}$. $\square$

Let $D$ split $X$ as $Z$ plus $b$ hyperbolic planes, with $Z$ of signs $t$, and let $Y$ have signs $s$. Recall from [Volume 6](/chapter/rallis-inner-product/#singular-forms) that the coefficient of a theta integral along $D$ at $\jmath T$ unfolds as a sum over the rational frames $x$ of $Y$ with Gram matrix $T$ of an integral over the stabiliser of $x$ modulo its rational points, and that on such a stabiliser the slice at $x$ carries the Weil representation of the smaller pair $(Z, Y)$, with the character $\nu$ if $\delta = \nu\, \upsilon^{\operatorname{card} b}$.

**Theorem (Coefficients off negative forms).** Let $\nu$ have weight $\mu$ with $\mu_\tau < \operatorname{neg}(-t)$ at every real place, and let $\delta = \nu\, \upsilon^{\operatorname{card} b}$. Let $s_i = 1$ for some $i$, and $\operatorname{card} b + \operatorname{neg}(t) = \operatorname{neg}(s)$. Let $T$ be invertible and not represented by the signs $-1$. Suppose that the terms of the unfolded theta integral of $f$ at $g$ are absolutely integrable. Then the coefficient of the theta integral of $f$ along $D$ at $\jmath T$ vanishes at $g$.

Lean: `New.Exchange.integral_theta_pairWeil_stabilizer_eq_zero`, `New.Exchange.homSlice_pairWeil_stabilizer_mul`, `New.Exchange.centreCoeff_eq_zero_of_not_representedBy` (New/Determinant/Exchange/NegativeIndices.lean).

*Proof.* If no rational frame has Gram matrix $T$, the coefficient is an empty sum. Otherwise, by the theorem of Witt, the frames with Gram matrix $T$ form one orbit, and the coefficient is the integral of the term of one frame $x$ over $S$ modulo the rational stabiliser, where $S$ is the adelic stabiliser of $x$. Choose a real place $\tau$ at which $T$ is not of the form $-c^*c$, and $u$ by the proposition. Let $C$ be the part of $S$ that lies in the conjugate of the maximal compact subgroup by $u^{-1}$ at $\tau$; it is compact. By the lemma on Haar measure, the integral over $S$ is unchanged when the term is replaced by its mean over right translates by $C$. That mean is a bounded functional of the datum on the slice. On data with a fixed finite part it defines a functional on the Fock space at $\tau$ that is invariant under the stabiliser of $u x$ in $K(s)$, so it is $0$ by the proposition. Such data span a dense subspace, so the mean is $0$, and the coefficient is $0$. $\square$

**Remark (Formalization).** The hypothesis on $T$ is the failure of `RepresentedBy (-1)` for its image in the adeles; only the real places matter. The integrability of the terms is a hypothesis of the theorem; the users of the theorem supply it.
