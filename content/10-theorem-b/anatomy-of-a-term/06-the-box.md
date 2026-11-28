---
title: The box and the size of a near term
lean:
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/RemainingTerms/Box.lean
  - New/Spanning/Unfolding/Terms.lean
  - New/Spanning/RemainingTerms/OrbitSize.lean
decls:
  - New.Filling.levelMultiples
  - New.Filling.IsResidueDomain
  - New.exists_measurableSet_existsUnique_add_mem
  - New.Filling.exists_isResidueDomain
  - New.Filling.ratTriangle
  - New.Filling.reducedPoints
  - New.Filling.boxedPoints
  - New.Filling.mul_mem_boxedPoints_iff
  - New.Filling.frameBoxRadius
  - New.Filling.IsResidueDomain.mem_frameBox
  - New.Filling.mem_frameBox_of_mem_boxedPoints
  - New.Filling.IsNear
  - New.Filling.IsNear.mul_of_mem_besselU0
  - New.Filling.IsNear.norm_frameProducts_le
  - New.Filling.IsNear.norm_map_leadingMinor_sq_le
  - New.Filling.termDiscNorm
  - New.Filling.norm_map_termDisc_le
  - New.Filling.IsNear.termDiscNorm_le
  - New.Filling.cellRankSecondMoment
  - New.Filling.orbitBound
  - New.Filling.pairCountScale_le_mainSecondMoment
  - New.Filling.IsNear.inv_pow_le_orbitBound
  - New.Filling.gramDiscReal_realFrameGram_ratToInf
  - New.Filling.prod_pairingBoundSq_eq
  - New.Filling.pairingBoundConst_le_mul
  - New.Filling.two_pow_mul_pairCountScale_mul_le
  - New.Filling.pairingBoundConst_le
  - New.Filling.prod_pairingBoundSq_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The box and the size of a near term

An amplitude sum runs over the terms $\gamma$ and integrates over archimedean points $y$. The Bessel functions of [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/) vanish unless $y$ lies in the cut, so only the terms that join two points of bounded size contribute. This section makes "bounded size" precise. It defines the boxed points and the near terms, bounds the frame products of a near term, and defines the size $\operatorname{orbitBound}(j, x)$ that the later chapters attach to an orbit of terms.

### Boxed points

The group $\mathsf{U}(\mathbb{R})$ at the infinite places is not compact, so a fundamental domain for its rational points is needed. The frame at an archimedean point $y$ has a Gram-Schmidt matrix, which is upper unitriangular. Read in the rational frame, its entry $(a, b)$ is a tuple $\operatorname{ratTriangle}(y)_{ab}$ of complex numbers, one at each infinite place. The rational points of $\mathsf{U}$ move these entries by the lattice $M\mathcal{O}_E$.

**Definition (Residue domains and reduced points).** The level multiples are the tuples $(\Phi_v(Mx))_v$ for $x \in \mathcal{O}_E$. A residue domain is a measurable set $D$ of tuples such that every tuple has exactly one translate by a level multiple in $D$, and every point of $D$ has modulus at most $b^{26}$ at every place. A point $y$ is reduced for $D$ if $\operatorname{ratTriangle}(y)_{ab} \in D$ for all $a < b$.

Lean: `New.Filling.levelMultiples`, `New.Filling.IsResidueDomain`, `New.Filling.ratTriangle`, `New.Filling.reducedPoints` (New/Spanning/Unfolding/Setup.lean).

**Lemma (Measurable representatives).** Let $V$ be an abelian group and a standard Borel space with measurable translations, $L$ a countable subgroup and $B$ a measurable set that meets every coset of $L$ in a finite nonempty set. Then $B$ contains a measurable set that meets every coset of $L$ in exactly one point.

Lean: `New.exists_measurableSet_existsUnique_add_mem` (New/Spanning/RemainingTerms/Box.lean).

*Proof.* Fix a measurable injection $\phi: V \to \mathbb{R}$. In each coset take the point of $B$ at which $\phi$ is least; it exists since the coset meets $B$ in a finite nonempty set. The set of these points is $B \cap \bigcap_{l \in L}\{w : l + w \in B \Rightarrow \phi(w) \leq \phi(l + w)\}$, a countable intersection of measurable sets. $\square$

**Lemma (A residue domain exists).** For admissible data there is a residue domain.

Lean: `New.Filling.exists_isResidueDomain` (New/Spanning/RemainingTerms/Box.lean).

*Proof.* Let $B$ be the set of tuples of modulus at most $b^{26}$ at every place. By the approximation lemma `New.exists_principal_near_of_mem_differentIdeal` for the different $\varpi$, for every tuple $w$ there is $a \in \mathcal{O}_E$ with $|-w_v/M - \Phi_v(a)| \leq (2f)^2|\Phi_v(\varpi)|$ at every $v$. Then $|\Phi_v(Ma) + w_v| \leq M(2f)^2|\Phi_v(\varpi)| \leq b^{23}\cdot b^2\cdot b = b^{26}$, by the admissible bounds $M \leq b^{23}$, $2f \leq b$ and $|\Phi_v(\varpi)| \leq b$. So every coset meets $B$. It meets $B$ in a finite set, since only finitely many integers have all conjugates bounded. The previous lemma, with $L$ the level multiples, gives $D \subset B$. $\square$

**Definition (Boxed points).** Let $D_*$ be a residue domain chosen by Hilbert's epsilon operator. A point $y$ is boxed if it is reduced for $D_*$ and lies in the cut at every infinite place: $\operatorname{besselLength}(y_v) \leq b^{6n+2}$.

Lean: `New.Filling.boxedPoints` (New/Spanning/RemainingTerms/Box.lean).

**Remark (Formalization).** The set $D_*$ is not explicit. The proofs use only the three properties of a residue domain, and these hold for $D_*$ since a residue domain exists. No bound of the later chapters depends on the choice.

**Lemma (Invariance of the box).** If $u_v \in \mathsf{U}^0$ at every infinite place, then $uy$ is boxed if and only if $y$ is boxed.

Lean: `New.Filling.mul_mem_boxedPoints_iff` (New/Spanning/RemainingTerms/Box.lean).

*Proof.* An element of $\mathsf{U}^0$ fixes every frame vector, so the frame vectors $y^{-1}\mathfrak{f}_a$ and their Gram-Schmidt matrix do not change. The Bessel length is invariant under the Bessel subgroup on the left. $\square$

**Theorem (Boxed points lie in the frame box).** Let $D$ be a residue domain and $y$ reduced for $D$. Then every frame vector at $y_v$ has length at most $b^{27}\operatorname{besselLength}(y_v)$. If $y$ is boxed, every frame vector at $y_v$ has length at most $b^{37n}$, the frame box radius.

Lean: `New.Filling.frameBoxRadius` (New/Spanning/Unfolding/Setup.lean). Lean: `New.Filling.IsResidueDomain.mem_frameBox`, `New.Filling.mem_frameBox_of_mem_boxedPoints` (New/Spanning/RemainingTerms/Box.lean).

*Proof.* The frame vector of index $l$ is $\sum_a g_{al}\,o_a$, with the orthogonal Gram-Schmidt vectors $o_a$ and the Gram-Schmidt matrix $g$. Each $o_a$ has length at most $\operatorname{besselLength}(y_v)$ ([Lemma](/decl/New.norm_orthoFrame_mem_Icc/)). The entry $g_{al}$ is $\operatorname{ratTriangle}(y)_{al}$ times the ratio of the basis scales $|\kappa_v|^{\varrho - l}/|\kappa_v|^{\varrho - a}$, which is at most $1$ for $a \leq l$ since $|\kappa_v| \geq 1$. So $|g_{al}| \leq b^{26}$ for $a < l$, $g_{ll} = 1$ and $g_{al} = 0$ for $a > l$. There are $\varrho + 1 \leq b$ terms, so the length is at most $b \cdot b^{26}\operatorname{besselLength}(y_v)$. For a boxed point this is at most $b^{27}b^{6n+2} \leq b^{37n}$, since $6n + 29 \leq 37n$. $\square$

### Near terms

**Definition (Near terms).** A rational $\gamma$ is near if there is a boxed point $y$ such that $\gamma^{-1}y$ is boxed.

Lean: `New.Filling.IsNear` (New/Spanning/Unfolding/Terms.lean).

**Lemma (Nearness under the frame fixer).** If $\gamma$ is near and $u, u'$ are rational elements of $\mathsf{U}^0$, then $u\gamma u'$ is near.

Lean: `New.Filling.IsNear.mul_of_mem_besselU0` (New/Spanning/Unfolding/Terms.lean).

*Proof.* Let $y$ witness that $\gamma$ is near. Then $uy$ is boxed, and $(u\gamma u')^{-1}uy = u'^{-1}(\gamma^{-1}y)$ is boxed, by the invariance of the box. $\square$

**Theorem (The frame products of a near term).** Let the data be admissible and $\gamma$ near. Then at every infinite place $w$ and for all $i, j$,

$$|\Phi_w(Z(\gamma)_{ij})| \leq b^{134n}, \qquad |\Phi_w(D_l(\gamma))|^2 \leq b^{270n^2}\ \text{for all } l \leq n.$$

Lean: `New.Filling.IsNear.norm_frameProducts_le`, `New.Filling.IsNear.norm_map_leadingMinor_sq_le` (New/Spanning/Unfolding/Terms.lean).

*Proof.* Let $y$ witness that $\gamma$ is near. The entry $(i, j)$ of the real frame Gram matrix of $\gamma_w$ is $|\kappa_w|^{(\varrho - i) + (\varrho - j)}\Phi_w(Z(\gamma)_{ij})/N$. By the lemma `New.norm_realFrameGram_le_mul` it is at most the product of the lengths of the frame vectors $i$ at $y_w$ and $j$ at $(\gamma^{-1}y)_w$. Both points are boxed, so both lengths are at most $b^{37n}$. With $|\kappa_w| \geq 1$ and $N \leq b^{60n}$, $|\Phi_w(Z_{ij})| \leq b^{60n}b^{74n} = b^{134n}$. For the minor of order $l$, expand the determinant: it has $l! \leq l^l$ terms, each a product of $l$ entries. So $|\Phi_w(D_l)| \leq l^l b^{134nl} \leq b^{l + 134nl}$, using $l \leq n \leq b$. Then $2(l + 134nl) \leq 2n + 268n^2 \leq 270n^2$. $\square$

**Definition (The discriminant norm).** $\operatorname{termDiscNorm}(\gamma) = \prod_v|\Phi_v(\mathsf{g}(\gamma))|$, the product over the $f$ infinite places.

Lean: `New.Filling.termDiscNorm` (New/Spanning/Unfolding/Terms.lean).

The number $\mathsf{g}(\gamma)$ is fixed by the involution, so it lies in the totally real subfield $E^+$. The $f$ infinite places of $E$ restrict to the $f$ real places of $E^+$. So $\operatorname{termDiscNorm}(\gamma) = |N_{E^+/\mathbb{Q}}(\mathsf{g}(\gamma))|$, and it is at least $1$ when $\mathsf{g}(\gamma)$ is a nonzero algebraic integer.

**Corollary (The discriminant of a near term).** At every place, $|\Phi_v(\mathsf{g}(\gamma))| \leq |\Phi_v(\det Z(\gamma))|^2$. If $\gamma$ is near and the data are admissible, then $\operatorname{termDiscNorm}(\gamma) \leq b^{270n^2f}$.

Lean: `New.Filling.norm_map_termDisc_le`, `New.Filling.IsNear.termDiscNorm_le` (New/Spanning/RemainingTerms/OrbitSize.lean).

*Proof.* By [Lemma](/decl/New.Filling.map_termDisc_eq_norm/), $|\Phi_v(\mathsf{g})| = |\Phi_v(\det Z)|^2 - N^2|\Phi_v(D_\varrho)|^2 \leq |\Phi_v(\det Z)|^2$. Take the product over the $f$ places and apply the theorem with $l = n$. $\square$

### The size of an orbit

The later chapters sort the near terms into orbits under $\gamma \mapsto u\gamma u'$ with $u, u'$ in the groups $\mathsf{U}^0_c$ of [the terms of a block](/chapter/anatomy-of-a-term/#the-terms-of-a-block). Each orbit gets a size. Let $D_{\mathrm{main}}$ and $D_{\mathrm{id}}$ be the main and the identity second moments of [the data and its sizes](/chapter/data-and-sizes/), and let $n_p = \#\bar{R}_0\, n_X N^{-kf}$, where $\bar R_0$ is the reduced image of the Bessel subgroup and $n_X$ is the number of classes.

**Definition (Second moment of a cell, orbit bound).** For a cell rank $j$ put $\mathcal{D}_j = D_{\mathrm{main}}$ if $j = \varrho + 1$ and $\mathcal{D}_j = \tau^{-16}D_{\mathrm{id}}$ if $j \leq \varrho$. With $j' = \min(\varrho, j)$, the orbit bound at the gauge $x$ is

$$\operatorname{orbitBound}(j, x) = \tau^2\Big(\frac{\mathcal{D}_j}{n_p\,(M^{2j'f}x)^k}\Big)^{1/2}.$$

Lean: `New.Filling.cellRankSecondMoment`, `New.Filling.orbitBound` (New/Spanning/RemainingTerms/OrbitSize.lean).

**Remark (Formalization).** The source takes the real square root, which is $0$ at a negative argument. For a gauge $x > 0$ the quotient is nonnegative, since $\mathcal{D}_j \geq 0$ and $n_p > 0$, and the square root is the usual one.

**Lemma (The pair count against the main moment).** For admissible data, $n_p \leq D_{\mathrm{main}}$.

Lean: `New.Filling.pairCountScale_le_mainSecondMoment` (New/Spanning/RemainingTerms/OrbitSize.lean).

*Proof.* $D_{\mathrm{id}} = \#\bar R_0\, n_X\, d$, where $d \geq 1$ is the number of Bessel coordinates, so $n_p \leq D_{\mathrm{id}}$ since $N \geq 1$. The admissible data give $\tau^{44}D_{\mathrm{id}} \leq D_{\mathrm{main}}$, and $\tau \geq 1$. $\square$

**Theorem (Lower bound for the top orbit bound).** Let the data be admissible, $\gamma$ near and $x = \operatorname{termDiscNorm}(\gamma) \geq 1$. Then $\operatorname{orbitBound}(\varrho + 1, x) \geq b^{-k^3f}$.

Lean: `New.Filling.IsNear.inv_pow_le_orbitBound` (New/Spanning/RemainingTerms/OrbitSize.lean).

*Proof.* At the top rank $j' = \varrho$. Use $\tau^2 \geq 1$ and the previous lemma: the bound is at least $(M^{2\varrho fk}x^k)^{-1/2}$. It is enough that $M^{2\varrho fk}x^k \leq b^{2k^3f}$. By $M \leq b^{23}$ and the corollary, the left side is at most $b^{e}$ with $e = 46\varrho fk + 270n^2fk$. Since $k \geq 1000(2\varrho+2)^9 \geq 316n^2$, $e \leq 316n^2fk \leq 2k^3f$. $\square$

**Remark.** The proof needs $k$ to be large against $n^2$. [The chapter on the remaining terms](/chapter/remaining-terms/) uses the theorem to bound the tail of a near term of the top cell by its orbit bound.

### The open cell bound in units of the orbit bound

[The chapter on Bessel functions at a real place](/chapter/bessel-real-place/) bounds the open cell part of a term at a place $v$ by a quantity $\operatorname{pairingBoundSq}$ ([Definition](/decl/New.pairingBoundSq/)) that depends on $\gamma$ only through the discriminant $\operatorname{gramDiscReal}$ of the real frame Gram matrix of $\gamma_v$. The link to the rational discriminant is a scaling. Let $s_v = \prod_a s_{v,a}$ be the product of the squared frame scales $s_{v,a} = \kappa_v^{2(\varrho - a)}/N$.

**Lemma (Real and rational discriminants).** $\operatorname{gramDiscReal}(Z(\gamma_v)) = s_v^2|\Phi_v(\mathsf{g}(\gamma))|$.

Lean: `New.Filling.gramDiscReal_realFrameGram_ratToInf` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The real frame vectors are the rational ones scaled by $\sqrt{s_{v,a}}$ at each index. So $\det Z(\gamma_v) = s_v\Phi_v(\det Z(\gamma))$. The leading minor of order $\varrho$ scales by $\prod_{a<\varrho}s_{v,a} = s_v/s_{v,\varrho} = Ns_v$. The real discriminant is $|\det|^2 - |D_\varrho|^2$, so it is $s_v^2(|\Phi_v\det Z|^2 - N^2|\Phi_v D_\varrho|^2) = s_v^2\Phi_v(\mathsf{g})$. $\square$

**Lemma (The product of the open cell bounds).** Let $\operatorname{pairingBoundConst}$ be the product over $v$ of the open cell bounds with $\mathsf{g}$ replaced by $1$. Then

$$\prod_v\operatorname{pairingBoundSq}(\gamma_v) = \frac{\operatorname{pairingBoundConst}}{x^{10^5n^4 + k - 1}}, \qquad x = \operatorname{termDiscNorm}(\gamma).$$

Lean: `New.Filling.prod_pairingBoundSq_eq` (New/Spanning/RemainingTerms/OrbitSize.lean).

*Proof.* The open cell bound at $v$ is $(\rho^{9n}/g_v)^{10^5n^4}\cdot d^2/(\deg\cdot c\cdot(g_v/2)^{k-1})$ with $g_v = \operatorname{gramDiscReal}$. Insert the previous lemma and collect the powers of $|\Phi_v(\mathsf{g})|$. $\square$

**Theorem (The constant of the open cell).** For admissible data, with the covolume $\nu$ of the unipotent group,

$$\operatorname{pairingBoundConst} \leq \Big(\frac{\nu\tau^2}{2}\Big)^2\frac{D_{\mathrm{main}}}{n_p M^{2\varrho fk}}.$$

Lean: `New.Filling.pairingBoundConst_le` (New/Spanning/RemainingTerms/OrbitSize.lean).

*Proof.* Write $d$ for the number of Bessel coordinates, $\deg$ for the Bessel degree, $c_G$ for the open cell constant, $\Lambda$ for the frame scale product and $a_*$ for the scaled Siegel constant of [the data and its sizes](/chapter/data-and-sizes/). The proof chains three bounds. First, $\operatorname{pairingBoundConst} \leq 2^{kf}\tau d^2/(\deg c_G^f\Lambda^2)$. Second, $2^{kf}n_pM^{2\varrho fk} \leq \tau a_*\operatorname{vol}(\hat{\mathcal O})^n$.

Lean: `New.Filling.pairingBoundConst_le_mul`, `New.Filling.two_pow_mul_pairCountScale_mul_le` (New/Spanning/RemainingTerms/OrbitSize.lean).

For the first, the frame scales give $b^{-60n^2} \leq s_v \leq b^{46n^2}$, so the powers of $b$ from the frame box radius and from the $s_v$ have an exponent of order $n^9$, and the lemma on the tail scale bounds them by $\tau$. For the second, $x = 200fk\,\mathrm{rd}_E$ satisfies $x^{1000} \leq b$, so $x^{4kf} \leq \tau$ absorbs the powers of $2$, $k$ and $\mathrm{rd}_E$, and the order of the unipotent group is at least $M^{2\varrho fk}$. Third, the admissible data give $a_* \leq (1 + b^{-9})D_{\mathrm{main}}\deg c_G^f\operatorname{vol}(\hat{\mathcal O})^{-n}(\nu\Lambda/d)^2$. Multiply the three. The factors $d$, $\deg$, $c_G$, $\Lambda$ and the volume cancel, and

$$\operatorname{pairingBoundConst}\cdot n_pM^{2\varrho fk} \leq (1 + b^{-9})\tau^2\nu^2D_{\mathrm{main}} \leq 2\tau^2\nu^2D_{\mathrm{main}}.$$

Finally $\tau^2 \geq b^2 \geq 8$, so $2\tau^2\nu^2 \leq (\nu\tau^2/2)^2$. $\square$

**Theorem (The open cell bound by the orbit bound).** For admissible data and $x = \operatorname{termDiscNorm}(\gamma) \geq 1$,

$$\prod_v\operatorname{pairingBoundSq}(\gamma_v) \leq \Big(\frac{\nu\operatorname{orbitBound}(\varrho+1, x)}{2}\Big)^2.$$

Lean: `New.Filling.prod_pairingBoundSq_le` (New/Spanning/RemainingTerms/OrbitSize.lean).

*Proof.* By the two previous results the left side is at most $(\nu\tau^2/2)^2D_{\mathrm{main}}/(n_pM^{2\varrho fk}x^{10^5n^4+k-1})$. Since $x \geq 1$ and $10^5n^4 + k - 1 \geq k$, we can replace the power of $x$ by $x^k$. The result is $(\nu/2)^2\tau^4D_{\mathrm{main}}/(n_p(M^{2\varrho f}x)^k)$, which is the square of $\nu\operatorname{orbitBound}(\varrho+1, x)/2$. $\square$
