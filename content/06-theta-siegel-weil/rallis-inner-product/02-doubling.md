---
title: Doubling
lean:
  - Lib/SiegelWeil/RallisInner/Doubling.lean
decls:
  - New.SiegelWeil.negSourceFactor
  - New.SiegelWeil.norm_negSourceFactor
  - New.SiegelWeil.theta_negSourceFactor_smul
  - New.SiegelWeil.doubleDatum
  - New.SiegelWeil.theta_doubleDatum
  - New.SiegelWeil.graphSplitting
  - New.SiegelWeil.weilMatrixCoeff
  - New.SiegelWeil.zeroTerm_graphSplitting
  - New.SiegelWeil.IsClean
  - New.SiegelWeil.mul_eq_zero_of_zeroTerm_ne_zero
  - New.SiegelWeil.exists_graph_eq_of_zeroTerm_ne_zero
  - New.SiegelWeil.graphSplitting_lagrangian_injective
  - New.SiegelWeil.theta_splitWeil_doubleDatum
  - New.SiegelWeil.zeroTerm_graphSplitting_doubleDatum
  - New.SiegelWeil.integral_conj_theta_mul_theta
  - New.SiegelWeil.exists_doubling_bound
  - New.SiegelWeil.exists_doubling_le_height
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Doubling

This section proves the doubling identity. It writes the product of two theta kernels as one theta kernel on the doubled space, applies the Siegel-Weil formula, and finds the Lagrangians with a nonzero term. Throughout, $S$ has rank $n$, $T$ has rank $m$, and $a$, $b$ are characters of $[U(1)]$ that twist the Weil representation $\omega = $ `New.pairWeil S T a b`.

### The doubled datum

The space $S^-$ is $S$ with the form $-J$. The data on $\operatorname{Hom}(S^-, T)$ are the data on $\operatorname{Hom}(S, T)$, by transport. The theta functionals of the two spaces differ by complex conjugation and by a scalar of modulus one.

**Lemma.** There is a complex number $c$ with $|c| = 1$ such that $\theta_{S^-}(c \cdot \bar f) = \overline{\theta_S(f)}$ for every datum $f$ on $\operatorname{Hom}(S, T)$. Here $\bar f$ is the transport of $f$ to $\operatorname{Hom}(S^-, T)$.

Lean: `New.SiegelWeil.negSourceFactor`, `New.SiegelWeil.norm_negSourceFactor`, `New.SiegelWeil.theta_negSourceFactor_smul` (Lib/SiegelWeil/RallisInner/Doubling.lean).

**Remark (Formalization).** The scalar `negSourceFactor S T` is chosen by `choose` from an existence statement. The source does not compute it. Only its modulus and the identity above are used. The theta functional is unique up to a scalar, and the source fixes only its absolute value, so a free phase of this kind is expected.

**Definition.** The *doubled datum* of $f'$ and $f$ is the datum $f \boxtimes c\,\bar{f'}$ on $\operatorname{Hom}(S \oplus S^-, T)$. It is linear in $f$ and conjugate linear in $f'$.

Lean: `New.SiegelWeil.doubleDatum` (Lib/SiegelWeil/RallisInner/Doubling.lean).

**Lemma.** The theta functional of $S \oplus S^-$ at the doubled datum is $\overline{\theta(f')}\,\theta(f)$.

Lean: `New.SiegelWeil.theta_doubleDatum` (Lib/SiegelWeil/RallisInner/Doubling.lean).

The group $U(S) \times U(S)$ embeds in $U(S \oplus S^-)$, and the group $U(T)$ acts on both sides. The next lemma states that the doubled datum is compatible with these actions.

**Lemma.** For data $f$, $f'$, points $g$, $g'$ of $U(S)(\mathbb{A})$ and $x$ of $U(T)(\mathbb{A})$,
$$\theta_{S \oplus S^-}\big(\omega(1, x)\, d\big) = \overline{\theta(\omega(g', x) f')}\;\theta(\omega(g, x) f),$$
where $d$ is the doubled datum of $\omega(g', 1) f'$ and $\omega(g, 1) f$, and $\omega$ on the left is the untwisted representation `New.SiegelWeil.splitWeil` of the doubled pair.

Lean: `New.SiegelWeil.theta_splitWeil_doubleDatum` (Lib/SiegelWeil/RallisInner/Doubling.lean).

At the points $(g, 1)$ the character $a$ plays no role, so the source takes it to be $1$ there. The proof checks that the characters fit: the negation of the form changes $b$ into $b^{-1} \upsilon^{m}$, where $\upsilon$ is the splitting character of the Weil data.

### The graph Lagrangians

Let $\delta$ be a rational isometry of $S$. The graph $\{(\delta y, -y)\}$ is a Lagrangian of $S \oplus S^-$, and the graph $\{(\delta y, y)\}$ is a dual Lagrangian.

**Definition.** The *graph splitting* of $\delta$ is the complete splitting of $S \oplus S^-$ with isotropic frame $k = (\delta; -1)$, dual frame $l = (\delta; 1) \cdot \tfrac12 J^{-1}$ and an empty anisotropic part.

Lean: `New.SiegelWeil.graphSplitting` (Lib/SiegelWeil/RallisInner/Doubling.lean).

The three Gram conditions $k^* J' k = 0$, $l^* J' l = 0$ and $l^* J' k = 1$, with $J' = J \oplus -J$, follow from $\delta^* J \delta = J$. The source checks them by computation with block matrices.

**Definition.** The *matrix coefficient* of $f$ and $f'$ is the function $g \mapsto \langle f', \omega(g, 1) f \rangle$ on $U(S)(\mathbb{A})$, for the representation $\omega = $ `New.pairWeil S T 1 b`. If $f'$ is omitted it is $f$.

Lean: `New.SiegelWeil.weilMatrixCoeff` (Lib/SiegelWeil/RallisInner/Doubling.lean).

**Lemma.** The term of the graph Lagrangian of $\delta$ in the Siegel-Weil formula, at the doubled datum of $f'$ and $f$, is the matrix coefficient $\langle f', \omega(\delta^{-1}) f \rangle$. More generally, the term of the graph of $\delta^{-1}$ at the doubled datum of $\omega(g', 1) f'$ and $\omega(g, 1) f$ is $\langle f', \omega(g'^{-1} \delta g) f\rangle$.

Lean: `New.SiegelWeil.zeroTerm_graphSplitting`, `New.SiegelWeil.zeroTerm_graphSplitting_doubleDatum` (Lib/SiegelWeil/RallisInner/Doubling.lean).

*Proof.* The term of a Lagrangian is the value at $0$ of the datum in the Schrödinger model of a splitting along it. For the graph splitting this value is a mean over adelic vectors modulo rational ones. A change of variables that sends $(X, Y)$ to the coordinates of the graph turns this mean into the inner product of the two data on $\operatorname{Hom}(S, T)$. The second statement follows from the first, from $\langle \omega(h) u, \omega(h) u' \rangle = \langle u, u'\rangle$ and from the homomorphism property of $\omega$. $\square$

**Lemma.** Distinct rational isometries have distinct graph Lagrangians.

Lean: `New.SiegelWeil.graphSplitting_lagrangian_injective` (Lib/SiegelWeil/RallisInner/Doubling.lean).

*Proof.* If two graphs agree, the frames satisfy $(\delta'^{-1}; -1) = (\delta^{-1}; -1)\, c$ for a matrix $c$. The lower blocks give $c = 1$, and then $\delta = \delta'$. $\square$

### Clean data

For mixed signs, Lagrangians that are not graphs can have a nonzero term. The source excludes them by a condition on the datum.

**Definition.** A datum $F$ on $\operatorname{Hom}(S, T)$ is *clean* if one of two conditions holds.

- (a) All signs of $S$ agree.
- (b) $F = \Psi \otimes f$ is the Schrödinger datum of a function $\Psi$ at a set $A$ of places that is disjoint from its conjugate, $\Psi$ is a Schwartz-Bruhat function above $A$, and there is a place $w$ such that every matrix $y$ with $\Psi(y) \neq 0$ has a left inverse at $w$.

Lean: `New.SiegelWeil.IsClean` (Lib/SiegelWeil/RallisInner/Doubling.lean).

**Lemma.** Let $f$ be clean, and let $D$ be a complete splitting of $S \oplus S^-$ whose isotropic frame has the blocks $K$ in $S$ and $K'$ in $S^-$. Suppose that the term of the Lagrangian of $D$ at the doubled datum of $f'$ and $\omega(g, 1) f$ is not $0$. If $K' c = 0$ for a matrix $c$, then $K c = 0$.

Lean: `New.SiegelWeil.mul_eq_zero_of_zeroTerm_ne_zero` (Lib/SiegelWeil/RallisInner/Doubling.lean).

*Proof.* Suppose $K' c = 0$. The Gram condition of $D$ gives $(Kc)^* J (Kc) = 0$, so the columns of $Kc$ are isotropic vectors of $S$. In case (a) the space $S$ is definite, and $Kc = 0$. In case (b) suppose $Kc \neq 0$. The term is a bounded linear functional $\ell$ of the datum. It is invariant under the Heisenberg translations attached to the columns of $Kc$, because these vectors lie in the Lagrangian. The support of $\Psi$ consists of matrices with a left inverse at $w$, so no point of the support is orthogonal to all these translations. A functional with this invariance vanishes at $\Psi \otimes f$. This contradicts the hypothesis. $\square$

**Proposition.** Let $f$ be clean, and let $L$ be a Lagrangian of $S \oplus S^-$ whose term at the doubled datum of $f'$ and $\omega(g, 1) f$ is not $0$. Then $L$ is the graph Lagrangian of a rational isometry of $S$.

Lean: `New.SiegelWeil.exists_graph_eq_of_zeroTerm_ne_zero` (Lib/SiegelWeil/RallisInner/Doubling.lean).

*Proof.* Write the frame of a complete splitting along $L$ in blocks $K$ and $K'$. Its rank is $n$, since $S \oplus S^-$ has rank $2n$. The Gram condition reads $K^* J K = K'^* J K'$. By the lemma, $K'c = 0$ implies $D.k\, c = 0$, and the frame has a left inverse, so $c = 0$. Hence $K'$ is injective. It is a square matrix over $E$, so it has an inverse $B$. The matrix $-KB$ is an isometry of $S$, because $(KB)^* J (KB) = (K'B)^* J (K'B) = J$. The graph of its inverse lies in $L$, and both are Lagrangians, so they are equal. $\square$

### The doubling identity

**Theorem (Doubling identity).** Let $2n < m$, let $f$ be a clean datum, and let $f'$ be any datum. For $g$, $g'$ in $U(S)(\mathbb{A})$,
$$\int_{[U(T)]} \overline{\theta(\omega(g', x) f')}\;\theta(\omega(g, x) f)\, dx = \operatorname{vol}([U(T)]) \sum_{\gamma \in U(S)(E)} \langle f', \omega(g'^{-1} \gamma g) f \rangle.$$

Lean: `New.SiegelWeil.integral_conj_theta_mul_theta` (Lib/SiegelWeil/RallisInner/Doubling.lean).

*Proof.* Let $d$ be the doubled datum of $\omega(g', 1) f'$ and $\omega(g, 1) f$. By the compatibility lemma, the integrand is $\theta_{S \oplus S^-}(\omega(1, x) d)$. The space $S \oplus S^-$ has the complete splitting of $\delta = 1$, with $n$ hyperbolic planes, and $2n < m$. The Siegel-Weil formula of [the Siegel-Weil formula](/chapter/siegel-weil/) gives the integral as $\operatorname{vol}([U(T)])$ times the sum of the terms $Z_L(d)$ over all Lagrangians $L$. By the proposition, the terms vanish off the graph Lagrangians. The map from isometries to graphs is injective, so the sum is a sum over $\delta$ in $U(J)(E)$. The group $U(J)(E)$ is in bijection with $S.\Gamma$. The term of the graph of $\delta^{-1}$ is $\langle f', \omega(g'^{-1} \delta g) f\rangle$. $\square$

The textbook form is the doubling identity of Rallis. In the unitary case it is written out, for example, in Y. Liu (2011), Proposition 2.3, and in Eischen, Harris, Li and Skinner, Section 4.1.4. The source cites both. The classical identity holds with the Siegel Eisenstein series on $U(S \oplus S^-)$ in place of the sum over Lagrangians, and it holds outside Weil's range after regularization.

**Remark (Formalization).** The source does not define an Eisenstein series on the doubled group. The sum over Lagrangians in the Siegel-Weil formula plays its role. Only Lagrangians of graphs appear, and this follows from the clean condition, not from an orbit decomposition of the doubled flag variety. In the classical method the other orbits contribute terms that vanish for cusp forms. Here the forms are not assumed cuspidal, so the source removes those orbits with the test datum. The hypothesis `IsClean` has real content in case (b). The open finding F-084 of the project asks whether every call site discharges it.

### Bounds

The next results give the absolute convergence that the inner product formula needs.

**Lemma.** Let $2n < m$. There is a finite constant $C$ such that, for all characters $a$, $b$, all data $f$, $f'$ and all $g$, $g'$, both the integral of $|\overline{\theta(\omega(g', x) f')}\,\theta(\omega(g, x) f)|$ over $[U(T)]$ and the sum $\sum_\gamma |\langle f', \omega(g'^{-1}\gamma g) f \rangle|$ are at most $C\, \|\omega(g', 1) f'\|\, \|\omega(g, 1) f\|$.

Lean: `New.SiegelWeil.exists_doubling_bound` (Lib/SiegelWeil/RallisInner/Doubling.lean).

The proof bounds the theta kernel of the doubled pair by an integrable function times the norm of the datum. This bound comes from [the Siegel-Weil formula](/chapter/siegel-weil/). The sum of the norms of the terms of the graphs is finite by the summability part of the Siegel-Weil formula. The lemma holds for every datum, clean or not.

**Lemma.** Let $2n < m$ and fix $a$, $b$, $f$, $f'$. There are $l \in \mathbb{N}$ and a finite constant $C$ such that both quantities of the last lemma are at most $C\, \operatorname{ht}(g')^l\, \operatorname{ht}(g)^l$, where $\operatorname{ht}$ is the height on $U(S)(\mathbb{A})$.

Lean: `New.SiegelWeil.exists_doubling_le_height` (Lib/SiegelWeil/RallisInner/Doubling.lean).

Both quantities are invariant under rational points in $g$ and in $g'$. The proof replaces $g$ by a point of the same class at which $\|\omega(g, 1) f\|$ grows at most like a power of the height.
