---
title: Riemann's relation and normal generation
lean:
  - Lib/Shimura/ThetaNormality/RiemannRelation.lean
  - Lib/Shimura/ThetaNormality/NormalGeneration.lean
  - Lib/Shimura/ThetaModuli/FlatClosure.lean
decls:
  - New.IsAppellHumbert.sum_shift_mul_shift
  - New.ThetaTori.ThetaTorus.IsRiemannTuple
  - New.paddingTuple
  - New.ThetaTori.ThetaTorus.riemann_relation
  - New.ThetaTori.ThetaTorus.exists_forall_valuation_thetaCoord_zero_le
  - New.ThetaTori.HasGoodReduction.normBall_pow_pow
  - New.ThetaTori.HasGoodReduction.finrank_reduction_eq
  - New.Variety.ThetaNull.IsCutOut
  - New.ThetaTori.ThetaTorus.isCutOutAt_reduction
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Riemann's relation and normal generation

A flat family of projective varieties has the same Hilbert function in every fibre. To show that its closure is flat, the source must control the ideals of the fibres modulo a good place. Two classical facts give this control. Riemann's theta relation expresses products of theta functions through theta-null values. Normal generation says that the theta functions of degree $r^j$ are products of theta functions of degree $r$. The source proves both over a valuation ring of $\mathbb{C}$, with the sup norm of Section 3 in place of cohomology.

### The classical statements

Let $A$ be a complex abelian variety and $M$ an ample line bundle. Koizumi, *Theta relations and projective normality of abelian varieties*, Amer. J. Math. 98 (1976), proves that $M^r$ is projectively normal for $r \geq 3$: the map $\operatorname{Sym}^k H^0(A, M^r) \to H^0(A, M^{rk})$ is onto for all $k$. Birkenhake and Lange, *Complex Abelian Varieties*, 2nd ed. (2004), Chapter 7, give Riemann's theta relations and Koizumi's theorem. The source needs these facts in a form that survives reduction, and only in the degrees $r^j$ with $r = D.\mathrm{paddedNorm}$.

### Orthogonality

The basic identity is Schur orthogonality for the finite Heisenberg group that acts on the theta functions. Let $(L, B, \chi)$ be an Appell-Humbert datum with positive Riemann form on a full lattice $L$. For $a$ in the dual lattice $L^\vee$ of $L$ for the Riemann form, write $U_a$ for the twisted translation by $a$. It sends theta functions of type $(B, \chi)$ to theta functions of the same type.

**Lemma (Orthogonality of translates).** Let $T$ be a finite set and $a : T \to L^\vee$ a map such that translation by every point of $L^\vee$ permutes the classes $a(s)$ modulo $L$. Let $d$ be the integer square root of $[L^\vee : L]$. Then for all theta functions $f, g$ of type $(B, \chi)$ and all $z, w \in V$,
$$d \sum_{s \in T} U_{-a(s)}g(z)\, U_{a(s)}f(w) = |T|\, f(z)\, g(w).$$

Lean: `New.IsAppellHumbert.sum_shift_mul_shift` (Lib/Shimura/ThetaNormality/NormalGeneration.lean).

The index $[L^\vee : L]$ is the square of the dimension of the space of theta functions of type $(B, \chi)$ (Birkenhake and Lange, Chapter 3). The identity is Schur's lemma for the irreducible representation of the Heisenberg group.

**Remark (Formalization).** The constant $d$ is `Nat.sqrt` of the index. Since the index is a square, $d$ is the exact square root. If the hypothesis on $a$ holds, $T$ meets every class of $L^\vee/L$, so $|T| \geq d^2 > 0$, and the identity is not empty.

### Riemann's relation

Let $x$ be a theta torus for the datum $D$. Recall that $T = D.\mathrm{dualTorsion}$, $r = D.\mathrm{paddedNorm}$, and $\theta_s$ is the theta coordinate of Section 3. Let $T[r]$ be the $r$-torsion of $T$.

**Definition (Riemann tuple).** A family $p = (a_k, b_k)_{k \in K}$ of pairs in $\mathcal{O}_E$ is a *Riemann tuple* for $D$ when $\sum_k \bar a_k a_k = r$ and $\sum_k \bar a_k b_k = 0$.

Lean: `New.ThetaTori.ThetaTorus.IsRiemannTuple` (Lib/Shimura/ThetaNormality/RiemannRelation.lean).

For $\mu : K \to T$ and $w, z \in V$ put
$$P_p(\mu; w, z) = \prod_{k \in K} \theta_{\mu_k}(a_k z + b_k w).$$
This is the function `thetaProduct`. The conditions on $p$ make $z \mapsto P_p(\mu; w, z)$ a theta function of degree $r$, for the lattice over $T[r]$.

**Example (The padding tuple).** Let $c \in \mathcal{O}_E$ and let $a_1, \ldots, a_{r-3}$ be a padding of $c$ to $r$ (Section 2). The padding tuple is the family of pairs
$$(1, 0),\ (1, 0),\ (c, 1),\ (1, -\bar c),\ (a_1, 0), \ldots, (a_{r-3}, 0).$$
Then $\sum \bar a_k a_k = 1 + 1 + \bar c c + 1 + \sum_l \bar a_l a_l = r$ by the padding, and $\sum \bar a_k b_k = \bar c \cdot 1 + 1 \cdot (-\bar c) = 0$. So it is a Riemann tuple. The summand $3$ of the padding condition comes from the three pairs with first entry $1$. Section 5 uses the tuple for $c = -1$, with a padding of $1$ that spans $\mathcal{O}_E$, and the tuple for $c = 0$ with all $a_l = 1$.

Lean: `New.paddingTuple` (Lib/Shimura/ThetaNormality/RiemannRelation.lean).

**Theorem (Riemann's relation).** Let $p$ and $q = (a'_k, b'_k)$ be Riemann tuples for $D$, and let $\mu, \mu' : K \to T$ satisfy $\sum_k \bar a_k \mu_k = t = \sum_k \bar a'_k \mu'_k$. Then for every $z \in V$,
$$|T|\, P_q(\mu'; w, 0)\, P_p(\mu; w, z) = \sqrt{[T : T[r]]} \sum_{s \in T} P_p(\mu - a s; w, 0)\, P_q(\mu' + a' s; w, z),$$
where $(\mu - as)_k = \mu_k - a_k s$ and $(\mu' + a's)_k = \mu'_k + a'_k s$.

Lean: `New.ThetaTori.ThetaTorus.riemann_relation` (Lib/Shimura/ThetaNormality/RiemannRelation.lean).

*Proof.* $P_p(\mu; w, \cdot)$ and $P_q(\mu'; w, \cdot)$ are theta functions of degree $r$ of the same type for the lattice over $T[r]$, since $\sum \bar a_k \mu_k = \sum \bar a'_k \mu'_k$. Its dual for $rB$ is the lattice over $T$. Translation by the lift of $s \in T$ sends $P_p(\mu; w, \cdot)$ to a multiple of $P_p(\mu + a s; w, \cdot)$ (`thetaShift_periodPoint_thetaProduct`), and the roots of unity cancel. Apply the orthogonality lemma with the lifts of $T$, $f = P_p(\mu; w, \cdot)$ and $g = P_q(\mu'; w, \cdot)$, at the points $z$ and $0$. The index of the lattice over $T[r]$ in its dual is $[T : T[r]]$, which gives the factor. $\square$

**Remark (Formalization).** The factor $\sqrt{[T : T[r]]}$ is the natural number `(D.rTorsion.relIndex D.dualTorsion).sqrt`, the integer square root. The index is a square, so the factor is exact. The textbook relation uses a $4 \times 4$ matrix with entries $\pm 1/2$. The source uses one variable $z$, a parameter $w$, and coefficients in $\mathcal{O}_E$.

### Theta-null values of largest valuation

**Lemma (Theta-null values of largest valuation).** Assume that $(B, \chi, v)$ has good reduction with level $r$ for the theta torus $x$, and that $v(|T|) = 1$. Then for every $s \in T$ there is $u \in T$ such that each of $\theta_u(0)$, $\theta_{-u}(0)$ and $\theta_{s - u}(0)$ has the largest valuation among all $\theta_t(0)$, $t \in T$.

Lean: `New.ThetaTori.ThetaTorus.exists_forall_valuation_thetaCoord_zero_le` (Lib/Shimura/ThetaNormality/RiemannRelation.lean).

*Proof.* The valuation is written multiplicatively. Let $\tau = v(\theta_o(0))$ be the largest of the $v(\theta_t(0))$. Let $\tau'$ be the largest over $t$ of $\min(v(\theta_{s-t}(0)), v(\theta_{-t}(0)))$, taken at $t = u$. It suffices to show $\tau \leq \tau'$; a private lemma then handles $\theta_u(0)$. All $\theta_t$ have the same norm $\rho > 0$. Write $r = k + 3$. Consider the product $\Phi = \theta_s \cdot \theta_{ro - s} \cdot \theta_0^{k+1}$, a theta function of degree $r$. By the multiplicative norm of Section 3, the supremum of its sizes over the torsion points is $\rho^r$. So it suffices to show $\tau \cdot \mathrm{size}_\Phi(z) \leq \tau' \rho^r$ at every torsion point $z$. For this, apply Riemann's relation with the tuple whose pairs are all $(1, 0)$, to the indices of $\Phi$ on one side and to the constant index $o$ on the other side. The left side is $|T|\,\theta_o(0)^r\,\Phi(z)$, with valuation $\tau^r v(\Phi(z))$, because $v(|T|) = 1$. The term for $t$ on the right side contains the factor $\theta_{s-t}(0)\theta_{-t}(0)$, whose valuation is at most $\tau'\tau$ because it is the minimum times the maximum of the two values. The other factors at $0$ have valuation at most $\tau$, the factors at $z$ are bounded by the norm, and the integer $\sqrt{[T : T[r]]}$ has valuation at most $1$. The ultrametric inequality bounds the sum by its largest term. Cancel $\tau^{r-1}$. $\square$

This gives condition 4 of the theorem on theta families from points (Section 5).

### Normal generation over a valuation ring

Let $(B, \chi, v)$ have good reduction with level $r$, and let $f \neq 0$ be a theta function of type $(B, \chi)$. The *ball* of $f$ is the set of theta functions $g$ of type $(B, \chi)$ with $\|g\|_v \leq \|f\|_v$. It is a module over the valuation ring $O_v$, the analogue of the lattice of integral sections.

**Lemma (Integral normal generation).** Let $f$ be a theta function for $(L, B, \chi)$ and also for an Appell-Humbert datum $(L_0, B, \zeta)$ on a lattice $L_0 \supseteq r^{-1}L$. Then for every $j \geq 0$, the $r^j$-th power of the ball of $f$ is the ball of $f^{r^j}$ in degree $r^j B$.

Lean: `New.ThetaTori.HasGoodReduction.normBall_pow_pow` (Lib/Shimura/ThetaNormality/NormalGeneration.lean).

The power is the $O_v$-span of products of $r^j$ elements. One inclusion is the multiplicativity of the norm. The other is proved by induction from $j = 1$ (`New.ThetaTori.HasGoodReduction.normBall_pow`), with the key step `New.ThetaTori.HasGoodReduction.mem_of_mem_normBall`: an $O_v$-module that contains the translates of $f$ by the dual lattice of $L_0$ contains the ball of $f$. Its proof uses the orthogonality lemma.

**Lemma (Reduction keeps the rank).** Let $(B, \chi, v)$ have good reduction with level $r$, and let $f \neq 0$ be a theta function of type $(B, \chi)$. Let $W$ be a finite $O_v$-module and $\lambda : W \to (V \to \mathbb{C})$ an $O_v$-linear map onto the ball of $f$. Let $\varphi : O_v \to k$ be a ring map onto a field, and $\mathrm{red} : W \to Q$ a $\varphi$-semilinear map to a $k$-vector space with $\mathrm{red}(w) = 0$ exactly when $\|\lambda(w)\|_v < \|f\|_v$. Then the $k$-span of the image of $\mathrm{red}$ has dimension equal to the complex dimension of the space of theta functions of type $(B, \chi)$.

Lean: `New.ThetaTori.HasGoodReduction.finrank_reduction_eq` (Lib/Shimura/ThetaNormality/NormalGeneration.lean).

*Proof.* The ball is finitely generated and torsion free over the valuation ring $O_v$, so it is flat, and hence free, since $O_v$ is local. A basis $b$ of the ball is a complex basis of the theta functions, by flatness of $\mathbb{C}$ over $O_v$. The kernel of $\lambda$ lies in the kernel of $\mathrm{red}$, since $\|f\|_v > 0$. So $\mathrm{red}$ factors through the ball. A combination $\sum c_i b_i$ has norm less than $\|f\|_v$ exactly when all $c_i$ lie in the maximal ideal, because the norm of the ball is the Gauss norm of the coordinates in the basis $b$ (this uses the multiplicative norm). So the reductions of the $b_i$ form a basis of the span of the image. $\square$

### The ideal of the reduced theta points

Let $k$ be a field and consider polynomials in variables $X_s$, $s \in J$.

**Definition (Cut out by points).** Let $r, i \in \mathbb{N}$, $\sigma : \mathbb{N} \to \mathbb{N}$, $c \in J$, and let $(p_a)_a$ be points of $k^J$. An ideal $I$ of $k[X_s : s \in J]$ is *cut out by the points $p_a$ in the chart $c$*, with ranks $\sigma$ and bound $i$, when: $X_c - 1 \in I$; for every $j$ the forms of degree $r^j$ span a space of dimension $\sigma(j)$ modulo $I$; and for $j \leq i$ a form of degree $r^j$ lies in $I$ exactly when it vanishes at all $p_a$.

Lean: `New.Variety.ThetaNull.IsCutOut` (Lib/Shimura/ThetaModuli/FlatClosure.lean).

Section 5 gives the scheme version `IsCutOutAt`. The ranks used are `thetaRanks T r j`, the integer square root of $\#\{y : r^j y \in T\}$, which is the dimension of the space of theta functions of degree $r^j$.

**Theorem (Reduction of the theta points).** Let $x$ be a theta torus with good reduction at $v$ of level $r = D.\mathrm{paddedNorm}$, and let $\varphi : O_v \to k$ be onto a field. Let $q(z)$ be integral homogeneous coordinates of the theta vector $(\theta_s(z))_{s \in T}$ for every $z \in V$, and $p(l)$ those of the theta vector at the lift of each level point $l$. Let $S$ be a scheme with a $k$-point $t$ and maps $N_l$ to projective space such that $N_l$ has the homogeneous coordinates $\varphi \circ p(l)$ at $t$. Then the maps $N_l$ cut out at $t$ the reduced vectors $\varphi \circ q(z)$, $z \in V$, with ranks `thetaRanks T r` and bound $D.\mathrm{exponentBound}$.

Lean: `New.ThetaTori.ThetaTorus.isCutOutAt_reduction` (Lib/Shimura/ThetaNormality/RiemannRelation.lean).

*Proof.* Fix charts and a chart $c$. In the chart $c$ the forms of degree $r^j$ that vanish at all reduced points $\varphi \circ q(z)$ are those whose lift is small, that is, has norm less than the norm of the ball, by the definition of the reduction. By integral normal generation, the forms of degree $r^j$ in the theta coordinates map onto the ball of degree $r^j$. By the lemma on reduction, the quotient by the small forms has dimension equal to the dimension of the theta functions of degree $r^j B$, which is `thetaRanks T r j`. For $j \leq D.\mathrm{exponentBound}$, the level points represent the dual lattice of $r^j B$ modulo the period lattice, by the choice of `D.levelTorsion`. So a form of such a degree vanishes at all reduced points exactly when it vanishes at the reductions of the level points, which are the coordinates of the $N_l$ at $t$. $\square$

**Remark (Formalization).** The theorem is stated for integral coordinates $q(z)$ that are given as hypotheses, one of them a unit in each vector (`IsIntegralCoords`). Such coordinates exist, since one can divide by a coordinate of largest valuation, and a change of choice does not change the reduced point.
