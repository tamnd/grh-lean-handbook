---
title: The hyperbolic plane step
lean:
  - New/OneLift/FalseLifts/HyperbolicPlaneStep.lean
decls:
  - New.SiegelWeil.lift_pairThetaKer_swap_apply
  - New.SiegelWeil.projOn_homSlice_zero
  - New.SiegelWeil.DescentsVanish.integral_homSlice_eq_zero
  - New.SiegelWeil.norm_theta_sub_zeroTerm_le
  - New.SiegelWeil.theta_sub_zeroTerm_rho_ratMap
  - New.SiegelWeil.exists_col_k_mem_latticeBall
  - New.SiegelWeil.subspaceMean_theta_sub_zeroTerm_eq_zero
  - New.SiegelWeil.exists_norm_theta_sub_zeroTerm_le
  - New.SiegelWeil.DescentsVanish.bddAbove_lift
  - New.SiegelWeil.DescentsVanish.of_isEmpty
  - New.SiegelWeil.descentsVanish_add_planes
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The hyperbolic plane step

This section climbs the tower. Let the descents of $Y$ from $U(V)$ to $U(W)$ vanish. Add one hyperbolic plane to $W$, to get $W'$. The theta kernel of $W'$ is the kernel of $W$ (its zero term along the plane) plus a remainder. The zero term gives descents to $W$, which vanish. The remainder decays at the cusp. So the descents to $W'$ are bounded, and by [Section 5](/chapter/false-lifts/#small-roots) they vanish.

Throughout, $V$ is definite of rank $n$, $W$ has rank $r$, and $D$ is a splitting of $W'$ into $W$ and $p$ hyperbolic planes, with an isotropic frame $k$ (`D : W'.Splitting W p`). It is adapted (`IsBaseAdapted D`) if its adelic frames are orthonormal at the infinite places and integral at the finite places. The splitting $D$ induces a splitting of $\mathrm{Hom}(W', V)$. Its zero term $\theta_0 = \theta_W \circ \mathrm{zeroTerm}$ is the constant term of the theta functional along the frame. The slice $\mathrm{homSlice}\ 0\ \phi$ is the zero term of $\phi$, a datum on $\mathrm{Hom}(W, V)$. The character $\upsilon_1$ is the restriction to $U(1)$ of the character $\upsilon$ of the Weil data (`upsilonU1`).

### The descent as an integral

**Lemma (The descent).** The descent of $Y$ from $U(T)$ to $U(S)$ by $\phi$ at $g$ is $\int_{[U(T)]} \theta(\omega(g, h)\phi)\, Y(h)\, dh$.

Lean: `New.SiegelWeil.lift_pairThetaKer_swap_apply` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* This is the definition of the lift for the swapped kernel. $\square$

### The zero term gives descents to $W$

**Lemma (Slices of vacua).** Let $D$ be adapted. If $\phi$ is the vacuum at the places of $S$, then so is $\mathrm{homSlice}\ 0\ \phi$.

Lean: `New.SiegelWeil.projOn_homSlice_zero` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* The slice is a mixed model operator. The frames of $D$ are integral at the finite places, so this operator commutes with the projection on the vacua at each finite place. $\square$

**Theorem (The zero term contributes nothing).** Let $D$ be adapted, and let the descents of $Y$ to $W$, twisted by $a$, vanish above $S$. Let $\phi$ be a datum on $\mathrm{Hom}(W', V)$ that is the vacuum at $S$. Then for every $g \in U(W')(\mathbb{A})$,

$$\int_{[U(V)]} \theta_W\big(\mathrm{homSlice}\ 0\ (\omega_{a\upsilon_1^{p}}(g, h)\phi)\big)\, Y(h)\, dh = 0.$$

Lean: `New.SiegelWeil.DescentsVanish.integral_homSlice_eq_zero` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* By the Iwasawa decomposition of $D$, $g\kappa = n\, m(u, g_0)$, with $\kappa$ in the maximal compact subgroup, $n$ in the unipotent radical and $m(u, g_0)$ in the Levi subgroup $GL_p \times U(W)$. Let $\phi' = \omega(\kappa^{-1}, 1)\phi$. It is again the vacuum at $S$, since $\kappa$ is integral there. On the slice at $0$, the unipotent element acts trivially. The Levi element acts by

$$\mathrm{homSlice}\ 0\ (\omega(g, h)\phi) = \nu\, \omega_a(g_0, h)\big(\mathrm{homSlice}\ 0\ \phi'\big), \qquad \nu = \chi_n(\det u)^{-1}\sqrt{|\det u|}^{\,n},$$

with $\chi_n$ the space character. This is the slice law of [Lagrangians and zero terms](/chapter/siegel-weil/#lagrangians-and-zero-terms); the twist $\upsilon_1^p$ cancels the character that the Levi part gives on the slice. So the integral is $\nu$ times the descent of $Y$ to $W$ at $g_0$ by $\mathrm{homSlice}\ 0\ \phi'$. By the lemma on slices of vacua, this datum is the vacuum at $S$. So the descent is $0$. $\square$

### The remainder is bounded

Now let $p$ be one point, so $W' = W \oplus \mathbb{H}$, and let $\ell = \theta_{W'} - \theta_0$.

**Lemma (Four facts on the remainder).**

1. If $|\theta(\phi) - \theta(\varrho(kb)\phi)| \leq B$ for every adelic $b$, then $|\ell(\phi)| \leq B$. Here $\varrho$ is the action of translations on data.
2. $\ell$ is invariant under the translations by the rational maps $z\, k^* J_{W'}$, for every rational column $z$.
3. For every $g$ there is a rational $\gamma$ such that, if $\mathrm{ht}(g) > 2$, then $k$ lies in the lattice of $W'$ moved by $\gamma g$, with length at most $2/\mathrm{ht}(g)$.
4. Let $d$ be a basis of $V$. The mean of $u \mapsto \ell(\varrho(u)\phi)$ over the adelic points of the span of the maps $d_j\langle k, \cdot\rangle$, modulo the rational points, is $0$.

Lean: `New.SiegelWeil.norm_theta_sub_zeroTerm_le`, `New.SiegelWeil.theta_sub_zeroTerm_rho_ratMap`, `New.SiegelWeil.exists_col_k_mem_latticeBall`, `New.SiegelWeil.subspaceMean_theta_sub_zeroTerm_eq_zero` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* (1) The zero term is the mean of $b \mapsto \theta(\varrho(kb)\phi)$ over the compact quotient of the adelic points $b$ modulo the rational ones. So $\ell(\phi)$ is the mean of $\theta(\phi) - \theta(\varrho(kb)\phi)$, and the mean of a function bounded by $B$ is bounded by $B$.

(2) $\theta$ is invariant under rational translations. The translation by $z\, k^*J_{W'}$ lies in the span of the isotropic frame of $\mathrm{Hom}(W', V)$, and the zero term is invariant under translations along this frame.

(3) If $\mathrm{ht}(g) \leq 2$, take $\gamma = 1$; the claim is empty. Otherwise the lemma on short isotropic vectors of [growth, convergence and adjointness](/chapter/theta-lifts-seesaw/#growth-convergence-and-adjointness) gives a rational isotropic $\xi \neq 0$ in the lattice moved by $g$, of length at most $2/\mathrm{ht}(g)$. By Witt's theorem there is a rational $\gamma \in U(W')$ with $\gamma\xi = k$. The element $\gamma$ carries the lattice and the length at $g$ to those at $\gamma g$.

(4) Since $d$ is invertible, the span of the maps $d_j\langle k, \cdot\rangle$ is the span of the isotropic frame of $\mathrm{Hom}(W', V)$. It is isotropic, and by (2) $\ell$ is invariant under its rational points. So the mean is the mean along the frame. At the translate by $kb$, $\ell$ is $\phi(kb) - \theta_0(\phi)$, and the mean of $\phi(kb)$ over $b$ is $\theta_0(\phi)$. The difference is $0$. $\square$

**Theorem (A uniform bound).** Let $A$ be disjoint from its conjugate, $\Psi$ Schwartz-Bruhat at $A$ and $\phi = v_P \otimes \Psi \otimes \mathrm{vac}$. Let $\chi$ be any character of $U(1)$. There is $K$ such that for every $g \in U(W')(\mathbb{A})$ there is a rational $\gamma$ with

$$|\ell(\omega_\chi(\gamma g, h)\phi)| \leq K \quad\text{for all } h \in U(V)(\mathbb{A}).$$

Lean: `New.SiegelWeil.exists_norm_theta_sub_zeroTerm_le` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* We use two results of [growth, convergence and adjointness](/chapter/theta-lifts-seesaw/#growth-convergence-and-adjointness). The first is moderate growth: $|\theta(\omega(g, h)\phi)| \leq C\|\phi\|(\mathrm{ht}(h)\mathrm{ht}(g))^i$. The second is the decay estimate `exists_norm_pairWeil_schrodingerOp_mul_pow_le`: if $\ell \circ \omega(g, h)$ has moderate growth and, for $\mathrm{ht}(g) > 2$, a "short pair" of rational vectors exists, then $|\ell(\omega(g,h)\phi)|$ is bounded by $C'$ times a moment of $v_P$ times a power of $\mathrm{ht}(h)$.

Take $\gamma$ from fact 3, and $g' = \gamma g$. As $\gamma$ is rational, the kernel at $g'$ is the kernel at $g$, so moderate growth holds at $g'$ with $\mathrm{ht}(g)$. By fact 1, applied to the two terms, $\ell$ has the growth bound with the constant $2C$. Let $d$ be a basis of $V$ in the lattice at $h$, of length at most $c\,\mathrm{ht}(h)$. If $\mathrm{ht}(g) > 2$, then $(d, k)$ is a short pair. Its source vectors are short by fact 3, its frame is isotropic, $\ell$ is invariant by fact 2, and the mean is $0$ by fact 4. So the decay estimate applies. Since $V$ is definite, $\mathrm{ht}(h) = 1$. So the bound $K = C' \cdot (\text{moment of } v_P)$ does not depend on $g$ or $h$. $\square$

**Theorem (Bounded descents).** Let $A$ be disjoint from its conjugate, let $Y$ be automorphic, and let the descents of $Y$ to $W$, twisted by $a$, vanish above $(A \cup \bar A)^c$. Let $D$ be an adapted splitting of $W'$ into $W$ and one plane. Then for $\phi = v_P\otimes\Psi\otimes\mathrm{vac}$, with $\Psi$ Schwartz-Bruhat at $A$, the descent of $Y$ to $W'$ by $\phi$, twisted by $a\upsilon_1$, is bounded.

Lean: `New.SiegelWeil.DescentsVanish.bddAbove_lift` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* The datum $\phi$ is the vacuum off $A \cup \bar A$. Let $|Y| \leq B$; $Y$ is bounded since it is rapid on the compact quotient. Fix $g$, and take $\gamma$ and $K$ from the uniform bound. The lift is left invariant under rational points, so the descent at $g$ is the descent at $\gamma g$. By the theorem on the zero term, with one plane, the integral against $\theta_0$ at $\gamma g$ is $0$. So the descent at $g$ is

$$\int_{[U(V)]} \ell(\omega(\gamma g, h)\phi)\, Y(h)\, dh,$$

and its modulus is at most $K\, B \cdot \mathrm{vol}[U(V)]$. $\square$

### The tower

**Lemma (No planes).** If $p$ is empty and the descents of $Y$ to $W$ vanish above $S$, then the descents to $W'$ vanish above $S$.

Lean: `New.SiegelWeil.DescentsVanish.of_isEmpty` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* With an empty frame, the zero term is the whole kernel: $\theta_W(\mathrm{homSlice}\ 0\ \psi) = \theta_{W'}(\psi)$. The theorem on the zero term gives the claim. $\square$

**Theorem (The tower).** Let $A$ be disjoint from its conjugate, $\Sigma = A \cup \bar A$, and let the descents of the automorphic function $Y$ to $W$, twisted by $a$, vanish above $\Sigma^c$. Let $D$ be an adapted splitting of $W'$ into $W$ and $p$ planes. Let $w$ be a split place off $\Sigma$, with the base change of $a$ unramified at $\bar w$. Let $Y$ be spherical at $w$ with $H_w(X)Y = 0$, where

$$|X| = \big(\sqrt q^{\,r}\, q^{\,n - r - 1}\big)^{-1}.$$

If $2r + 2\#p + 3 < n$, then the descents of $Y$ to $W'$, twisted by $a\,\upsilon_1^{\#p}$, vanish above $\Sigma^c$.

Lean: `New.SiegelWeil.descentsVanish_add_planes` (New/OneLift/FalseLifts/HyperbolicPlaneStep.lean).

*Proof.* Induction on $l = \#p$. If $l = 0$, use the lemma on no planes.

Let $\#p = l + 1$. By the theorem on special data of [Section 3](/chapter/false-lifts/#data-and-small-classes), it suffices to show that the descent $F$ of $Y$ by $\phi = v_P\otimes\Psi\otimes\mathrm{vac}$, twisted by $\chi = a\upsilon_1^{l+1}$, is $0$. Remove one plane from $D$: this gives an adapted splitting of $W'$ into $W_l = W \oplus \mathbb{H}^l$ and one plane (`exists_isBaseAdapted_comp_removePlanes`). The rank condition for $l$ follows from the one for $l + 1$. So by induction, the descents of $Y$ to $W_l$, twisted by $a\upsilon_1^l$, vanish above $\Sigma^c$. The theorem on bounded descents shows that $F$ is bounded.

The character $\upsilon$ is unramified at $\bar w$, so $\chi$ is unramified there. The datum $\phi$ is the vacuum at $\bar w$, as $\bar w \notin \Sigma$. The rank of $W'$ is $m = r + 2(l + 1)$, and $n = m + k$ with $k \geq 0$. Write $|X| = \sqrt q^{\,-d}$ with $d = r + 2(n - r - 1)$. For $j \leq d$, $\sqrt q^{\,j}|X| \leq 1$. As computed at the end of [Section 5](/chapter/false-lifts/#small-roots), both exponents $m + 2k$ and $2(m + 1) + k$ are at most $d$. So the theorem on bounded descents of a Hecke eigenfunction gives $F = 0$. $\square$

**Remark (Formalization).** The induction runs over the cardinality $l$, with the type $p$ and the space $W'$ generalized. The twist $a\,\upsilon_1^{\#p}$ is a product of characters of $U(1)$; for $p = $ `Unit` it is $a\upsilon_1$, which is the form used in `bddAbove_lift`. The hypothesis on $|X|$ is an equality, but only the upper bound $|X| \leq \sqrt q^{\,-d}$ is used.
