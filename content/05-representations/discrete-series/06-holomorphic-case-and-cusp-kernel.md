---
title: The holomorphic case, the cusp kernel and the character wave
lean:
  - Lib/DiscreteSeries/FlenstedJensen/Defs.lean
  - Lib/DiscreteSeries/Holomorphic/ModelFunction.lean
  - Lib/DiscreteSeries/Holomorphic/PeaksAwayFromCusp.lean
  - Lib/DiscreteSeries/CuspKernel.lean
  - Lib/General/Analysis/HolomorphicIntegrals.lean
  - Lib/General/Groups/BesselGroups.lean
  - Lib/Adelic/Adeles/AdditiveCharacter.lean
  - New/Spanning/MainTerm/GlobalSieve.lean
decls:
  - New.IsKDominant
  - New.IsPosFirstOrder
  - New.HasHolGap
  - New.IsHolOfWeight
  - New.holMinors
  - New.holMinorsPi
  - New.holMinors_ite_sign
  - New.isHolOfWeight_holMinorsPi
  - New.IsHolOfWeight.integral_mul_conj_holMinorsPi
  - New.IsHolOfWeight.eq_holMinorsPi_mul
  - New.dsCoeff_eq_holMinors_lowestKType
  - New.dsCoeff_eq_holMinors
  - New.Rows.IsPeak.le_firstMinimum
  - New.DiscreteSeries.integral_idempotentKernel_mul_eq_zero
  - New.hua_integral_le
  - New.wave
  - New.norm_wave
  - New.stdAddChar
  - New.Filling.wave_two_pi_I_mul
  - New.Filling.stdAddChar_div_deltaE
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The holomorphic case, the cusp kernel and the character wave

This section treats the holomorphic chamber, where $c_\lambda$ is a quotient of principal minors that reproduces holomorphic functions. Then it gives the peaks of holomorphic forms, the vanishing of constant terms, Hua's integral, and the answer to the spec question Q-68.

### Holomorphic functions on the group

Classically a discrete series representation of $U(p,q)$ is holomorphic when its Harish-Chandra parameter lies in a chamber for which all noncompact positive roots are of one type. Then the representation is a space of holomorphic sections over the bounded symmetric domain $G/K$, and its lowest $K$-type has a simple coefficient. Section 2 gave the case $U(1,1)$. The source does not use the domain. It works on the group and expresses holomorphy by an analytic extension to complex matrices.

Fix the signs $\varepsilon$ and an order $o : n \to \mathbb Z$ on the indices.

**Definition.** The order $o$ *puts the signs $+1$ first* if $o$ is injective and $o(i) < o(j)$ whenever $\varepsilon_i = 1$ and $\varepsilon_j = -1$.

Lean: `New.IsPosFirstOrder` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

**Definition.** A weight $w : n \to \mathbb Z$ is *$K$-dominant* for $o$ if $w_j \le w_i$ whenever $\varepsilon_i = \varepsilon_j$ and $o(i) < o(j)$. So $w$ decreases weakly along $o$ inside each block of equal signs.

Lean: `New.IsKDominant` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

**Definition.** A weight $w$ has the *holomorphic gap* $\gamma$ if $w_i + \gamma \le w_j$ whenever $\varepsilon_i = 1$ and $\varepsilon_j = -1$.

Lean: `New.HasHolGap` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

The source works on a product $G^\Phi$ of copies of $G = U(\operatorname{diag}\varepsilon)$, indexed by a set $\Phi$. Later volumes take for $\Phi$ the infinite places of a CM field. A weight is then a family $u = (u_\tau)_{\tau \in \Phi}$.

**Definition.** A function $F$ on $G^\Phi$ is *holomorphic of weight $u$* if there is a function $F'$ on families of complex matrices with this property: for every $h \in G^\Phi$ and every family $b$ of matrices that are triangular for $o$, with $h_\tau$ and $b_\tau$ in the block diagonal algebra for a second set of signs $\varepsilon'$, $F'$ is complex analytic at $z = (h_\tau b_\tau)_\tau$, and
$$F'(z) = \prod_{\tau \in \Phi} \chi_{u_\tau}(b_\tau)\, F(h),$$
where $\chi_{u_\tau}(b)$ is the character $\prod_i b_{ii}^{u_\tau(i)}$ of the diagonal of $b$. The default value of $\varepsilon'$ is the constant $1$, and then the block condition is empty.

Lean: `New.IsHolOfWeight` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

So $F$ extends to the complexification and transforms under a Borel subgroup by a character.

### The model function

**Definition.** For a weight $w$ and a matrix $b$, put $c_i = 2\sum_j |w_j|$ if $\varepsilon_i = 1$ and $c_i = 0$ otherwise. Then
$$\operatorname{holMinors}_\varepsilon(w)(b) = \frac{m_{w+c}(b)}{m_c(b)},$$
where $m$ is the product of principal minors of Section 3. For a family $u$ and $h \in G^\Phi$, $\operatorname{holMinorsPi}_\varepsilon(u)(h) = \prod_\tau \operatorname{holMinors}_\varepsilon(u_\tau)(h_\tau)$.

Lean: `New.holMinors` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

Lean: `New.holMinorsPi` (Lib/DiscreteSeries/FlenstedJensen/Defs.lean).

The shift $c$ makes both weights $w + c$ and $c$ dominant, so both products of minors are polynomials. At a singular matrix `New.weightMinors` has the junk value $1$ (Section 3), and where the denominator is $0$ the quotient is $0$ by the Lean convention for division. On $G$ the relevant minors do not vanish, because the principal minor of $g \in U(p,q)$ on the indices of sign $+1$ has absolute value at least $1$.

**Theorem.** Let $a \le b$ be integers, and let $w$ be the weight with $w_i = a$ when $\varepsilon_i = 1$ and $w_i = b$ otherwise. Then for $g \in G$,
$$\operatorname{holMinors}_\varepsilon(w)(g) = \frac{(\det g)^b}{\Delta_+(g)^{b-a}},$$
where $\Delta_+(g)$ is the principal minor of $g$ on the indices of sign $+1$.

Lean: `New.holMinors_ite_sign` (Lib/DiscreteSeries/Holomorphic/ModelFunction.lean).

For $U(1,1)$ with $\varepsilon = (1,-1)$, $w = (w_1, w_2)$ and $k = w_2 - w_1$, this gives $g_{11}^{-k}(\det g)^{w_2}$. This is the coefficient of the holomorphic discrete series of weight $k$ in Section 2.

**Theorem.** Let $o$ put the signs $+1$ first, and let each $u_\tau$ be $K$-dominant for $o$. Then $\operatorname{holMinorsPi}_\varepsilon(u)$ is holomorphic of weight $u$.

Lean: `New.isHolOfWeight_holMinorsPi` (Lib/DiscreteSeries/Holomorphic/ModelFunction.lean).

### The reproducing formula

**Theorem.** Let $o$ put the signs $+1$ first, let each $u_\tau$ be $K$-dominant for $o$, and let $F$ be holomorphic of weight $u$. Put $m = \operatorname{holMinorsPi}_\varepsilon(u)$. If $F \overline m$ is integrable for the measure on $G^\Phi$, then
$$\int_{G^\Phi} F(h)\,\overline{m(h)}\,dh = \Big(\int_{G^\Phi} |m(h)|^2\,dh\Big)\, F(1).$$

Lean: `New.IsHolOfWeight.integral_mul_conj_holMinorsPi` (Lib/DiscreteSeries/Holomorphic/ModelFunction.lean).

*Proof.* For $\theta$ in the circle let $r_\theta \in G^\Phi$ be the diagonal matrix with entries $\theta^{o(i)}$ in each factor. Left translation by $r_\theta$ preserves the measure, so the integral is equal to the integral over $h$ of the mean over $\theta$ of $F(r_\theta h)\overline{m(r_\theta h)}$. Under the torus, $m$ moves by a character: $\overline{m(r_\theta h)}$ is $\overline{m(h)}$ times the inverse of the character of weight $u$ at $r_\theta$. A lemma on circle means (`New.IsHolOfWeight.circle_mean_holMinorsPi`) uses the analytic extension of $F$ and gives the mean of $F(r_\theta h)$ against this inverse character as $m(h) F(1)$. So the inner mean is $m(h)F(1)\overline{m(h)} = |m(h)|^2 F(1)$. Integrate over $h$. $\square$

When $F$ also satisfies $F(g^{-1}) = \overline{F(g)}$, the source gets more: $F$ is a multiple of the model function.

**Theorem.** Let $o$ put the signs $+1$ first, let each $u_\tau$ be $K$-dominant for $o$, and let $F$ be holomorphic of weight $u$ with $F(g^{-1}) = \overline{F(g)}$ for all $g$. Then $F(h) = \operatorname{holMinorsPi}_\varepsilon(u)(h)\, F(1)$ for all $h$.

Lean: `New.IsHolOfWeight.eq_holMinorsPi_mul` (Lib/DiscreteSeries/Holomorphic/ModelFunction.lean).

The symmetry turns the law for right translation by the torus into a law for left translation. No integrability is necessary.

### The coefficient in the holomorphic chamber

The next two results connect the model function with the coefficient $c_\lambda$ of Section 3.

**Theorem.** Let $l$ be a parameter with a gap $h$, and let $o$ put the signs $+1$ first. Suppose that $l_j < l_i$ when $\varepsilon_i = \varepsilon_j$ and $o(i) < o(j)$, and that $l_i < l_j$ when $\varepsilon_i = 1$ and $\varepsilon_j = -1$. Then $c_l(g) = \operatorname{holMinors}_\varepsilon(\Lambda)(g)$ for every $g \in G$, where $\Lambda$ is the highest weight of the lowest $K$-type of $l$.

Lean: `New.dsCoeff_eq_holMinors_lowestKType` (Lib/DiscreteSeries/Holomorphic/ModelFunction.lean).

*Proof.* Both sides are real analytic on $G$: the left side by `New.HCParam.analyticAt_dsCoeff` (Section 4), the right side because it is a quotient of polynomials with a denominator that does not vanish on $G$. So it is sufficient to prove the equality near $1$. Near $1$ write $g = x' a x$, where $a$ is block diagonal, and $x' - 1$ and $x - 1$ lie in the two off diagonal corner blocks. In the order $o$, $x'$ is lower unipotent and $x$ is upper unipotent, so the character of every weight is $1$ at $x'$ and at $x$. The integral of Flensted-Jensen is invariant under these corner factors, by the conditions on $l$ across the signs. So $c_l(g) = c_l(a)$. On block diagonal $a$ near $1$ the integral over $K$ can be computed, and it gives $\operatorname{holMinors}_\varepsilon(\Lambda)(a)$. The model function has the same invariance under $x'$ and $x$, by the Borel law for $\operatorname{holMinors}$. $\square$

The main theorem of the holomorphic case states the hypotheses in terms of the weight $w$, not the parameter $l$.

**Theorem.** Let $o$ put the signs $+1$ first, let $A$ and $\gamma$ be natural numbers, and let $w$ be $K$-dominant for $o$ with the holomorphic gap $\gamma$, where $\gamma > 500n^3 + A + n + 1$. Put $l = 2w + 2\rho$, where
$$2\rho(a) = \#\{j : o(a) < o(j)\} - \#\{j : o(j) < o(a)\}.$$
Then $l$ has the large gap $500n^3 + A$, and $c_l(g) = \operatorname{holMinors}_\varepsilon(w)(g)$ for every $g \in G$.

Lean: `New.dsCoeff_eq_holMinors` (Lib/DiscreteSeries/Holomorphic/ModelFunction.lean).

*Proof.* The value of $2\rho$ at the index of rank $r$ in $o$ is $n + 1 - 2r$. So $l$ decreases strictly along $o$ inside each block, because $w$ decreases weakly. Across the blocks $l$ jumps up by at least $2(\gamma - n)$. This gives the large gap and the hypotheses of the previous theorem. A computation of the lowest $K$-type shows that its highest weight is $w$. The previous theorem then applies. $\square$

In Lean the parameter is the expression `2 * w + twoRho (-o) ⊤`. The theorem has the form of a `let` followed by a conjunction. With $\lambda = l/2$, the docstring gives $\lambda_a = w_a + (n+1)/2 - r$ for the index $a$ of rank $r$.

For $U(1,1)$ the theorem gives the following. Take $w = (w_1, w_2)$ with $w_2 - w_1 = k$. The gap condition is $k > 4003 + A$. Then $l = (2w_1 + 1, 2w_2 - 1)$ and $c_l(g) = g_{11}^{-k}(\det g)^{w_2}$. With the computation of Section 2, the formal degree is $k - 1$. The classical result holds for $k \ge 2$, so the bound on $k$ is a cost of the method and not a property of $U(1,1)$.

**Remark (Formalization).** The reproducing formula needs the hypothesis that $F\overline m$ is integrable. The theorem does not supply it, and each use must prove it. For a bounded $F$ the decay bound of Section 4 is the natural tool, because $m = c_l$ in the holomorphic chamber. The formula has no hypothesis on the measure other than left invariance under the torus. So the constant $\int|m|^2$ depends on the normalisation of the measure, and the source identifies it with the inverse formal degree only through `New.dsCoeff_eq_holMinors` and Section 5.

### Peaks away from the cusp

The source uses the holomorphic case to bound where a holomorphic form can be large. Let $E$ be a CM field. Let $F$ be a function on the adelic unitary group $G(\mathbb A_E)$ that is left invariant under the rational points $\Gamma$ of a hermitian space $V$, holomorphic at every translate of a weight $u$, and right invariant under a principal level subgroup for an element $p$. A *peak* of $F$ is a point $g$ where $|F(g)|$ is more than half the supremum of $|F|$.

**Theorem.** Let $o$ put the signs $+1$ first. Let $u$ have the holomorphic gap $1$ at every infinite place $w$, with $|u_w(i)| \le A$ and $A \ge 2$. Let $\bar p = -p$ and $\operatorname{Im}\Phi_w(p) \in (0, A']$ for every infinite place, with $A' \ge 1$. If $F$ is $\Gamma$-invariant, right invariant under the principal level of $p$, holomorphic of weight $u$ in the adelic sense, and $g$ is a peak of $F$, then the first minimum of the lattice $V$ moved by $g$ is at least $(AA')^{-1/2}$.

Lean: `New.Rows.IsPeak.le_firstMinimum` (Lib/DiscreteSeries/Holomorphic/PeaksAwayFromCusp.lean).

The first minimum is the length of the shortest nonzero vector, cut off at $1$. The proof in the source goes as follows. If the first minimum at $g$ is small, a short lattice vector is isotropic. The transvection along it fixes $F(g\,\cdot)$. A Schwarz lemma for the holomorphic function then makes $|F(g)|$ smaller than half the supremum. The source cites Poor and Yuen (Math. Ann. 318, 2000, Theorem 1.3) for the Siegel modular analogue. I have not checked that reference, so I do not give it in the notes.

### The vanishing of constant terms

Classically, the $K$-finite matrix coefficients of an integrable discrete series representation are cusp forms: their constant terms along every proper parabolic subgroup vanish. The file header in the source cites Godement (C. R. Acad. Sci. Paris 225, 1947) and Wallach, Real Reductive Groups I (1988), for this result. The source does not state this theorem. It proves an abstract step that has the same effect for the kernel $e_\lambda$.

**Theorem.** Let $G$ be a second countable locally compact group with a left Haar measure, and let $e$ be an idempotent kernel on $G$ (Section 5). Let $H$ and $\ell$ be real functions on $G$ with $H$ continuous, $|H(xg) - H(x)| \le \ell(g)$ for all $x, g$, and $\|e\|\ell$ integrable. Let $D$ be a subgroup of $G \times \mathbb C^\times$ such that $H(rg) = H(g) - \log|c|$ for $(r, c) \in D$. Suppose that every neighbourhood $W$ of $1$ has a $c$ with $\log|c| \ne 0$ such that for every $x$ some $b \in W$ has $(xbx^{-1}, c) \in D$. Then
$$\int_G e(g)\, f(xg)\,dg = 0$$
for every $x \in G$ and every bounded continuous $f$ with $f(rg) = f(g)$ whenever $(r, 1) \in D$.

Lean: `New.DiscreteSeries.integral_idempotentKernel_mul_eq_zero` (Lib/DiscreteSeries/CuspKernel.lean).

For a unitary group the source takes for $D$ the group `New.dilationGroup A` of an isotropic matrix $A$: the pairs $(g, c)$ with $gA = cA$ and $g$ trivial on the vectors orthogonal to the columns of $A$. The pairs with $c = 1$ form the radical, and the invariant functions $f$ are functions on the quotient by it. The function $H$ is a height that a dilation by $c$ moves by $-\log|c|$. The theorem says that the kernel $e$ kills them. The proof in the source considers the operator $T\varphi(y) = \int e(g)\varphi(yg)\,dg$ and the space $V$ of bounded continuous $\varphi$ that are fixed by $T$ and invariant under the radical. A dilation close to $1$ acts on $V$ as an operator $S$ with $S^n = 0$ and $S$ injective. So $V = 0$, and $Tf \in V$.

**Remark (Formalization).** The docstring of the theorem says that it is a step toward Harish-Chandra's theorem, and that the theorem itself is not stated. The book follows the source here. The same file proves the hypothesis `hD_near` for unitary groups: for an isotropic $A$, every $x$ and every $c > 0$, some $y$ within distance $c$ of $1$ has $xyx^{-1}$ in the dilation group with the factor $1 + c$ (`New.DiscreteSeries.exists_conj_mem_dilationGroup`). The cusp kernel that the source builds from the kernels of discrete series is `New.isCuspKernel_typeKernel`, in Lib/Adelic/AutomorphicForms/RealConvolution.lean. This chapter does not treat it.

### Hua's integral

The integrals over the corner blocks in the holomorphic case lead to integrals of negative powers of determinants. The source bounds them by one lemma, after Hua.

**Theorem.** Let $M$ be a positive definite matrix and $S$ an invertible matrix, both of size $k$. Let $c \ge 0$, let $r \ge k$ be a natural number, let $s$ be a finite set of indices, and put $w_i = y_i S + a_i$ for row vectors $y_i \in \mathbb C^k$. Then the iterated integral over the rows $y_i$, $i \in s$, of
$$c\,\Big|\det\Big(M + \sum_{i \in s} w_i^* w_i\Big)\Big|^{-(|s| + r)}$$
is at most $c\,\big(\pi^k/(k!\,|\det S|^2)\big)^{|s|}\,|\det M|^{-r}$.

Lean: `New.hua_integral_le` (Lib/General/Analysis/HolomorphicIntegrals.lean).

The proof is an induction on $s$: each row is absorbed into $M$ and contributes one factor $\pi^k/(k!\,|\det S|^2)$. The integral is a lower Lebesgue integral of a nonnegative function, so there is no integrability hypothesis.

### The question Q-68: wave is the additive character up to the factor $-2\pi i$

The spec asks whether `wave` is consistent with the additive character used in `Lib/DiscreteSeries`. The answer from the source is yes, after a scaling by $2\pi i$ and a sign.

**Definition.** For $c \in \mathbb C$, $\operatorname{wave}(c) = \exp(c - \bar c)$.

Lean: `New.wave` (Lib/General/Groups/BesselGroups.lean).

**Theorem.** $|\operatorname{wave}(c)| = 1$ for every $c \in \mathbb C$.

Lean: `New.norm_wave` (Lib/General/Groups/BesselGroups.lean).

Since $c - \bar c = 2i\operatorname{Im} c$, $\operatorname{wave}(c) = \exp(2i\operatorname{Im} c)$. This is a continuous unitary character of the additive group $\mathbb C$. Every such character has the form $x \mapsto \operatorname{wave}(\alpha x)$ for one $\alpha \in \mathbb C$. So the question is only which $\alpha$ connects `wave` to the character of the adeles.

**Definition.** For a CM field $E$, the standard additive character of the adeles $\mathbb A_E$ is
$$\psi(x) = \mathbf e\Big(-\sum_{w} 2\operatorname{Re} x_w\Big)\,\psi_f(x_f),$$
where $\mathbf e(t) = \exp(2\pi i t)$, the sum runs over the infinite places, and $\psi_f$ is the standard character of the finite adeles.

Lean: `New.stdAddChar` (Lib/Adelic/Adeles/AdditiveCharacter.lean).

**Theorem.** For $w \in \mathbb C$, $\operatorname{wave}(2\pi i w) = \mathbf e(2\operatorname{Re} w)$.

Lean: `New.Filling.wave_two_pi_I_mul` (New/Spanning/MainTerm/GlobalSieve.lean).

So at a complex place, $x \mapsto \mathbf e(-2\operatorname{Re} x)$ is $x \mapsto \operatorname{wave}(-2\pi i x)$, that is $\alpha = -2\pi i$. The factor $2 \operatorname{Re} x$ is the trace from $\mathbb C$ to $\mathbb R$, as is usual at a complex place. The source uses this in the following identity, where the sign is absorbed into the argument.

**Theorem.** Let $\varpi$ be the generator of the different of $E$ in the filling data. For $y \in E$ and an adele $z$, both integral away from a finite set $T$ of places,
$$\psi\big((y/\varpi)\cdot(-z)\big) = \prod_{w} \operatorname{wave}\Big(\frac{2\pi i}{\Phi_w(\varpi)}\,\Phi_w(y)\,z_w\Big) \cdot \chi_T(y z_T),$$
where $\chi_T$ is the character $x \mapsto \psi_f(-x/\varpi)$ on the product of the completions at $T$.

Lean: `New.Filling.stdAddChar_div_deltaE` (New/Spanning/MainTerm/GlobalSieve.lean).

Inside `Lib/DiscreteSeries`, `wave` occurs in two places. The structure `New.IsBesselFunction` (Lib/DiscreteSeries/Bessel/Basic.lean) asks that $F(ny) = \operatorname{wave}(s(n))F(y)$ for $n$ in a unipotent group, where $s(n)$ is the sum of the entries just above the diagonal on a frame. The instance `New.Floors.complexPlace` (Lib/DiscreteSeries/Bruhat/ComplexPlace.lean) takes `wave` as the character $\psi$ of the local field $\mathbb C$, with Lebesgue measure and the Gaussian kernel $\exp(-|x|^2)$. The files of this chapter, on the coefficient $c_\lambda$, use no additive character. So inside `Lib/DiscreteSeries` there is no second character for `wave` to disagree with. The local files fix one nontrivial character of $\mathbb C$, and the global files connect it to $\psi$ by the two lemmas above. The normalisation $\exp(c - \bar c)$ is not the usual $\mathbf e(\operatorname{Tr} x)$, but it differs from it only by the scaling $c = 2\pi i x$, and the source states this scaling.

**Remark (Formalization).** The research note on the general library calls the normalisation of `wave` unusual. It is a different scaling of the standard character, and the source proves the relation. A reader who compares a Bessel function of the local files with a Whittaker coefficient of an adelic form must insert the factor $-2\pi i$ and the different $\varpi$. The proofs in the source do this through `New.Filling.stdAddChar_div_deltaE`. This section does not check every use of `wave` in the later volumes.
