---
title: The induced character
lean:
  - New/Spanning/Unfolding/Moments.lean
decls:
  - New.Filling.mem_besselU_of_reduction_eq_one
  - New.Filling.reducedChar
  - New.Filling.reducedCharMean
  - New.Filling.reducedCharMean_conj
  - New.Filling.trace_besselTranslate_eq_mul_reducedChar
  - New.Filling.extendedBesselChar_toPlaces_eq_reducedChar
  - New.Filling.integral_extendedBesselChar_conj_eq
  - New.Filling.sum_sq_norm_integral_extendedBesselChar_conjugate_le
  - New.Filling.inv_ideleM_mem_integralOff
  - New.Filling.sum_norm_reducedCharMean_sq_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The induced character

The good forms of [the next section](/chapter/moments/#good-forms) need the trace of $r_\psi(x) = \sum_tx(t)r_\psi(t)$ for a central idempotent $x$ of one factor. This section shows that the trace of $r_\psi(s)$ is $D_X$ times the Bessel character $\psi_U$ on the reduction of the unipotent group, and that the mean $\psi_U^\natural$ of $\psi_U$ over conjugates is small in $\ell^2(\bar G)$: $\sum_s|\psi_U^\natural(s)|^2 \leq 2$. The function $\#\bar G\,\psi_U^\natural$ is, up to a normalization, the character of the representation of $\bar G$ induced from $\psi_U$. A bound of this kind in $\ell^2$ says that the induced representation has few multiplicities. The proof does not use the representation theory of $\mathrm{GL}_r$ over finite fields. It transfers the question to the finite places, where [the mass integral](/chapter/finite-densities/#shells-decay-and-mass) of the finite Bessel vector gives the bound.

Throughout, $E$ carries Weil data, which include a primitive root of unity of order $5040$, and $S$ is admissible, unless a result says less. $K_S$ is the stabilizer of the lattice in the finite adelic group, and $\mathrm{red} : K_S \to \bar G$ the reduction, which is onto for admissible data ([the standing hypotheses](/chapter/poincare-series/#the-data-are-admissible)).

### The character on $\bar G$

**Lemma (Unipotent elements of the class groups).** Let $\gamma \in R_0$, let $c$ be a class, and let $k = h_c^{-1}\gamma h_c$ lie in $K_S$. If $\mathrm{red}(k)_j = 1$ for one $j \in \{0, 1\}$, then $k$ lies in the unipotent group $\mathsf{U}$.

Lean: `New.Filling.mem_besselU_of_reduction_eq_one` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Write $\gamma = u\eta$ with $u \in \mathsf{U}$ and $\eta$ in the unitary group of $X_0$. Put $y = h_c^{-1}\eta h_c$, a finite adelic point of $U(X_0)$. Then $ky^{-1} = h_c^{-1}uh_c$ lies in $\mathsf{U}$, because the class representatives normalize $\mathsf{U}$. An element of $\mathsf{U}\cdot U(X_0)$ that lies in $K_S$ has both factors in $K_S$, and each entry of $y$ is an entry of $k$ or of the identity matrix. So $y \in K_S$, and $y$ reduces to $1$ at the chosen places above $p_j$. Freeness ([Lemma](/decl/New.Filling.eq_one_of_reduceAt_eq_one/)) in the $k$ variables of $X_0$ gives $\eta = 1$. So $k = h_c^{-1}uh_c \in \mathsf{U}$. $\square$

**Definition (The reduced character).** For $s \in \bar G$, if there is $k \in K_S \cap \mathsf{U}$ with $\mathrm{red}(k) = s$, then $\psi_U(s) = \chi(k)$, the unipotent character at such a $k$. Otherwise $\psi_U(s) = 0$.

Lean: `New.Filling.reducedChar` (New/Spanning/Unfolding/Moments.lean).

**Remark (Formalization).** The source picks the element $k$ with `choose`. The value $\chi(k)$ does not depend on the choice: this follows from the lemma below on the character at the finite places, whose left side does not mention $k$. So $\psi_U$ is the function of the textbook, extended by $0$ off the image $\bar U_0$ of $K_S \cap \mathsf{U}$.

**Definition (The mean over conjugates).** $\psi_U^\natural(s) = \frac{1}{\#\bar G}\sum_{g \in \bar G}\psi_U(gsg^{-1})$.

Lean: `New.Filling.reducedCharMean` (New/Spanning/Unfolding/Moments.lean).

**Lemma (A class function).** $\psi_U^\natural(gsg^{-1}) = \psi_U^\natural(s)$.

Lean: `New.Filling.reducedCharMean_conj` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Substitute $g \mapsto g'g^{-1}$ in the mean. $\square$

**Theorem (The trace of $r_\psi$).** Let $s \in \bar G$ with $s_j = 1$ for one $j$. Then $\operatorname{tr}r_\psi(s) = D_X\,\psi_U(s)$.

Lean: `New.Filling.trace_besselTranslate_eq_mul_reducedChar` (New/Spanning/Unfolding/Moments.lean).

*Proof.* By [the lemma on the trace](/decl/New.Filling.trace_besselTranslate/), $\operatorname{tr}r_\psi(s) = \sum_{(c, i)}\mathcal{A}_{R_0}(c, s^{-1}, c)_{i, i}/\nu$.

First let $s = \mathrm{red}(k)$ with $k \in K_S \cap \mathsf{U}$. The scalar law ([Theorem](/decl/New.Filling.amplitudeSum_besselU_mul/)) for the stable set $R_0$, with $u = 1$ and $u' = k$, gives $\mathcal{A}_{R_0}(c, s^{-1}, c) = \chi(k)\mathcal{A}_{R_0}(c, 1, c)$. The identity block is $\nu$ on the diagonal. So each of the $D_X$ summands is $\chi(k) = \psi_U(s)$.

Now let $s$ not be such a reduction. Suppose that $\gamma \in R_0$ is a term over $(c, s^{-1}, c)$, with $k = h_c^{-1}\gamma h_c \in K_S$ of reduction $s^{-1}$. Then $\mathrm{red}(k)_j = 1$, so $k \in \mathsf{U}$ by the lemma above. Then $k^{-1} \in K_S \cap \mathsf{U}$ has the reduction $s$, a contradiction. So all blocks are sums over the empty set, and both sides are $0$. $\square$

### The transfer to the finite places

Let $T$ be a finite conjugation-stable set of finite places such that $M^{-1}$ is integral off $T$. Let $F$ be filling data at $T$ ([Definition](/decl/New.Filling.IsFillingData/), in [the chapter on the main term](/chapter/main-term/#the-place-at-t-and-filling-data)). Let $K$ be the integral points of the group at $T$, $K(M)$ the principal congruence subgroup of level $M$, and $dy$ the measure of $F$. The function $\chi_M$ is $\psi(\sigma(u)/M)$ on $uK(M)$ for $u \in \mathsf{U}$, with $\sigma(u)$ the sum of the entries at the simple roots, and $0$ off $\mathsf{U}K(M)$ ([Definition](/decl/New.Floors.IntegralPlace.extendedBesselChar/), in [the finite Bessel vector](/chapter/finite-densities/#the-finite-bessel-vector)). We write $l_T$ for the component at $T$ of $l \in K_S$. Two facts about filling data are used ([the section on Kloosterman sums](/chapter/main-term/#kloosterman-sums-and-unfolding)): $\mathrm{red}(k) = \mathrm{red}(l)$ if and only if $k_T^{-1}l_T \in K(M)$; and for $k$ integral off $T$ in $\mathsf{U}$, $\psi(\sigma(k_T)/M) = \chi(k)$.

**Lemma (The character at the finite places).** For $l \in K_S$, $\chi_M(l_T) = \psi_U(\mathrm{red}(l))$.

Lean: `New.Filling.extendedBesselChar_toPlaces_eq_reducedChar` (New/Spanning/Unfolding/Moments.lean).

*Proof.* If $\mathrm{red}(l) = \mathrm{red}(k)$ with $k \in K_S \cap \mathsf{U}$, then $k_T \in \mathsf{U}$ and $k_T^{-1}l_T \in K(M)$. So $\chi_M(l_T) = \psi(\sigma(k_T)/M) = \chi(k) = \psi_U(\mathrm{red}(l))$ ([Lemma](/decl/New.Floors.IntegralPlace.extendedBesselChar_eq/)).

Otherwise $\psi_U(\mathrm{red}(l)) = 0$. Suppose $\chi_M(l_T) \neq 0$. Then $u^{-1}l_T \in K(M)$ for some $u \in \mathsf{U}$ at $T$. Lift $u$ to $k \in \mathsf{U}$ integral off $T$ with $k_T = u$ ([Theorem](/decl/New.Filling.exists_isIntegralOff_toPlaces_eq/)). Then $k_T \in l_TK(M) \subset K$, so $k \in K_S \cap \mathsf{U}$ and $\mathrm{red}(k) = \mathrm{red}(l)$. This is a contradiction. $\square$

**Lemma (The integral over conjugates).** For $l \in K_S$,

$$\int_K\chi_M(yl_Ty^{-1})\,dy = \mathrm{vol}(K)\,\psi_U^\natural(\mathrm{red}(l)).$$

Lean: `New.Filling.integral_extendedBesselChar_conj_eq` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Put $\varphi(y) = \chi_M(yl_Ty^{-1})$. For each $g \in \bar G$ choose $\sigma(g) \in K_S$ with $\mathrm{red}(\sigma(g)) = g$. As $\sigma(g)_T \in K$ and the measure is invariant under left translation, $\int_K\varphi(\sigma(g)_Ty)\,dy = \int_K\varphi(y)\,dy$. Sum over $g$:

$$\#\bar G\int_K\varphi\,dy = \sum_g\int_K\varphi(\sigma(g)_Ty)\,dy = \int_K\sum_g\varphi(\sigma(g)_Ty)\,dy.$$

The exchange of the finite sum and the integral needs each summand to be integrable on $K$. The function $\chi_M$ is continuous, so each summand is continuous, and $K$ is compact. Now fix $y \in K$ and write $y = k_T$ with $k \in K_S$ (the theorem on lifts). By the previous lemma,

$$\sum_g\varphi(\sigma(g)_Tk_T) = \sum_g\psi_U\bigl(g\,\mathrm{red}(k)\,\mathrm{red}(l)\,\mathrm{red}(k)^{-1}g^{-1}\bigr) = \#\bar G\,\psi_U^\natural(\mathrm{red}(l)),$$

since $\psi_U^\natural$ is a class function. So the integrand is constant on $K$. Integrate and cancel $\#\bar G$. $\square$

**Remark (Formalization).** The family $\sigma$ is chosen with `choose` from the surjectivity of the reduction. The result does not depend on the choice. In Lean an integral of a function that is not integrable is $0$; the proof shows integrability, so the identity is not an identity of junk values.

**Lemma (The $\ell^2$ bound at the finite places).** Let $T$, $F$ be as above, and let $T$ be a subset of the set of chosen places and their conjugates. Let $(\sigma_s)_{s \in I}$ be a finite family in $K_S$ whose reductions are distinct. Put $a(z) = \int_K\chi_M(yzy^{-1})\,dy$. Then

$$\sum_{s \in I}|a(\sigma_{s, T})|^2 \leq 2\,\mathrm{vol}(K)^2.$$

Lean: `New.Filling.sum_sq_norm_integral_extendedBesselChar_conjugate_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Let $C_s = \sigma_{s, T}K(M)$. For $z \in C_s$ and $y \in K$, $yzy^{-1} \in y\sigma_{s, T}y^{-1}K(M)$, as $K(M)$ is normal in $K$, and $\chi_M$ is invariant under right translation by $K(M)$ ([Lemma](/decl/New.Floors.IntegralPlace.extendedBesselChar_mul_of_mem_unitaryLevel/)). So $a$ is constant on $C_s$. The cosets $C_s$ are disjoint, because $\sigma_{s, T}^{-1}\sigma_{t, T} \in K(M)$ means $\mathrm{red}(\sigma_s) = \mathrm{red}(\sigma_t)$. In $[0, \infty]$

$$\Big(\sum_s|a(\sigma_{s, T})|^2\Big)\mathrm{vol}(K(M)) = \sum_s\int_{C_s}|a|^2 = \int_{\bigcup_sC_s}|a|^2 \leq \int|a|^2 = \varkappa(K).$$

The second equality is additivity of the integral of a nonnegative function over disjoint measurable sets. The mass integral satisfies $\varkappa(K) \leq \mathrm{vol}(K)\mathrm{vol}(K(M))(\mathrm{vol}(K) + 2^{-n})$ ([Theorem](/decl/New.Floors.IntegralPlace.IsLargeLatticeData.massIntegral_le_main_add_error/) with $Q = 2$ and $t = n$). Its rank condition $n + 2\cdot 10^9n^4 \leq k$ follows from the chain of inequalities of the shape. The places of $T$ have large norm, so the non-units have small volume, and $2^{-n} \leq \mathrm{vol}(K)$ ([Theorem](/decl/New.Floors.IntegralPlace.IsLargeLatticeData.inv_two_pow_le_groupMeasure/)). So the right side is at most $2\mathrm{vol}(K)^2\mathrm{vol}(K(M))$. As $K(M)$ is open and compact, $0 < \mathrm{vol}(K(M)) < \infty$, and we can divide. $\square$

**Remark (Formalization).** The computation is in $[0, \infty]$, with the integrals `lintegral` of $\|a\|_e^2$. There every sum and every integral has a value, and the additivity over the countable disjoint family $(C_s)$ holds with no condition. The passage back to real numbers uses $\mathrm{vol}(K) < \infty$ and $\mathrm{vol}(K(M)) < \infty$. These are the second and third exchanges named in [the conventions](/chapter/moments/#what-the-chapter-proves).

**Lemma (The level is a unit off $T$).** If $T$ contains every chosen place and its conjugate, then $M^{-1}$ is integral off $T$.

Lean: `New.Filling.inv_ideleM_mem_integralOff` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Let $r$ be the idele that is $1$ off $T$ and $0$ on $T$. Then $M^{-1}r$ is integral if $r$ vanishes modulo each chosen place and each conjugate (`New.Filling.inv_ideleM_smul_mem_iff`), which holds. $\square$

The lemma uses neither admissibility nor Weil data.

### The bound for the induced character

**Theorem (The induced character).** $\sum_{s \in \bar G}|\psi_U^\natural(s)|^2 \leq 2$.

Lean: `New.Filling.sum_norm_reducedCharMean_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Let $T$ be the set of chosen places and their conjugates. It is stable under conjugation, and $M^{-1}$ is integral off $T$ by the previous lemma. Choose filling data $F$ at $T$ ([Theorem](/decl/New.Filling.exists_isFillingData/)). Choose $\sigma(s) \in K_S$ with $\mathrm{red}(\sigma(s)) = s$; the reductions are distinct. By the integral over conjugates, $a(\sigma(s)_T) = \mathrm{vol}(K)\psi_U^\natural(s)$. The $\ell^2$ bound gives

$$\mathrm{vol}(K)^2\sum_s|\psi_U^\natural(s)|^2 \leq 2\,\mathrm{vol}(K)^2.$$

As $K$ is open, compact and nonempty, $0 < \mathrm{vol}(K) < \infty$. Divide. $\square$

The constant $2$ is $1 + 1$: the main term $\mathrm{vol}(K)$ of the mass integral and the error $2^{-n}$, which is at most $\mathrm{vol}(K)$. The theorem holds with no assumption on the size of $b$ beyond admissibility. The statement itself mentions only $\bar G$; the filling data $F$ and the set $T$ are tools of the proof.
