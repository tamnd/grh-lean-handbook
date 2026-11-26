---
title: The pairs of the tower and the good datum
lean:
  - New/UpperBound/Seesaw/GoodDatum.lean
  - New/UpperBound/Seesaw/AdmissibleEvaluation.lean
decls:
  - New.Seesaw.liftsNeighbours_middleDoubleLift
  - New.Seesaw.matchesDenominators_middleDoubleLift
  - New.Seesaw.lastScaling
  - New.Seesaw.liftsNeighbours_lastDoubleLift
  - New.Seesaw.matchesDenominators_lastDoubleLift
  - New.Data.chosenRatio
  - New.Data.chosenRatio_mul_star
  - New.Data.chosenRatio_apply_of_N_mem
  - New.Data.v_piM_eq_one_of_N_mem
  - New.Data.v_star_piM_mul_chosenRatio
  - New.Data.flipScale_mul_divStar_ideleA
  - New.Data.isScalingAtM_of_eq_one_or_eq
  - New.Data.isScalingAtM_one
  - New.Data.isScalingAtM_lastScaling
  - New.Data.latticeScale_two_mul
  - New.Data.isAdmissibleEval_doubleLiftEvalY
  - New.Seesaw.mulVec_mem_translations
  - New.Seesaw.mem_translations_of_mem_stdLattice
  - New.Seesaw.isAdmissibleCombination_weil_of_mem_localLevel
  - New.Seesaw.exists_arrowProduct_eq_smul_finHeisenbergOp
  - New.Data.piM_mul_normQ_mem_ideal
  - New.Data.isAdmissibleCombination_pointDatumY
  - New.Data.isAdmissibleCombination_translatedPointDatumY
  - New.Data.absNorm_pow_mul_card_dvd_residueMatrixCount_pow
  - New.Data.isAdmissibleCombination_arrowProduct_translatedPointDatumY
  - New.Data.exists_isAdmissibleCombination_evaluatedDatum
  - New.Data.exists_isAdmissibleCombination_gluedVacuum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The pairs of the tower and the good datum

Section 4 proved that $\mathrm{ev}_D$ is admissible under three hypotheses: the frame of $V'$ spans a glued lattice, the lifts lift the neighbours, and the data match the denominators. This section checks the last two for the two kinds of pairs, then for the pairs of the tower with explicit $u$, $\delta$ and $\beta$. It ends with the good datum: the tensor of all evaluated data is an admissible combination of glued vacua with denominator $R^{2m}$. The notation of Section 4 is kept. In particular $s$ is the flip scale and $\eta$ the unit with $\bar\eta\eta = -1$.

### The middle pairs

For a middle pair the string of $V$ has odd length $m \neq 1$, and the plane is spanned by the middle vectors $z$ of $V$ and $z''$ of $V''$. The lift has the component $s x$ on $X$, $x$ on $X''$, and $s u c$ at both $z$ and $z''$. The scaling is $\kappa = 1$.

**Theorem (Neighbours lift in a middle pair).** Suppose that the frames of $V$ and $V''$ span the glued lattices for $(a, \pi, u)$ and $(a, \pi, u'')$, and that $s u = \bar\eta\,\delta\,u''$. Then the middle double lift lifts the neighbours for $(\pi, u, 1, \delta)$.

Lean: `New.Seesaw.liftsNeighbours_middleDoubleLift`.

*Proof.* Let $(c, x)$ be a neighbour vector. By the lemma on $V^- \oplus V''$ it suffices to treat the two blocks.

In $V$, after division by $s$, the component on $X$ is $x$ and the coordinate at $z$ is $uc = u(\pi^{-1}x_e + (c - \pi^{-1}x_e))$. The adele $c - \pi^{-1}x_e$ is integral by condition 4 of a neighbour vector, $\bar\pi x_e$ is integral by condition 3, and $x_i$ is integral for $i \neq e$ by condition 2. The lemma on vectors of the glued lattice applies.

In $V''$ the component on $X''$ is $x$. Since $\delta c = c$, the coordinate at $z''$ is $suc = \bar\eta\delta u''c = u''\bar\eta c = u''(\pi^{-1}x_{e''} + (\bar\eta c - \pi^{-1}x_{e''}))$. The last term is integral by condition 5. The string of $V''$ has odd length $m - 2$, and the lemma applies again. $\square$

**Lemma (Denominators in a middle pair).** The middle double lift matches the denominators for $(1, \beta)$.

Lean: `New.Seesaw.matchesDenominators_middleDoubleLift`.

*Proof.* The inclusion keeps each index of $X$ in $V$ and each index of $X''$ in $V''$. So a nonzero entry joins two indices with the same weight, $\beta$ or $\bar\beta$. $\square$

### The last pair

For the last pair $m = 1$, $V''$ is standard with no string, and $N = p\bar p$ with $p \in E$. The vector $e''$ is $z/p$ in $V^-$, where $z$ is the string vector of $V$. There is no plane.

**Definition (The last scaling).** $\kappa^{\mathrm{last}}_b = \delta$ for $b = e''$ and $1$ otherwise.

Lean: `New.Seesaw.lastScaling`.

**Theorem (Neighbours lift in the last pair).** Suppose that $\pi^{-1} = p^{-1}$ as finite adeles, the frame of $V$ spans the glued lattice for $(a, \pi, u)$, and $su = \bar\eta\delta$. Then the last double lift lifts the neighbours for $(\pi, u, \kappa^{\mathrm{last}}, \delta)$.

Lean: `New.Seesaw.liftsNeighbours_lastDoubleLift`.

*Proof.* Let $(c, x)$ be a neighbour vector. The lift has component $sx$ on $X$, component $x$ on $X'' \setminus \{e''\}$, and coordinate $\pi^{-1}\delta x_{e''}$ at $z$, from $\kappa_{e''}x_{e''}$ times $z/p$.

In $V$, after division by $s$, the coordinate at $z$ is $s^{-1}\pi^{-1}\delta x_{e''}$. Multiply $su = \bar\eta\delta$ by $\eta$. Since $\eta\bar\eta = -1$, this gives $s^{-1}\delta = -\eta u$. So the coordinate is $-u\eta\pi^{-1}x_{e''} = u(\pi^{-1}x_e + c')$ with

$$c' = -\pi^{-1}x_e - \eta\pi^{-1}x_{e''} = (c - \pi^{-1}x_e) + \eta(\bar\eta c - \pi^{-1}x_{e''}).$$

The second equality uses $\eta\bar\eta c = -c$. Both terms are integral by conditions 4 and 5, and $\eta$ is integral. The lemma on vectors of the glued lattice applies.

In $V''$ the point is $1$ and the string is empty. The coordinates are $x_b$ for $b \in X'' \setminus \{e''\}$, which are integral by condition 2. $\square$

**Lemma (Denominators in the last pair).** Suppose that $v(\bar\beta\delta) = v(\beta)$ at every finite place. Then the last double lift matches the denominators for $(\kappa^{\mathrm{last}}, \beta)$.

Lean: `New.Seesaw.matchesDenominators_lastDoubleLift`.

*Proof.* Only $e''$ changes its block: it has weight $\bar\beta$ as an index of $X''$ and lands in $V^-$, where the weight is $\beta$. With the scaling the weight of $e''$ is $\bar\beta\delta$, whose valuation is that of $\beta$. All other indices stay in their blocks with $\kappa = 1$. $\square$


### The scalings of the tower

Now let $D$ be the data of [the data and its sizes](/chapter/data-and-sizes/). Recall from [standard lattices](/chapter/seesaw-identity-1/) the ideles $\varpi_M$ (`D.chosenIdele`), which has the valuations of $\beta = $ `D.piM` and is $1$ away from the chosen places, $a = \alpha/\bar\varpi_M$ and $\pi = \pi_N$. The scale of $Y_k$ is $u_k = (a/\bar a)^{\lceil (m - k)/2\rceil}$ with $m = 2\varrho + 2$. By [the tower has standard lattices](/decl/New.Data.spansLattice_gradingY/), the frame of $Y_k$ spans the glued lattice for $(a, \pi_N, u_k)$ when $k \le 2\varrho + 1$.

**Definition (The chosen ratio).** $\delta = \varpi_M/\bar\varpi_M$.

Lean: `New.Data.chosenRatio` (New/UpperBound/Seesaw/GoodDatum.lean).

**Lemma (Properties of $\delta$ and $\beta$).**

1. $\delta\bar\delta = 1$.
2. $\delta = 1$ and $\beta$ is a unit at every place above $N$.
3. $v(\bar\beta\delta) = v(\beta)$ at every finite place.
4. $s \cdot (a/\bar a) = \bar\eta\,\delta$.

Lean: `New.Data.chosenRatio_mul_star`, `New.Data.chosenRatio_apply_of_N_mem`, `New.Data.v_piM_eq_one_of_N_mem`, `New.Data.v_star_piM_mul_chosenRatio`, `New.Data.flipScale_mul_divStar_ideleA`.

*Proof.* (1) $\delta\bar\delta = (\varpi_M/\bar\varpi_M)(\bar\varpi_M/\varpi_M) = 1$. (2) No place above $N$ is chosen, so $\varpi_M$ and $\bar\varpi_M$ are $1$ there, and $v(\beta) = v(\varpi_M) = 1$. (3) $v(\bar\beta/\bar\varpi_M) = 1$ at every place, since $\beta$ and $\varpi_M$ have the same valuations. So $v(\bar\beta\delta) = v(\varpi_M) = v(\beta)$. (4) By Section 4, $s = \bar\eta\bar\alpha\alpha^{-1}$. Also $a/\bar a = (\alpha/\bar\varpi_M)(\varpi_M/\bar\alpha)$. The factors $\alpha$ and $\bar\alpha$ cancel, and $s\,(a/\bar a) = \bar\eta\varpi_M/\bar\varpi_M$. $\square$

**Proposition (Scalings for the tower).** Let $\kappa$ be factors on the rows, each $1$ or $\delta$, and equal to $1$ on the first block. Then $\kappa$ is a scaling at $M$ for $(N, \beta, \delta)$. In particular $\kappa = 1$ and $\kappa = \kappa^{\mathrm{last}}$ are scalings.

Lean: `New.Data.isScalingAtM_of_eq_one_or_eq`, `New.Data.isScalingAtM_one`, `New.Data.isScalingAtM_lastScaling`.

*Proof.* Conditions 1 to 4 of a scaling are the lemma and the hypothesis. For condition 5, $\bar\beta\cdot 1$ is integral, and $\bar\beta\delta$ is integral by (3), since $\beta$ is. For condition 6, on the first block $\beta\kappa_b = \beta$, and on the second block $\bar\beta\kappa_b$ is condition 5. The last scaling is $\delta$ only at $e''$, which lies in the second block. $\square$

**Lemma (The scale gains one factor).** For $i \le \varrho$, $u_{2i} = (a/\bar a)\,u_{2i+2}$.

Lean: `New.Data.latticeScale_two_mul`.

*Proof.* With $m = 2\varrho + 2$, the exponent is $\lfloor (m - 2i + 1)/2\rfloor = \lfloor (m - 2i - 1)/2\rfloor + 1$. $\square$

So $s\,u_{2i} = \bar\eta\,\delta\,u_{2i+2}$ for $i \le \varrho$.

**Theorem (The pairs of the tower are admissible).** For $i \le \varrho$ the evaluation $\mathrm{ev}_i$ of pair $i$ is an admissible evaluation for $(N, P_N, \beta)$ with weights $\mathrm{selfOrConj}(\beta)$, where $P_N$ is the set of places dividing $\pi_N$.

Lean: `New.Data.isAdmissibleEval_doubleLiftEvalY`.

*Proof.* $P_N$ is split for $N$ and $\pi_N$ is split squarefree (part 1). The frame of $Y_{2i+1}$ spans the glued lattice. For $i < \varrho$ the pair is a middle pair with $\kappa = 1$. Take $u = u_{2i}$ and $u'' = u_{2i+2}$. Both frames span their glued lattices, since $2i + 2 \le 2\varrho$, and $su = \bar\eta\delta u''$. The theorem on middle pairs and the lemma on their denominators apply. For $i = \varrho$ the pair is the last pair with $\kappa = \kappa^{\mathrm{last}}$ and $p = \pi_N \in E$. The space $Y_m$ is standard, and $u_m = 1$, so $su_{2\varrho} = \bar\eta\delta$. The frame of $Y_{2\varrho}$ spans its glued lattice, $\pi^{-1} = p^{-1}$ by definition of $\pi_N$, and $v(\bar\beta\delta) = v(\beta)$. The theorem on the last pair and its lemma apply. In both cases the main theorem of Section 4 gives the claim. $\square$

### Point data as combinations

The evaluation is applied to products of moved point data. Four general facts are needed. Write $\mathrm{Tr}(q, d)$ for the translations of [part 1](/chapter/seesaw-identity-1/).

**Lemma (Integral points preserve translations).** Let $g$ be a finite unitary point that is integral at every place prime to $q$, and $d$ an integral adele.

1. If $x \in \mathrm{Tr}(q, d)$, then $gx \in \mathrm{Tr}(q, d)$.
2. Every integral vector lies in $\mathrm{Tr}(q, d)$.
3. If $x \in \mathrm{Tr}(q, d)$ and $p$ implies $q = 1$, then $\omega(1, g)\rho(x)\phi_0$ is an admissible combination of the $\rho(y)\phi_0$, $y \in \mathrm{Tr}(q, d)$, with denominator $1$ away from $q$ and size $1$ under $p$.

Lean: `New.Seesaw.mulVec_mem_translations`, `New.Seesaw.mem_translations_of_mem_stdLattice`, `New.Seesaw.isAdmissibleCombination_weil_of_mem_localLevel`.

*Proof.* (1) $(gx)_i = \sum_j g_{ij}x_j$, and at $w \nmid q$ each $d\,g_{ij}x_j$ is integral. (2) $d$ and $x$ are integral. (3) Apply the [theorem on moved vacua](/decl/New.Seesaw.isAdmissibleCombination_weil_vacElem/) with $c = \Delta(g)$, $C = 1$ and $A = \mathrm{Tr}(q, d)$, which contains $g(x + \lambda)$ by (1) and (2). The coefficient $c/|\Delta(g)|^2$ equals $\Delta(g^{-1})^{-1}$, and $\Delta(g^{-1})$ is a unit at the primes prime to $q$, since $g^{-1}$ is integral there. If $p$ holds, then $q = 1$, so $g$ is integral everywhere and $\Delta(g) = 1$. $\square$

**Lemma (Products of two translates).** Let $t_1$ and $t_2$ be matrices on $\mathrm{Hom}(V, V')$ and $\mathrm{Hom}(V', V'')$ with $\bar\beta t_1$ and $\bar\beta t_2$ integral away from $q$. Then the joined datum of $\rho(t_1)\phi_0$ and $\rho(t_2)\phi_0$ is $\zeta\rho(z)\phi_0$ on $\mathrm{Hom}(V', V^- \oplus V'')$, with $\zeta$ a root of unity and $z$ in the weighted translations of $q$ with weights $\mathrm{selfOrConj}(\beta)$.

Lean: `New.Seesaw.exists_arrowProduct_eq_smul_finHeisenbergOp`.

*Proof.* Take $z$ with block $-\eta\,t_1^*$ on $V^-$ and block $t_2$ on $V''$. The joined datum of the two translates is the semicharacter value squared times $\rho(z)\phi_0$ (Lean: `New.Seesaw.finHeisenbergOp_arrowProduct`), and that value is a root of unity. On the first block $\beta(-\eta\bar t_1) = -\eta\,\overline{\bar\beta t_1}$ is integral away from $q$, since $\eta$ is integral. $\square$

Let $\vartheta$ be a twist with places $\vartheta.Q$, and $q = \prod_{w \in \vartheta.Q} Nw$. The point datum of lift $k$ is the indicator of the inclusion matrix modulo the twist modulus, with the vacuum at the other places ([unfolding in stages](/chapter/seesaw-identity-1/)).

**Proposition (Moved point data).** Let each $y_k$ be integral at the places prime to $q$.

1. The twist modulus divides $\beta q$.
2. The point datum of lift $k$ is an admissible combination of the $\rho(x)\phi_0$, $x \in \mathrm{Tr}(q, \bar\beta)$, with denominator $N(\beta)^{|Y_{k+1}\times Y_k|}$ away from $q$ and size $1$ under any $p$.
3. The same holds for the point datum moved by $(y_k, y_{k+1})$, with size $1$ under $\vartheta.Q = \emptyset$.
4. The joined datum of the moved point data of lifts $k$ and $k+1$ is an admissible combination of the $\rho(z)\phi_0$, $z$ in the weighted translations of $q$ with weights $\mathrm{selfOrConj}(\beta)$, with denominator $N(\beta)^{|Y_{k+1}\times Y_k|}N(\beta)^{|Y_{k+2}\times Y_{k+1}|}$ and size $1$ under $\vartheta.Q = \emptyset$.

Lean: `New.Data.piM_mul_normQ_mem_ideal`, `New.Data.isAdmissibleCombination_pointDatumY`, `New.Data.isAdmissibleCombination_translatedPointDatumY`, `New.Data.isAdmissibleCombination_arrowProduct_translatedPointDatumY`.

*Proof.* (1) The modulus is the product of the chosen places and the places of $\vartheta.Q$. The chosen places generate the ideal $(\beta)$, and $q$ lies in each place of $\vartheta.Q$. (2) The datum is $\Psi\otimes$ applied to the vacuum, where $\Psi$ is the indicator of one class, with values in $\{0, 1\}$ and $\sum|\sigma\Psi| = 1$. The projection fixes the vacuum. Apply the [theorem on values of $\Psi\otimes$](/decl/New.Seesaw.isAdmissibleCombination_schrodingerOp/) with $g = \beta$, using (1). (3) The moved datum is $c\,\omega(1, g)$ of the datum, where $g$ is the finite point of the pair and $c$ is a quotient of character values at the determinants. The point $g$ is integral at the places prime to $q$. The characters have a weight, so $c$ is integral away from $q$ and $|\sigma(c)| \le 1$. Substitute (3) of the lemma into (2) by the substitution rule of part 1, and multiply by $c$. (4) Combine (3) for $k$ and $k + 1$ by the bilinear rule, with the joined product as bilinear map. The lemma on products replaces each product of translates by a root of unity times a translate. $\square$

### The good datum

Let $R = N(\beta)^{n_m^2}$ (`D.residueMatrixCount`), where $n_m$ is the rank of $X_m$. In terms of the principal level, $R = M^{fn_m^2}$.

**Lemma (The denominator of a pair).** For $i \le \varrho$, the product of $N(\beta)^{|Y_{2i+1}\times Y_{2i}|}$, $N(\beta)^{|Y_{2i+2}\times Y_{2i+1}|}$ and the number of matrices modulo $\beta$ of shape $(X_{2i}\sqcup X_{2i+2})\times X_{2i+1}$ divides $R^4$.

Lean: `New.Data.absNorm_pow_mul_card_dvd_residueMatrixCount_pow`.

*Proof.* The number of matrices modulo $\beta$ with $r$ entries is $N(\beta)^r$. So the product is $N(\beta)^e$ with $e$ the sum of the three sizes. All ranks are at most $r = n_m$, so $e \le r^2 + r^2 + 2r\cdot r = 4r^2$. $\square$

**Theorem (Evaluated data).** For $i \le \varrho$ there is a constant $C_i$ with the following property. For every twist $\vartheta$ and every family $y$ of points integral at the places prime to $q$, the evaluated datum $\mathrm{ev}_i(\vartheta, y)$ is an admissible combination of the vectors $C_i\,G(t_1, t_2)$, over $t_1, t_2 \in \mathrm{Tr}(q, \bar\beta)$, with denominator $R^4$ away from $q$ and size $1$ under $\vartheta.Q = \emptyset$.

Lean: `New.Data.exists_isAdmissibleCombination_evaluatedDatum`.

*Proof.* Let $C_i$ be the constant of the admissible evaluation $\mathrm{ev}_i$. The number $q$ is prime to $N$, since the twist is coprime to the level. By (4) of the proposition the joined datum is a combination of translates $\rho(z)\phi_0$. Apply $\mathrm{ev}_i$, and substitute for each $\mathrm{ev}_i(\rho(z)\phi_0)$ the combination given by admissibility, with $n = q$ and $p = (\vartheta.Q = \emptyset)$. The denominators multiply, and their product divides $R^4$ by the lemma. The sizes multiply to $1$. $\square$

The glued vacuum of a tuple $t$ of translations is the pure tensor over $i \le \varrho$ of the glued data $\mathrm{Glue}(\phi^\flat_{t,2i}\otimes\phi^\flat_{t,2i+1})$, where $\phi^\flat_{t,j}$ is the integral vacuum of $\mathrm{Hom}(X_j, X_{j+1})$ translated by $t_j$ ([columns and the composite lift](/chapter/upper-bound-objects/)).

**Theorem (The good datum).** There is a constant $C$ with the following property. For every twist $\vartheta$ and every family $y$ of points integral at the places prime to $q$, the pure tensor $\bigotimes_{i \le \varrho}\mathrm{ev}_i(\vartheta, y)$ is an admissible combination of the vectors $C\cdot\mathrm{gluedVacuum}(t)$, over the tuples $t$ with every $t_j \in \mathrm{Tr}(q, \bar\beta)$, with denominator $R^{2m}$ away from $q$ and size $1$ under $\vartheta.Q = \emptyset$.

Lean: `New.Data.exists_isAdmissibleCombination_gluedVacuum`.

*Proof.* The integral vacuum is $\kappa_j$ times the vacuum, with $\kappa_j = s_0^{|X_{j+1}\times X_j|}$ for the vacuum scale $s_0 \neq 0$ of [the integral vacuum](/chapter/integral-vacuum/). The gluing is linear. So $C_i\,G(t_{2i}, t_{2i+1}) = c_i\,\mathrm{Glue}(\phi^\flat_{t,2i}\otimes\phi^\flat_{t,2i+1})$ with $c_i = C_i/(\kappa_{2i}\kappa_{2i+1})$. A pure tensor of multiples is the product of the multiples times the pure tensor. Take $C = \prod_{i \le \varrho}c_i$. The theorem on pure tensors of part 1, applied to the $\varrho + 1$ combinations of the theorem on evaluated data, gives denominator $(R^4)^{\varrho+1} = R^{2m}$, since $m = 2\varrho + 2$, and size $1^{\varrho+1} = 1$. $\square$

**Remark (Formalization).** The constants $C_i$ are chosen by `choose!` from existence statements. The statement of the good datum does not say $C \neq 0$. The proofs give $C_i = cK$ with $c \neq 0$ and $K \ge 1$ (Section 4), so the chosen constants could be shown nonzero, but no statement records this. Section 6 therefore treats the case $c_0C = 0$ separately. The vacuum scale $s_0$ is also a `choose` object, and only $s_0 \neq 0$ is used.

### Example: the size of $R$

Let $E$ be imaginary quadratic, so $f = 1$, and let $M = p_0p_1 = 5 \cdot 13 = 65$. Then $N(\beta) = 65$. If $\varrho = 0$, then $m = 2$, and there is one pair, the last pair, with $X_0 \to X_1 \to X_2$. With $n_2 = 3$ the bound of a pair is $R^4 = 65^{36}$, and the good datum has denominator $R^{2m} = R^4$. With $\varrho = 1$ there are two pairs, $m = 4$, and the denominator is $R^8 = (65^{n_4^2})^8$. These denominators are cleared in Section 6 by the factor $u$ of [part 1](/decl/New.Seesaw.IsAdmissibleCombination.normUnit_smul/).
