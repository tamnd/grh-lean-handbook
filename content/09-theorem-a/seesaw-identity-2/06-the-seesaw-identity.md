---
title: The assembly and the seesaw identity
lean:
  - New/UpperBound/Seesaw/SeesawIdentity.lean
decls:
  - New.Data.restrictToFormY
  - New.Data.lowerChain_eq_of_lowerChainUpTo_eq
  - New.Data.exists_integral_eq_mul_inner_restrictToFormY
  - New.Data.transposedLiftY
  - New.Data.transposedLiftY_apply
  - New.Data.integral_mul_liftY
  - New.Data.twistedPairWeil_datumY_of_mem_levelY
  - New.Data.hasLevel_transposedLiftY
  - New.Data.isRapid_conjFormY
  - New.Data.integral_unfoldStageOn_mul_transposedLiftY
  - New.Data.sum_quotient_chosenLevel_eq_sum_cutPoints
  - New.Data.integral_mul_liftY_poincareAt
  - New.Data.exists_integral_mul_lowerChainUpTo_eq_cutSum
  - New.Data.evaluatedTensor
  - New.Data.seesawDatum
  - New.Data.isInvariant_seesawDatum
  - New.Data.exists_lowerChainUpTo_poincareAt_eq
  - New.Data.exists_isAdmissibleCombination_seesawDatum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The assembly and the seesaw identity

This section gives the tools of the top stage and of the descent, and proves the two unfolding theorems that [part 1](/chapter/seesaw-identity-1/) left to this chapter. Then it builds the tensor $\varphi_\xi$, expands it with the good datum of Section 5, and proves the seesaw identity.

Throughout, $m = 2\varrho + 2$, $G_j = U(Y_j)$, $J_j(\vartheta)$ is the level `levelY ϑ j` of the lift $\iota_j$, $J^\circ$ is the lattice stabiliser and $J_M \subseteq J^\circ$ the chosen level. The sets $\Omega_j$, the multiplicities $m_j$ and the cut sum $\Sigma_k$ are those of [part 1](/chapter/seesaw-identity-1/), Section 7.

### The top stage

The lower chain ends in automorphic forms on $Y_m$, the composite lift in algebraic forms.

**Definition (Restriction to forms on $Y_m$).** For a number $M$ with $m = M$, the map $\mathrm{res}_M$ from forms on $X_M$ to automorphic forms on $Y_M$ is the restriction `D.restrictToY` to algebraic forms, followed by the inverse of the isomorphism from automorphic forms to algebraic forms of [automorphic forms as algebraic forms](/chapter/automorphic-forms/).

Lean: `New.Data.restrictToFormY` (New/UpperBound/Seesaw/SeesawIdentity.lean).

**Lemma (Back to algebraic forms).** If $\iota_{M-1}\circ\cdots\circ\iota_0(f) = \mathrm{res}_M\,\psi$, then $\iota_\vartheta(f) = \mathrm{res}\,\psi$, where $\iota_\vartheta$ is the lower chain with values in algebraic forms and $\mathrm{res}$ is `New.Data.restrictToYOfEq`.

Lean: `New.Data.lowerChain_eq_of_lowerChainUpTo_eq`.

*Proof.* The lower chain $\iota_\vartheta$ is the image of the chain in automorphic forms under the isomorphism to algebraic forms. Apply this isomorphism to both sides of the hypothesis. $\square$

The top grading `New.Data.lastGrading` of $Y_m$ has the empty string. It identifies $Y_m$ with the standard definite space on the $n_m - 1$ indices of $X_m$ other than the last. Let $\mathrm{incl}$ be the resulting map of unitary groups, and write $\mathrm{diag}(k, 1)$ for the block embedding of $U(Y_m) \times U(1)$ into $U(X_m)$.

**Theorem (The pairing at the top).** Let $t$ be a linear form on the values of forms on $X_m$. There is $C_t \in \mathbb{C}$ with the following property. Let $x$ be a form on $Y_m$, $\psi$ a form on $X_m$ and $F$ a function on $G_m$. Suppose that $F(\mathrm{incl}\,k) = t\bigl(\psi(\mathrm{diag}(k, 1))\bigr)$ for every $k$. Then

$$\int_{[G_m]} F\,\bar x = C_t\,\langle x, \mathrm{res}_m\psi\rangle.$$

Lean: `New.Data.exists_integral_eq_mul_inner_restrictToFormY`.

*Proof.* The space $Y_m$ is standard and the top grading has no isotropic part. So its Bessel group is $G_m$, every point is some $\mathrm{incl}\,k$, and the hypothesis gives $F$ everywhere. The integral of an automorphic function made from the highest vector against the coefficient $h \mapsto t(\psi(\mathrm{diag}(h,1)))$ is a constant $C$ times a class mean $\mathrm{avg}$ (Lean: `New.Seesaw.integral_algFormCoeff_blockEmb`, Lib/Adelic/AutomorphicForms/BlockPeriods.lean). The level is $J^\circ$, of index $1$, so the left side is $C\cdot\mathrm{avg}$. On the right side, the Petersson product with an algebraic form is a class integral ([automorphic forms as algebraic forms](/chapter/automorphic-forms/)). The restriction `D.restrictToY` is the branching map divided by $c = \prod_\tau \Phi_\tau(\bar\varpi_N)^{e_\tau}$. This gives $\langle x, \mathrm{res}_m\psi\rangle = (\dim W)^{-1} c^{-1}\,\mathrm{avg}$, where $W$ is the weight space of $Y_m$. The numbers $c$ and $\dim W$ are nonzero. So $C_t = C\,(\dim W)\,c$ works. $\square$

**Remark (Formalization).** The constant $C_t$ comes from an existence statement and may be $0$.

### The descent

**Definition (Descent).** Let $\bar Y_j$ denote forms of the conjugate type on $Y_j$ (Lean: `New.Data.ConjFormY`). The descent $\iota_j^t : \bar Y_{j+1} \to \bar Y_j$ is $[J^\circ : J_j(\vartheta)]$ times the theta lift along the swapped kernel, with the same datum $\phi_j$ as $\iota_j$.

Lean: `New.Data.transposedLiftY`.

**Lemma (Descent as a theta integral).** For $j < m$, $z \in \bar Y_{j+1}$ and $g \in G_j$,

$$\iota_j^t z(g) = [J^\circ : J_j(\vartheta)]\int_{[G_{j+1}]} \theta\bigl(\omega(g, h)\phi_j\bigr)\, z(h)\, dh.$$

Lean: `New.Data.transposedLiftY_apply`.

*Proof.* The datum is an arrow for the swapped kernel, and such a lift is this theta integral ([theta kernels and gauges](/chapter/theta-kernels-gauges/)). $\square$

**Lemma (Lift and descent are transposes).** For $j < m$, $z \in \bar Y_{j+1}$ and a form $f$ on $Y_j$,

$$\int_{[G_{j+1}]} z\cdot\iota_j f = \int_{[G_j]} \iota_j^t z\cdot f.$$

Lean: `New.Data.integral_mul_liftY`.

*Proof.* Both $\iota_j$ and $\iota_j^t$ are $[J^\circ : J_j(\vartheta)]$ times a theta lift with the datum $\phi_j$. The datum is an arrow in both directions. For such a datum the two theta lifts are transposes, by Fubini on $[G_j]\times[G_{j+1}]$ ([theta kernels and gauges](/chapter/theta-kernels-gauges/)). Pull the index out of both integrals. $\square$

**Lemma (The descent has level $J_j(\vartheta)$).** Let $u \in J_j(\vartheta)$. Then $\omega((1, u), 1)\phi_j = \phi_j$. So for $j < m$ every descent $\iota_j^t z$ is right invariant under $J_j(\vartheta)$.

Lean: `New.Data.twistedPairWeil_datumY_of_mem_levelY`, `New.Data.hasLevel_transposedLiftY`.

*Proof.* The element $(1, u)$ acts only on the finite point datum. Since $u$ reduces to $1$ at the level places, the tame characters give $1$, and the point datum is fixed ([the objects of the upper bound](/chapter/upper-bound-objects/)). For the second claim, write $\omega(gu, h)\phi_j = \omega(g, h)\,\omega((1,u), 1)\phi_j = \omega(g,h)\phi_j$ inside the theta integral of the previous lemma. $\square$

**Lemma.** For $j < m$, every $z \in \bar Y_{j+1}$ is rapidly decreasing.

Lean: `New.Data.isRapid_conjFormY`.

*Proof.* This holds for the arrow of the trivial twist, and it does not depend on the twist. $\square$

Recall the period $\Xi_{k+1}(\xi, y) = \int_{R'(E)\backslash G_{k+1}} \mathcal{W}_{k+1}\, z$ of part 1, Section 1 (Lean: `New.Data.unfoldedPeriod`). If the string of $\mathsf Y'$ has length $s_{k+1} = 2\varrho - k$, the integrand is integrable, by part 1, Section 5, and the lemma above (Lean: `New.Data.integrable_unfoldStage_mul`).

**Lemma (The recursion with the descent).** Let $k \leq 2\varrho + 1$, $\mathsf{Y}'$ a grading of $Y_{k+1}$ with a string of length $s_{k+1}$, and $z \in \bar Y_{k+1}$. Let $W_k$ be the function on the Bessel group $R_k$ of the standard grading of $Y_k$ from part 1. Then

$$\int_{[R_k]} W_k(r)\;\iota_k^t z\bigl(r\,(\xi_k, y_k)\bigr)\, dr = [J^\circ : J_k(\vartheta)]\;\Xi_{k+1}(\xi, y).$$

Lean: `New.Data.integral_unfoldStageOn_mul_transposedLiftY`.

*Proof.* The stage identity of part 1 evaluates $\Xi_{k+1}$ as the period of $W_k$ against the theta integral of $z$. Insert the formula for $\iota_k^t z$ as a theta integral and pull out the index. $\square$

### The first lift of the Poincaré series

**Lemma (Sums over $J_M/J_0(\vartheta)$).** Let $f$ be a function on $G_0^{\mathrm{fin}}$ that is right invariant under $J_0(\vartheta)$. Then the sum of $f$ over representatives of $J_M/J_0(\vartheta)$ equals $\sum_{c\in\Omega_0} f(c^{\mathrm{out}})$.

Lean: `New.Data.sum_quotient_chosenLevel_eq_sum_cutPoints`.

*Proof.* $\Omega_0$ is the set of classes modulo $J_0(\vartheta)$ of the elements of $J_M$. Send a class of $J_M$ to the class of its representative. This is a bijection onto $\Omega_0$, since $J_0(\vartheta) \subseteq J_M$. Two representatives of one class differ by an element of $J_0(\vartheta)$, so $f$ takes the same value on them. $\square$

**Theorem (The first lift of the Poincaré series).** Let $\mathsf{Y}'$ be a grading of $Y_1$ with a string of length $2\varrho$, and $z \in \bar Y_1$. Then

$$\int_{[G_1]} z\cdot\iota_0(\mathcal P\varphi) = [J^\circ : J_M]\sum_{c\in\Omega_0}\Xi_1\bigl((g, 1, 1, \ldots), (c^{\mathrm{out}}, 1, 1, \ldots)\bigr).$$

Lean: `New.Data.integral_mul_liftY_poincareAt`.

*Proof.* Write $J = J_0(\vartheta)$. The levels satisfy $J \subseteq J_M \subseteq J^\circ$, so $[J_M : J]\,[J^\circ : J_M] = [J^\circ : J]$. The index $[J^\circ : J]$ is not $0$, since $J^\circ$ is compact and $J$ is open. So $[J_M : J] \neq 0$, and $J_M/J$ is finite. For $x \in G_0^{\mathrm{fin}}$ put

$$P(x) = \int_{[R_0]} \mathcal{W}_\varphi(r)\;\iota_0^t z\bigl(r\,(g, x)\bigr)\, dr.$$

Since $(g, xu) = (g, x)(1, u)$ and $\iota_0^t z$ has level $J$, $P(xu) = P(x)$ for $u \in J$. By the recursion with the descent at $k = 0$, $P(x) = [J^\circ : J]\;\Xi_1((g,1,\ldots), (x,1,\ldots))$. Multiply the left side of the claim by $[J_M : J]$. Then

$$[J_M : J]\int z\cdot\iota_0(\mathcal P\varphi) = [J_M : J]\int_{[G_0]}\iota_0^t z\cdot\mathcal P\varphi = \sum_{q\in J_M/J} P(q^{\mathrm{out}}) = \sum_{c\in\Omega_0} P(c^{\mathrm{out}}).$$

The steps are the transpose lemma, the defining property of $\mathcal P$ for the form $\iota_0^t z$ of level $J$ (Lean: `New.Data.integral_mul_poincareAt`, [the objects of the upper bound](/chapter/upper-bound-objects/)). and the previous lemma. Insert the value of $P$ and write $[J^\circ : J] = [J_M : J][J^\circ : J_M]$. Cancel $[J_M : J] \neq 0$. $\square$

### The pairing as a cut sum

**Theorem (The pairing as a cut sum).** Fix $t$, $g$, $k \leq 2\varrho + 1$, a grading $\mathsf{Y}'$ of $Y_{k+1}$ with a string of length $s_{k+1}$, and a function $a$ of the archimedean tuples $\xi$. There is $c \in \mathbb C$ with the following property. Let $\varphi$ be a ramified source form, $z \in \bar Y_{k+1}$ and $S$ a function on tuples of classes $(y_iJ_i(\vartheta))_i$. Suppose that $\Xi_{k+1}(\xi, y) = a(\xi)\,S\bigl((y_iJ_i(\vartheta))_i\bigr)$ whenever $y_0 \in J_M$ and $y_m = 1$. Then

$$\int_{[G_{k+1}]} z\cdot(\iota_k\circ\cdots\circ\iota_0)(\mathcal P\varphi) = c\cdot\Sigma_{k+1}S.$$

Lean: `New.Data.exists_integral_mul_lowerChainUpTo_eq_cutSum`.

*Proof.* Induction on $k$, for all gradings $\mathsf{Y}'$ and all functions $a$.

*Base case $k = 0$.* Take $c = [J^\circ : J_M]\,a(g, 1, 1, \ldots)$. On $\Omega_0$ every multiplicity is $1$. For $c' \in \Omega_0$ the point $y = (c'^{\mathrm{out}}, 1, 1, \ldots)$ has $y_0 \in J_M$ and $y_m = 1$. So the hypothesis gives $\Xi_1 = a(g, 1, \ldots)\, S(c', 1, 1, \ldots)$, since the class of $c'^{\mathrm{out}}$ is $c'$. Insert this in the first lift theorem. The result is $c\,\Sigma_1 S$.

*Step from $k$ to $k+1$.* Let $\mathsf{Y}_0$ be the standard grading of $Y_{k+1}$. Its string has length $s_{k+1}$. For each $\xi$ apply the theorem on the integral over a cut (part 1, Section 7) to $\mathsf Y_0$, the level $J^\circ$ and the function $x \mapsto a(\xi$ with $\xi_{k+1} = x)$. This gives a constant $a'(\xi)$. The induction hypothesis for $\mathsf Y_0$ and $a'$ gives a constant $c$. Fix $\vartheta$, $\varphi$, $z \in \bar Y_{k+2}$ and $S$, and put $z' = \iota_{k+1}^t z \in \bar Y_{k+1}$. By the transpose lemma,

$$\int z\cdot(\iota_{k+1}\circ\cdots\circ\iota_0)(\mathcal P\varphi) = \int z'\cdot(\iota_k\circ\cdots\circ\iota_0)(\mathcal P\varphi).$$

Apply the induction hypothesis to $z'$ and the function $S'$ of the classes $(y_i J_i(\vartheta))_{i \leq k}$ given by

$$S'(y) = \sum_{c'\in\Omega_{k+1}} m_{k+1}(c')^{-1}\, S(y \text{ with } y_{k+1} = c').$$

The result is $c\,\Sigma_{k+1}S' = c\,\Sigma_{k+2}S$, by the definition of the cut sum. It remains to check the hypothesis: the period $\Xi'_{k+1}(\xi, y)$ of $z'$ for $\mathsf Y_0$ is $a'(\xi)\,S'(y)$ when $y_0 \in J_M$ and $y_m = 1$.

Fix such $\xi$, $y$. Let $f = W_{k+1}\cdot z'$ on $G_{k+1}$, with $W_{k+1}$ the function left by $k+1$ steps for $\mathsf{Y}_0$. Then $\Xi'_{k+1}(\xi, y) = \int_{R_0(E)\backslash G_{k+1}} f$. The theorem on the integral over a cut applies to $f$ with $T = \Omega_{k+1}$:

1. $f$ is continuous, and integrable by the lemma above.
2. $f$ is left invariant under the rational Bessel points, since $W_{k+1}$ is and $z'$ is automorphic.
3. $\Omega_{k+1}$ is a stage cut, so it is stable under the finite Bessel points that are integral (Lean: `New.Data.isStageCut_cutPoints`).
4. If $f(x) \neq 0$, then $W_{k+1}(x) \neq 0$. The support theorem of part 1, Section 6, gives lattice bounds on the orbit of $x$, since $\varphi$ is ramified and $y_0 \in J_M$. A stage cut has nonzero multiplicity at such points.
5. Let $\xi'$, $y'$ be $\xi$, $y$ with entry $k+1$ replaced by $x_\infty$, $x_{\mathrm f}$. Since $W_{k+1}(rx)$ is $W_k(r)$ with the outer variable $x$ (Lean: `New.Data.unfoldStage_update`), the recursion with the descent gives
$$\int_{[R_0]} f(rx)\,dr = [J^\circ : J_{k+1}(\vartheta)]\;\Xi_{k+2}(\xi', y') = [J^\circ : J_{k+1}(\vartheta)]\,a(\xi')\,S(y'),$$
by the hypothesis, since the entries $0$ and $m$ do not change.

With $b(q) = S(y$ with $y_{k+1} = q)$, the cut theorem gives $\int f = a'(\xi)\sum_{c'\in\Omega_{k+1}} m_{k+1}(c')^{-1}\,b(c') = a'(\xi)\,S'(y)$. $\square$

**Remark (Formalization).** The constant $c$ is built from existence statements and may be $0$. The function $a'$ is chosen by `choose`; only its defining property is used.

### The tensor $\varphi_\xi$

**Definition (The evaluated tensor and $\varphi_\xi$).** For a tuple $c$ of classes $c_i \in G_i^{\mathrm{fin}}/J_i(\vartheta)$, the evaluated tensor is the pure tensor of the evaluated data $\mathrm{ev}_i(\vartheta, (c_j^{\mathrm{out}})_j)$, $i \leq \varrho$, of part 1, Section 5. Put

$$\varphi_\xi = \Sigma_m(\text{evaluated tensor}).$$

Lean: `New.Data.evaluatedTensor`, `New.Data.seesawDatum`.

At the classes of a tuple $y$ the evaluated tensor is the pure tensor of $\mathrm{ev}_i(\vartheta, y)$, since the evaluated data do not depend on the representatives (Lean: `New.Data.evaluatedTensor_mk`, from `New.Data.evaluatedDatum_out`).

**Proposition (Invariance of $\varphi_\xi$).** The tensor $\varphi_\xi$ is jointly invariant: every tuple $b$ with $b_j$ in the level of $X_j$ and $b_m = 1$ fixes it under the Weil action.

Lean: `New.Data.isInvariant_seesawDatum`.

*Proof.* Let $b_Y(i) = \mathrm{incl}(b_i)$ for $i < m$ and $b_Y(m) = 1$, where $\mathrm{incl}$ is the map of finite points for the standard grading of $Y_i$. Since the Weil action is linear, it passes inside the cut sum. By property (1) of the cut sum (part 1, Section 7), translating the classes by $b_Y$ does not change $\Sigma_m$. So it is enough to show, for each tuple $c$: the action of $b$ on the evaluated tensor at $c$ equals the evaluated tensor at $b_Y c$. Both are pure tensors, so compare factor $i$. The evaluated datum at $b_Yc^{\mathrm{out}}$ is the evaluation of the translated point datum. For $i < \varrho$ the evaluation is that of a middle pair. It commutes with the actions of its three groups (Lean: `New.Seesaw.DoubleLiftData.finEval_arrowProduct_equivariant`, part 1, Section 4). For $i = \varrho$ it is that of the last pair. There the top factors of $b_Y$ and $b$ are both $1$, and the same equivariance applies with the trivial element. $\square$

### The unfolded identity

**Theorem (The lower chain of the Poincaré series).** Fix $g$ and $t$. There is $c_0 \in \mathbb{C}$ such that for every $\vartheta$ and every ramified source form $\varphi$,

$$(\iota_{m-1}\circ\cdots\circ\iota_0)(\mathcal P\varphi) = c_0\cdot\mathrm{res}_m\bigl(\Theta_\vartheta(\varphi; \varphi_\xi)\bigr),$$

where $\Theta_\vartheta(\varphi; w)$ is the chain of double lifts $X_0 \to\cdots\to X_m$ with the tensor of data $w$ (Lean: `New.Data.chainOfTensor`).

Lean: `New.Data.exists_lowerChainUpTo_poincareAt_eq`.

*Proof.* Let $C_\cdot$ be the constants of the pairing at the top. For each $\xi$, the evaluation after each pair (part 1, Section 5), applied to the last pair, gives a linear form $l_\xi$ with the following property. If $y_m = 1$, then the top function $W_m$ for the top grading at $\mathrm{incl}\,k$ is the coefficient $l_\xi$ of the chain of double lifts with data $\mathrm{ev}(\vartheta, y)$, at $\mathrm{diag}(k, 1)$. Apply the cut sum theorem with $k = 2\varrho + 1$, the top grading and $a(\xi) = C_{l_\xi}$. It gives $c_0$.

Fix $\vartheta$ and $\varphi$. It is enough to compare inner products with every form $x$ on $Y_m$. Fix $x$ and let $L(w) = \langle x, \mathrm{res}_m\Theta_\vartheta(\varphi; w)\rangle$, a linear form on tensors. Use $\bar x$ as the conjugate form. By the pairing at the top, with $F = W_m$ and $\psi$ the chain of double lifts with data $\mathrm{ev}(\vartheta, y)$,

$$\Xi_m(\xi, y) = C_{l_\xi}\, L(\text{evaluated tensor at } y)$$

when $y_m = 1$. So the cut sum theorem applies with $S(c) = L(\text{evaluated tensor at } c)$, and

$$\langle x, (\iota_{m-1}\circ\cdots\circ\iota_0)(\mathcal P\varphi)\rangle = c_0\,\Sigma_m(L\circ\text{evaluated tensor}) = c_0\,L(\varphi_\xi),$$

since $L$ is linear and passes inside the cut sum. This is the inner product of $x$ with the right side. $\square$

### The expansion of $\varphi_\xi$

Let $R = M^{fn_m^2}$ (Lean: `D.residueMatrixCount`) and $q = \prod_{w\in\vartheta.Q} N(w)$.

**Theorem (Expansion of $\varphi_\xi$).** There is one $C \in \mathbb C$ such that, for every $\vartheta$, the tensor $\varphi_\xi$ is an admissible combination of the vectors $C\cdot\mathrm{Glue}(x)$, $x \in \mathcal A_q$, with denominator $R^{2m}$ away from $q$ and size $R^{m}$ under $\vartheta.Q = \emptyset$. Here $\mathrm{Glue}(x)$ is the glued vacuum translated by $x$, and $\mathcal{A}_q$ is the set of admissible translations.

Lean: `New.Data.exists_isAdmissibleCombination_seesawDatum`.

*Proof.* Let $C$ be the constant of the good datum (Section 5). For $y$ integral away from $q$, the evaluated tensor at the classes of $y$ is an admissible combination of the $C\cdot\mathrm{Glue}(x)$ with denominator $R^{2m}$ and size $1$. By property (2) of the cut sum, $\varphi_\xi = \Sigma_m(\ldots)$ is an admissible combination of these values with denominator $1$ and size $R^m$. Substitution (part 1, Section 2) with $1\cdot R^{2m} \mid R^{2m}$ and $R^m\cdot 1 \leq R^m$ gives the claim. $\square$

### The proof of the seesaw identity

*Proof of the seesaw identity.* Let $c_0$ be the constant of the unfolded identity and $C$ that of the expansion. Put $d = R^{2m} \neq 0$ and

$$u = \mathrm{normUnit}(c_0C/d) \in \mathbb{C}^\times.$$

Take the constant $c = u^{-1}$. Fix a twist $\vartheta$.

*Clearing the denominator.* By the proposition on clearing the denominator (part 1, Section 2), $u\,c_0\,\varphi_\xi$ is an admissible combination of the $\mathrm{Glue}(x)$, $x \in \mathcal{A}_q$, with denominator $1$ and size $d\,R^m = R^{3m}$.

*Support.* For each $x \in \mathcal{A}_q$ there is $x' \in \mathcal{A}_q$ that vanishes at the places prime to $Mq$ and has the same glued vacuum ([the chain valuation](/chapter/chain-valuation/), Lean: `New.Data.exists_supported_translateDatum_eq`). So $\mathrm{Glue}(x) = 1\cdot\mathrm{Glue}(x')$, and $1$ is a root of unity. Rule (3) of the corollary in part 1, Section 2 gives a finitely supported $\Psi$ on the translations, with support in $\mathcal{A}_q$ intersected with the translations supported at $Mq$, values integral away from $q$, size $R^{3m}$ if $\vartheta.Q = \emptyset$, and

$$u\,c_0\,\varphi_\xi = \sum_x \Psi(x)\,\mathrm{Glue}(x).$$

The right side is the glued tensor of $\Psi$.

The size is $R^{3m} = M^{3fmn_m^2}$. The glued tensor $u c_0\varphi_\xi$ is jointly invariant, since $\varphi_\xi$ is and the Weil action is linear. So $\Psi$ is a chain datum.

*The identity.* Let $\varphi$ be a ramified source form. By the unfolded identity and linearity,

$$(\iota_{m-1}\circ\cdots\circ\iota_0)(u\,\mathcal{P}\varphi) = \mathrm{res}_m\bigl(\Theta_\vartheta(\varphi; u c_0\varphi_\xi)\bigr) = \mathrm{res}_m\bigl(\Theta_\vartheta(\varphi; \text{glued tensor of }\Psi)\bigr).$$

By the lemma on algebraic forms, $\iota_\vartheta(u\,\mathcal P\varphi) = B_{\vartheta,\Psi}(\varphi)$. Multiply by $u^{-1}$. $\square$

**Remark (Formalization).** The constant of the identity is $c = u^{-1}$. On a field, $\mathrm{normUnit}(x) = x^{-1}$ for $x \neq 0$ and $\mathrm{normUnit}(0) = 1$. So $c = c_0C/R^{2m}$ when $c_0C \neq 0$, and $c = 1$ when $c_0C = 0$. It is not $R^{2m}/(c_0C)$. The constants $c_0$ and $C$ come from existence statements, and neither is shown to be nonzero. If $c_0 C = 0$, then $u = 1$. Either $c_0 = 0$, or $C = 0$ and $\varphi_\xi$ is a combination of zero vectors. In both cases $u\,c_0\,\varphi_\xi = 0$, so the glued tensor of $\Psi$ is $0$. Then both sides of the identity are $0$. This is finding F-068 of [the register of findings](/chapter/register-of-findings/). The seesaw identity alone does not give a nonzero lift. Nonvanishing must come from another part of the argument, on the determinant side.

