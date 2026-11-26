---
title: The carrier
lean:
  - New/OneLift/ComparisonOperator/ThreeExchanges.lean
decls:
  - New.Rows.exists_mul_stdClassSum_modKernelStdSpace_eq_one
  - New.Rows.exists_stdClassSum_modKernelStdSpace_neg_eq_one
  - New.Rows.exists_mul_stdClassSum_eq_carrierForm
  - New.Rows.carrierForm_mem_rapidOfLevel_and_isAdelicHol
  - New.Rows.fockInner_realPairWeil_variableMinor_pow_eq_self
  - New.Rows.carrierForm_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The carrier

The first two exchanges turn a class sum of twisted kernels on the space $S$ of signature $(2m, m)$ into a number times the carrier $\varphi^\circ$. The carrier does not depend on the twist. We then show that $\varphi^\circ$ has full level, decays rapidly, is holomorphic and is not $0$.

Notation. $I_m$ is the standard definite space $E^m$ and $I_m^-$ is the same space with the form negated. $\theta^{V,W}_{a,b}[\Psi, P]$ is the theta kernel `New.modKernel` with characters $a$, $b$, a function $\Psi$ on matrices modulo $\mathfrak{m}$ and a polynomial $P$. The class sum $\mathrm{cs}$ on a definite space is `New.stdClassSum`: the sum, with weights $1/\#\mathrm{Aut}$, over the classes of the rational points and the integral level `stdLevel`. $y_\tau$ is the matrix of variables at the infinite place $\tau$, and $y^-_\tau$ is its block of the rows of sign $-1$.

Background in one line each. A character $\alpha$ is *tame for* $(\mathfrak{m}, \gamma, \chi)$ if it has weight $\gamma$ and its tame part is non-trivial exactly at the places of $\mathfrak{m}$ and induces $\chi$ ([exchange identity, part 2](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data)). The explicit exchange identity `New.Rows.exists_mul_stdClassSum_eq_integral_modKernel` equates $c$ times a class sum of kernels of $(W, I_a)$ with an integral of a kernel of $(V', W)$, with $|c|^2 = C/L_*(\alpha^{-1}\upsilon^{|b|+d}, d)$ ([explicit matching](/chapter/exchange-identity-2/#explicit-matching)). The one exchange theorem `New.Rows.mul_stdClassSum_eq_integral_mul_modKernel` chains two exchanges ([one exchange](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data)). The seesaw `New.modKernel_sum_left` says that a kernel on $W_1 \oplus W_2$ with a product datum is the product of the two kernels ([the pair and its kernel](/chapter/theta-lifts-seesaw/)). The carrier $\varphi^\circ$ = `New.Rows.carrierForm` and the coefficients $\mathsf{a}$ = `New.Rows.carrierCoeff` are defined in [the exchange data](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data).

### The first exchange

**Lemma (The first exchange).** Let $m > 0$ be even and let $k$ be a function from the infinite places to $\mathbb{N}$. There is a real $C$ with this property. For every modulus $\mathfrak{m}$, character $\alpha$ of $U(1)(\mathbb{A}_E)$ and character $\chi$ of $(O_E/\mathfrak{m})^\times$ such that $\alpha$ is tame for $(\mathfrak{m}, -k, \chi)$, there is $\gamma \in \mathbb{C}$ with

(a) $|\gamma|^2 = C/L_*\bigl(\mathfrak{m}, \alpha^{-1}\upsilon^{m/2}, m/2\bigr)$, and

(b) $\gamma\,\mathrm{cs}_h\Bigl(\theta^{I_m, I_m}_{\alpha,\alpha}\bigl[\chi\circ\det, \textstyle\prod_\tau \det(y_\tau)^{k(\tau)}\bigr](g, h)\Bigr) = 1$ for every $g$ in the adelic group of $I_m$.

Lean: `New.Rows.exists_mul_stdClassSum_modKernelStdSpace_eq_one` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Apply the explicit exchange identity with $W = I_m$, $V' = 0$ (the space on the empty index set), $V = I_m$, no added rows, and $d = m/2$. The ranks satisfy $m = 0 + 2d$ since $m$ is even, and the margin condition holds as $m \geq 2$. The rows at $\tau$ are $k(\tau)$ copies of the index set. This gives $C$ and, for each tame $\alpha$, a number $\gamma$ with (a). The set of places of the modulus is the one in the identity, so (a) holds as stated.

For (b), take the matched pair $\chi\circ\det$ and $1$ ([rank zero](/chapter/exchange-identity-2/#explicit-matching), `New.Rows.areMatched_det_one`). The left side of the identity is then the class sum in (b). Its polynomial is the stacked determinant with no added rows, and that is $\prod_\tau \det(y_\tau)^{k(\tau)}$. The right side is the integral over the group of $V' = 0$ of the kernel of $(0, I_m)$ with data $1$. That group is a point of volume $1$, and the kernel with the zero space is $\alpha(\det g)$ times the kernel with the standard characters, by the twist law `New.modKernel_twist`. Its value is $1$ after this factor, by `New.Rows.integral_modKernel_matchedPoly_of_isEmpty`. The factor $\alpha(\det g)$ appears on both sides and cancels. $\square$

Volume 12 uses this lemma for the twist measures of [the twisting theorem](/chapter/twisting-theorem/).

**Lemma (Conjugation).** Let $m > 0$. There is $n \in \mathbb{C}$ with $|n| = 1$ such that the following holds for every modulus $\mathfrak{m}$, character $c$ of $U(1)(\mathbb{A}_E)$, character $\chi$ of the residue ring and number $\gamma$. Let $\eta$ = `normNegOne` be the unit modulo $\mathfrak{m}$ that reduces a chosen element of norm $-1$. If
$$\gamma\,\mathrm{cs}_h\bigl(\theta^{I_m, I_m}_{c^{-1}, c^{-1}}[\chi^{-1}\circ\det, 1](g, h)\bigr) = 1$$
for every $g$ in the group of $I_m$, then
$$\bar\gamma\,\mathrm{cs}_h\Bigl(n\,\chi(\eta)^{-m}\,\theta^{I_m^-, I_m}_{c\upsilon^m, c\upsilon^m}[\chi\circ\det, 1](y, h)\Bigr) = 1$$
for every $y$ in the group of $I_m^-$.

Lean: `New.Rows.exists_stdClassSum_modKernelStdSpace_neg_eq_one` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

The lemma does not need $m$ to be even.

*Proof.* We use the conjugation law of theta kernels ([lean:Lib/Weil/DualPair/KernelLaws.lean#L390](lean:Lib/Weil/DualPair/KernelLaws.lean#L390), `New.exists_conj_modKernel_eq_mul_modKernel_neg`): there is $n$ with $|n| = 1$, depending only on the two spaces, such that $\overline{\theta^{S,T}_{a,b}[\Psi, P](g, h)} = n\,\theta^{S^-,T}_{a^{-1}\upsilon^{m}, b^{-1}\upsilon^{m}}[\Psi', \bar P](g, h)$, where $\Psi'(x) = \overline{\Psi(\eta^{-1}x)}$. Take $S = T = I_m$, $a = b = c^{-1}$, $\Psi = \chi^{-1}\circ\det$ and $P = 1$. Then $\bar P = 1$, and
$$\Psi'(x) = \overline{\chi^{-1}(\det(\eta^{-1}x))} = \chi(\eta^{-m}\det x) = \chi(\eta)^{-m}\chi(\det x),$$
as the values of $\chi$ have modulus $1$. Conjugate the hypothesis at $g = y$, moved to the group of $I_m$. The class sum commutes with conjugation, as its weights are rational. Each kernel becomes $n$ times the kernel of $(I_m^-, I_m)$ with datum $\chi(\eta)^{-m}\chi\circ\det$. The kernel is linear in the datum, so the scalar $\chi(\eta)^{-m}$ moves out. $\square$

### The carrier identity

**Theorem (The carrier as a class sum).** Let $m > 0$ be even. There is a real $C$ with this property. For every $\mathfrak{m}$, $\chi$ and every character $c$ of weight $0$ that is tame for $(\mathfrak{m}, \chi)$, there is $\gamma$ with

(a) $|\gamma|^2 = C\big/\bigl(L_*(\mathfrak{m}, c^{-1}\upsilon^m, m)\,L_*(\mathfrak{m}, c\,\upsilon^{m/2}, m/2)\bigr)$, and

(b) for every $x$ in the adelic group of $S$,
$$\gamma\,\mathrm{cs}_h\Bigl(\mathsf{a}(c, h)\,\theta^{S, I_{3m}}_{\upsilon^m, c}[\chi\circ\det, 1](x, h)\Bigr) = \varphi^\circ(x),$$
where the class sum runs over the classes of $I_{3m}$, with index set $\mathrm{Fin}(2m) \sqcup \mathrm{Fin}(m)$.

Lean: `New.Rows.exists_mul_stdClassSum_eq_carrierForm` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Let $J = I_m$ and $H = S$.

Step 1. The first exchange for $k = 0$ gives $C_1$. The character $c^{-1}$ is tame for $(\mathfrak{m}, \chi^{-1})$, so we get $\gamma_1$ with $|\gamma_1|^2 = C_1/L_*(c\upsilon^{m/2}, m/2)$ and $\gamma_1\,\mathrm{cs}(\theta^{J,J}_{c^{-1},c^{-1}}[\chi^{-1}\circ\det, 1]) = 1$. The conjugation lemma gives $n$ and turns this into
$$\bar\gamma_1\,\mathrm{cs}_h\bigl(n\,\chi(\eta)^{-m}\,\theta^{J^-, J}_{c\upsilon^m, c\upsilon^m}[\chi\circ\det, 1](y, h)\bigr) = 1 \quad\text{for all } y. \tag{1}$$

Step 2. Apply the explicit exchange identity with $W = J \oplus H$ of rank $4m$, $V' = J^-$, $V = I_{3m}$ and $d = m$. The ranks satisfy $3m = m + 2m$. The character is $c\upsilon^m$, which is tame of weight $m$, as $\upsilon^m$ has weight $m$ and trivial tame part. This gives $C_2$ and $\gamma_2$ with
$$|\gamma_2|^2 = C_2\big/L_*\bigl((c\upsilon^m)^{-1}\upsilon^{m + m}, m\bigr) = C_2\big/L_*(c^{-1}\upsilon^m, m).$$
Its identity (b) holds for all matched pairs, with the polynomial $P = \prod_\tau\det(y^-_\tau)^{2m}$ of the rows of $H$ of sign $-1$ on the right side.

Step 3. Chain the two exchanges by the one exchange theorem, with $E^b = J$, $W' = H$, the datum $\Psi' = 1$, the polynomial $P$, and (1) as the class sum identity for $F = 1$. It gives
$$\gamma_2\,\bar\gamma_1\,n\,\chi(\eta)^{-m}\,\mathrm{cs}_h\,\mathrm{cs}_g\Bigl(\theta^{J\oplus H, I_{3m}}_{c\upsilon^m, 1}[\Phi, 1]\bigl((g, x), h\bigr)\Bigr) = \int_{[U(J^-)]}\theta^{J^-, H}_{c\upsilon^m, 1}[1, P](y, x)\,dy,$$
where $\Phi(x', x'') = \chi(\det x'')$ and we have swapped the two finite class sums.

Step 4. The datum $\Phi$ is a product of $1$ on the rows of $J$ and $\chi\circ\det$ on the rows of $H$. By the seesaw, the kernel on $J \oplus H$ with characters $c\cdot\upsilon^m$ and $1$ is the product of $\theta^{J, I_{3m}}_{c,1}[1,1](g, h)$ and $\theta^{H, I_{3m}}_{\upsilon^m, 1}[\chi\circ\det, 1](x, h)$. The class sum over $g$ of the first factor is the coefficient $\mathsf{a}(c, h)$, by its definition.

Step 5. The right side of Step 3 is the theta lift of $1$ from $U(J^-)$ to $U(H)$ with polynomial $P$, twisted by $c$. With trivial modulus the finite datum is the indicator of the integral matrices. So the right side is $c(\det x)\,\varphi^\circ(x)$. On the left the kernel with characters $\upsilon^m$, $1$ is $c(\det x)^{-1}$ times the kernel with $\upsilon^m$, $c$. Cancel $c(\det x)$.

Step 6. Put $\gamma = \gamma_2\bar\gamma_1 n/\chi(\eta)^m$. As $|n| = 1$ and $\chi(\eta)$ is a root of unity, $|\gamma|^2 = |\gamma_1|^2|\gamma_2|^2$, which is (a) with $C = C_1C_2$. $\square$

**Remark (Formalization).** The theorem gives no lower bound on $C$. If $C = 0$, then $\gamma = 0$ and (b) says $\varphi^\circ = 0$. That would contradict the theorem below that $\varphi^\circ \neq 0$. So, if the reported checks hold, $C \neq 0$ whenever a tame character of weight $0$ exists. The source does not state this.

### Level, decay and holomorphy

Background in one line each. $\mathrm{rapidOfLevel}(V, N)$ is the space of continuous functions on the adelic group of $V$ that are left invariant under the rational points, right invariant under the principal congruence group $K(N)$, and of rapid decay ([lean:Lib/Weil/DualPair/HolomorphicData.lean#L108](lean:Lib/Weil/DualPair/HolomorphicData.lean#L108)). An order $o$ is *positive first* if it is injective and puts the positive basis vectors before the negative ones ([the holomorphic case](/chapter/discrete-series/)). $F$ is *adelic holomorphic* of weight $u$ for $o$ if every function $h \mapsto F(g(h, 1))$ on the real group is holomorphic of weight $u$ for $o$. The theta kernel of a Fock vector in $\mathrm{holomorphicData}$ is adelic holomorphic (`New.Rows.isAdelicHol_pairTheta`, [lean:Lib/Weil/DualPair/HolomorphicData.lean#L206](lean:Lib/Weil/DualPair/HolomorphicData.lean#L206)). A product of powers of minors lies in $\mathrm{holomorphicData}$ (`New.Rows.prod_variableMinor_mem_holomorphicData`, [neighbours and reproduction](/chapter/siegel-weil/)).

**Theorem (The carrier is a holomorphic form of full level).** Let $m > 0$ be even, and let $c$ be a character of weight $0$ that is tame for some $(\mathfrak{m}, \chi)$. Then

(a) $\varphi^\circ \in \mathrm{rapidOfLevel}(S, N)$ for every integer $N$ of $E$, and

(b) there is a positive first order $o$ on the basis of $S$ such that $\varphi^\circ$ is adelic holomorphic for $o$, of the weight $(0; 3m)$ at every infinite place: $0$ on the positive indices and $3m$ on the negative ones.

Lean: `New.Rows.carrierForm_mem_rapidOfLevel_and_isAdelicHol` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* By the carrier identity, $\varphi^\circ = \sum_i \mathrm{coef}_i\,\theta(h_i)$ is a finite combination, where $\theta(h)(x) = \theta^{S, I_{3m}}_{\upsilon^m, c}[\chi\circ\det, 1](x, h)$. The class sum has finitely many classes, so we can read off the points $h_i$ and the coefficients. Both properties are closed under finite combinations. So it is enough to prove them for each $\theta(h)$.

*Level.* Let $k$ be in `stdLevel`. Right translation of the kernel by $k$ in the group of $S$ multiplies it by $c(\det k)^{-1}\chi(\det k)$, by the action of the level on the datum. Tameness gives $c(\det k) = \chi(\det k)$ for $k$ of this level. So $\theta(h)$ is invariant under `stdLevel`, which contains $K(N)$ for every $N$.

*Rapid decay.* The datum $\chi\circ\det$ vanishes unless $\chi(\det y) \neq 0$, so unless $\det y$ is a unit and $y$ is invertible. A kernel whose datum is supported on matrices with a left inverse decays rapidly (`New.Rows.isRapid_modKernel`, [one exchange](/chapter/exchange-identity-2/#one-exchange-and-the-exchange-data)).

*Automorphy.* A theta kernel is continuous and invariant under the rational points.

*Holomorphy.* Let $o$ be $-1-i$ on the positive index $i \in \mathrm{Fin}(2m)$ and $i$ on the negative index $i \in \mathrm{Fin}(m)$. It is injective. The positive indices get values at most $-1$ and the negative ones values at least $0$, so $o$ is positive first. The polynomial $1$ is the product of the zeroth powers of the minors, so its Fock vector lies in $\mathrm{holomorphicData}$ of weight $(0; 3m)$. Then each $\theta(h)$ is adelic holomorphic of that weight, and so is the finite sum. $\square$

### The carrier is not zero

**Lemma (A constant matrix coefficient).** Let $m > 0$, and let $v$ be the Fock vector of the polynomial $\prod_\tau \det(y^-_\tau)^{2m}$ in the Fock space of the pair $(U(0, m), U(2m, m))$. Let $\Omega$ = `realPairWeil 0 0` be the real Weil representation with both weights $0$. Then $\langle v, \Omega(u, 1)v\rangle = \langle v, v\rangle$ for every $u$ in the compact group $\prod_\tau U(0, m)$.

Lean: `New.Rows.fockInner_realPairWeil_variableMinor_pow_eq_self` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Let $Q = \prod_\tau \det(y^-_\tau)^{2m}$.

Step 1. Each variable of a minor in the rows of sign $-1$ of $S$ has the sign $1$ in the pair. So $Q$ is a polynomial in the variables of sign $1$ only. Expand each determinant as a sum over permutations to see this.

Step 2. An element $g$ of $\prod_\tau U(0, m)$ acts on the variables by linear substitution with $g^{-1}$. A minor $\det(y^-_\tau)$ is scaled by the principal minor of $g_\tau$, which is $\det g_\tau$ as every index has sign $-1$. So $Q$ is scaled by $\prod_\tau \det(g_\tau)^{2m}$.

Step 3. For a polynomial in the variables of sign $1$ that is scaled in this way, the matrix coefficient factors: $c_Q(u, 1) = c_Q(1, 1)\,\mu\,\bar\mu$ with $\mu = m_{(3m)}(u)$ the product of powers of determinants of weight $3m$ (`New.Rows.polyMatrixCoeff_eq_holMinorsPi_mul_conj`, [neighbours and reproduction](/chapter/siegel-weil/)). Here $3m = 2m + m$.

Step 4. $\mu$ is a product of integer powers of the determinants of unitary matrices. Each has modulus $1$, so $\mu\bar\mu = 1$. Hence $c_Q(u, 1) = c_Q(1, 1)$, which is the claim. $\square$

**Theorem (The carrier is not zero).** For every $m > 0$, even or odd, $\varphi^\circ \neq 0$.

Lean: `New.Rows.carrierForm_ne_zero` (New/OneLift/ComparisonOperator/ThreeExchanges.lean).

*Proof.* Let $v$ be the vector of the lemma. It is not $0$, as $Q$ is a nonzero product of nonzero determinants of distinct variables. The group $U(0, m)$ is compact, so its Haar measure is finite and not $0$.

Suppose that $\varphi^\circ = 0$. The modulus of the carrier is trivial, so its finite datum is the vacuum datum, and that datum is sharp (`New.isSharp_vacuumDatum_of_mul_eq_one`, [the inner product formula](/chapter/rallis-inner-product/)). The carrier is the lift of the constant $1$, which is automorphic and of rapid decay on the compact quotient. So the vanishing lemma of the Rallis theory applies ([lean:Lib/SiegelWeil/RallisInner/SharpData.lean#L306](lean:Lib/SiegelWeil/RallisInner/SharpData.lean#L306), `New.realConv_eq_zero_of_lift_eq_zero`): if the lift of $y$ by $v$ and a sharp datum vanishes, and $u \mapsto \langle v, \Omega(u, 1)v\rangle$ is integrable, then the convolution of $u \mapsto \langle v, \Omega(u,1)v\rangle$ with $y$ is $0$. Here $y = 1$, and the integrand is the constant $\langle v, v\rangle$ by the lemma, so it is integrable. At the point $1$ the convolution is $\langle v, v\rangle$ times the measure of the group. Both factors are nonzero. This is a contradiction. $\square$

**Example (The scalar of Step 2).** Take $m = 2$ and one infinite place. The space $S$ has signature $(4, 2)$, and $Q = \det(y^-)^4$ where $y^-$ is the $2 \times 2$ block of the two negative rows. The element $u = \mathrm{diag}(e^{ia}, e^{ib})$ of $U(0, 2)$ substitutes $y^- \mapsto y^-u^{-1}$, so it scales $\det y^-$ by $e^{-i(a+b)}$ and $Q$ by $e^{-4i(a+b)}$. This scalar has modulus $1$. So $c_Q(u, 1) = c_Q(1, 1)$, and the integral over $U(0, 2)$ in the proof is $\langle v, v\rangle$ times the volume of $U(0,2)$.
