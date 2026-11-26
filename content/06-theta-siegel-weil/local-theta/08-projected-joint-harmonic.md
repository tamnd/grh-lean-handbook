---
title: The projected joint harmonic
lean:
  - Lib/DiscreteSeries/Theta/LocalCorrespondence.lean
  - Lib/Weil/Fock/OscillatorPair.lean
decls:
  - New.OscillatorRep
  - New.OscillatorPair
  - New.Fock.oscillatorPair_detTwist
  - New.OscillatorPair.swap
  - New.OscillatorPair.map_integratedRep_dsKernel
  - New.OscillatorPair.isDerivedAction_integratedRep
  - New.OscillatorPair.re_inner_integratedRep_pos
  - New.OscillatorPair.integratedRep_integratedRep_eq_self
  - New.OscillatorPair.integratedRep_oscRows_eq_zero
  - New.OscillatorPair.exists_bump_integratedRep_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The projected joint harmonic

This section passes from polynomials to the representations of the two groups on the Fock space. It proves three analytic results. Let $\Phi$ be a joint harmonic and $\pi(e_\lambda)$ the operator of the discrete series kernel of the first group. Then $\operatorname{Re}\langle\Phi, \pi(e_\lambda)\Phi\rangle > 0$. The vector $\pi(e_\lambda)\Phi$ is fixed by $\pi'(f)$ for every $f$ of suitable decay that reproduces $e_{\lambda'}$. For every polynomial $P$, the vector $\pi(e_\lambda)P$ is a smoothing of $\pi(e_\lambda)\Phi$ by a bump function on the second group.

The analytic input comes from [discrete series through one matrix coefficient](/chapter/discrete-series/). Its theorems apply to a representation on a normed space with an invariant positive definite form, a polynomial growth bound, and a module of $\mathfrak{gl}_n$ that is the derivative along a linear map. Here the space is the Fock space, the map is $P \mapsto v_P$, and the module is the row action or the column action.

### Oscillator pairs

**Definition (Oscillator representation).** Let $T$ be dual pair data with variables indexed by $I$, and let $\eta$ be the signs of the variables. An *oscillator representation* for $T$ is a homomorphism $\pi$ from $U(\varepsilon)$ to the bounded operators on the Fock space of $\eta$ such that the following hold.
1. $\pi$ is strongly continuous, it preserves the form $\langle\cdot,\cdot\rangle$ of the Fock space, and $\|\pi(g)\| \leq C\|g\|^{|I|}$ for a constant $C$.
2. On the vectors $v_P$ of polynomials, the derivative of $\pi$ is the row action of $T$.
3. If $P \neq 0$ is termwise harmonic for $T$ and $z \in U(\varepsilon)$ is positive definite, then $\langle v_P, \pi(z)v_P\rangle > 0$.

Lean: `New.OscillatorRep` (Lib/Weil/Fock/OscillatorPair.lean).

**Definition (Oscillator pair).** An *oscillator pair* for $T$ is a pair of maps $\pi$ of $U(\varepsilon)$ and $\pi'$ of $U(\varepsilon')$ to the bounded operators on one Fock space such that $\pi$ is an oscillator representation for $T$, $\pi'$ is an oscillator representation for the swap, and $\pi(g)$ commutes with $\pi'(h)$ for all $g$, $h$.

Lean: `New.OscillatorPair` (Lib/Weil/Fock/OscillatorPair.lean).

Conditions 1 and 2 are `New.IsUnitaryRep` and `New.IsDerivedAction`. The derivative is taken along the map `New.Fock.polyVector`, which sends $P$ to $v_P(x) = P(\zeta(x))e^{-|x|^2/2}$, where $\zeta(x)_i$ is $\bar x_i$ at positive and $x_i$ at negative coordinates.

**Theorem.** Let $R$, $C$ be finite sets with signs $\varepsilon$, $\varepsilon'$, and let $\gamma$, $\gamma'$ be integers. On the Fock space of the $R \times C$ matrices, with sign $\varepsilon_r\varepsilon'_c$ at the entry $(r, c)$, let $\omega$ be the Weil representation. Then $h \mapsto (\det h)^\gamma\,\omega(x \mapsto hx)$ of $U(\varepsilon)$ and $g \mapsto (\det g)^{\gamma'}\,\omega(x \mapsto xg^{-1})$ of $U(\varepsilon')$ form an oscillator pair for the standard data with sign $1$ and integers $\gamma$, $\gamma' + |R|$.

Lean: `New.Fock.oscillatorPair_detTwist` (Lib/Weil/Fock/OscillatorPair.lean).

*Proof.* The construction and the proof of the three conditions are in [the Weil representation from a vacuum](/chapter/weil-representation/). $\square$

For this model the source cites M. G. Davidson, Pacific J. Math. 129 (1987), §1 and Prop. 2.2, G. B. Folland, *Harmonic Analysis in Phase Space* (1989), chapters 1 and 4, and H. Reiter, *Metaplectic Groups and Segal Algebras*, LNM 1382 (1989).

**Proposition.** Let $R$ and $C$ be nonempty. If $\pi$, $\pi'$ form an oscillator pair for $T$, then $\pi'$, $\pi$ form an oscillator pair for the swap.

Lean: `New.OscillatorPair.swap` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* The swap of the swap is $T$, and the commutation is symmetric. $\square$

### The operator of the kernel

For a function $f$ on $U(\varepsilon)$, the operator $\pi(f)$ is $\int f(g)\pi(g)\,dg$, in Lean `New.integratedRep`. Let $e_\lambda$ be the discrete series kernel `New.HCParam.dsKernel`, that is, $g \mapsto d_\lambda\,\overline{c_\lambda(g)}$ with the formal degree $d_\lambda$.

**Lemma.** Let $\Phi$ be a joint harmonic for $T$, $l$, $l'$, and let $\pi$, $\pi'$ be an oscillator pair.
1. $\pi'(g')\,\pi(e_\lambda) = \pi(e_\lambda)\,\pi'(g')$ for every $g'$.
2. Along the map $P \mapsto \pi(e_\lambda)v_P$, the derivative of $\pi'$ is the column action.

Lean: `New.OscillatorPair.map_integratedRep_dsKernel` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean). The second part is `New.OscillatorPair.isDerivedAction_integratedRep`.

*Proof.* Matching gives the large gap with $A = |I|$ (`New.IsMatch.hasLargeGap`), so $g \mapsto e_\lambda(g)\|g\|^{|I| + 1}$ is integrable. Then a bounded operator $L$ can be moved under the integral: $L\,\pi(e_\lambda)x = \int e_\lambda(g)L\pi(g)x\,dg$ (`New.map_integratedRep`). Take $L = \pi'(g')$ for part 1. For part 2, apply the bounded operator $\pi(e_\lambda)$ to the derivative of $t \mapsto \pi'(\exp tY)v_P$, and use part 1. $\square$

### Positivity

**Theorem.** Let $\pi$, $\pi'$ be an oscillator pair for $T$, with $R$, $C$ nonempty, and let $\Phi$ be a joint harmonic for $T$, $l$, $l'$. Then
$$\operatorname{Re}\,\langle v_\Phi,\ \pi(e_\lambda)v_\Phi\rangle > 0.$$

Lean: `New.OscillatorPair.re_inner_integratedRep_pos` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* The polynomial $\Phi$ is not zero, termwise harmonic, and $K$-highest of weight $\Lambda$ for the row action. By condition 3 of an oscillator representation, $\langle v_\Phi, \pi(z)v_\Phi\rangle > 0$ for every positive definite $z$. The positivity theorem of the previous volume (`New.re_integratedRep_dsKernel_pos`) applies. $\square$

In particular $\pi(e_\lambda)v_\Phi \neq 0$.

### The fixed vector

**Theorem.** Let $\pi$, $\pi'$ be an oscillator pair for $T$, with $R$, $C$ nonempty, and let $\Phi$ be a joint harmonic for $T$, $l$, $l'$. Let $f$ be a function on $U(\varepsilon')$ such that $g \mapsto f(g)\|g\|^{|I|}$ is integrable and
$$\int f(y)\,e_{\lambda'}(y^{-1}g)\,dy = e_{\lambda'}(g) \quad \text{for every } g.$$
Then $\pi'(f)\,\pi(e_\lambda)v_\Phi = \pi(e_\lambda)v_\Phi$.

Lean: `New.OscillatorPair.integratedRep_integratedRep_eq_self` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* Put $p(P) = \pi(e_\lambda)v_P$. By the last lemma, $p$ is a map along which the derivative of $\pi'$ is the column action. The polynomial $\Phi$ is $K$-highest of weight $\Lambda'$ for the column action. By the fixed vector theorem of the previous volume (`New.integratedRep_fix_of_isKHighest`), it suffices that $p(\Omega'\Phi) = \kappa_{\lambda'}\,p(\Phi)$, where $\Omega'$ is the Casimir element of the column action.

The Casimir element of the first group acts on the image of $\pi(e_\lambda)$ by $\kappa_\lambda$ (`New.integratedRep_dsKernel_casimir`), so $p(\Omega\Phi) = \kappa_\lambda\,p(\Phi)$. Section 6 carries this to the second group. The row weight of $\Phi$ is $\Lambda$, so $p(\Omega_{c_T}\Phi) = (|u|^2 - |\rho|^2)\,p(\Phi)$. The centred Casimir elements differ by $nn'(n - n')/4$, and the comparison of Casimir values gives $p(\Omega'_{c_{T'}}\Phi) = (|u'|^2 - |\rho'|^2)\,p(\Phi)$. The column weight of $\Phi$ is $\Lambda'$, so restoring the centre gives $p(\Omega'\Phi) = \kappa_{\lambda'}\,p(\Phi)$. $\square$

### Vectors killed by the kernel

**Theorem.** Let $\pi$, $\pi'$ and $\Phi$ be as above. Let $Q$ be $K$-highest of weight $\nu$ for the row action, with $\nu - \Lambda$ not in the cone of the positive roots of $l$. Then $\pi(e_\lambda)v_{\rho(Y)Q} = 0$ for every complex matrix $Y$.

Lean: `New.OscillatorPair.integratedRep_oscRows_eq_zero` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* By the theorem of the previous volume on weights off the cone (`New.integratedRep_eq_zero_of_notMem_rootCone`), $\pi(e_\lambda)$ kills every translate $\pi(y)v_Q$. For $Y$ in the Lie algebra of $U(\varepsilon)$, the vector $v_{\rho(Y)Q}$ is the derivative of $t \mapsto \pi(\exp tY)v_Q$ at $0$, and the bounded operator $\pi(e_\lambda)$ kills it. Write a complex matrix as $Y_1 + iY_2$. $\square$

### The smoothing statement

Let $\mathcal{B}(\varepsilon')$ be the space of smooth functions with compact support on $U(\varepsilon')$, in Lean `New.DiscreteSeries.Bumps`. For a continuous function $F$ on $U(\varepsilon')$, the *smoothing* of $F$ by $\alpha$ is $g \mapsto \int\alpha(y^{-1})F(gy)\,dy$ (`New.DiscreteSeries.smear`). Its derivative along a curve $\gamma$ with $\gamma'(t) = \gamma(t)Y$ is the smoothing of $F$ by the right derivative $Y\alpha$ (`New.DiscreteSeries.hasDerivAt_smear`).

**Theorem (Smoothing).** Let $\pi$, $\pi'$ be an oscillator pair for $T$, with $R$, $C$ nonempty, and let $\Phi$ be a joint harmonic for $T$, $l$, $l'$. Then for every polynomial $P$ there is $\alpha \in \mathcal{B}(\varepsilon')$ with
$$\pi(e_\lambda)v_P = \pi'(g \mapsto \alpha(g^{-1}))\,\pi(e_\lambda)v_\Phi.$$

Lean: `New.OscillatorPair.exists_bump_integratedRep_eq` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* Put $p(P) = \pi(e_\lambda)v_P$, and let $S(\alpha) = \pi'(g \mapsto \alpha(g^{-1}))\,p(\Phi)$. Then $S(\alpha)$ is the value at $1$ of the smoothing of $g \mapsto \pi'(g)p(\Phi)$ by $\alpha$. Let $G$ be the space of polynomials $P$ with $p(P)$ in the image of $S$. It suffices to prove that $G$ is the space of all polynomials. Apply Howe's argument of Section 7.

*$G$ is stable under the column action.* Let $p(y) = S(\beta)$. For $Z$ in the Lie algebra of $U(\varepsilon')$, differentiate $t \mapsto \pi'(\exp tZ)p(y)$ at $0$ in two ways. By part 2 of the lemma on the kernel, the derivative is $p(\rho'(Z)y)$. By the rule for the derivative of a smoothing, it is $S(Z\beta)$. So $p(\rho'(Z)y) = S(Z\beta)$. A complex matrix is $Z_1 + iZ_2$.

*$G$ contains $\Phi$.* The large gap gives a bump function $\alpha$ with $\int\alpha(x^{-1})e_{\lambda'}(x^{-1}g)\,dx = e_{\lambda'}(g)$ (`New.HCParam.HasLargeGap.exists_bump_conv_dsKernel`). The fixed vector theorem gives $S(\alpha) = p(\Phi)$.

*Hypothesis 1.* By the last theorem, $p(\rho(Y)Q) = 0 = S(0)$.

*Hypotheses 2 and 3.* Integration by parts (`New.exists_integration_by_parts`) gives a linear map $\mathcal{A}$ from the module generated by $c_{-\lambda}$ under right derivatives to the bounded operators, with $\pi(e_\lambda) = \mathcal{A}(c_{-\lambda})$ and $\mathcal{A}(f)\,v_{\rho(Y)P} = -\mathcal{A}(Yf)\,v_P$. The generator $c_{-\lambda}$ is $K$-highest of weight $\Lambda(-l)$ for $-l$ (`New.isKHighest_dsGenerator`). For $\varepsilon_a = \varepsilon_b$ and $l_b < l_a$, integration by parts moves $E_{ba}$ onto $c_{-\lambda}$, and the compact lowering operators of $l$ kill $c_{-\lambda}$. So $p(\rho(E_{ba})P) = 0$. In the same way $p(\rho(E_{aa})P - \Lambda_aP) = 0$, since $c_{-\lambda}$ has the weight $-\Lambda$. So these polynomials lie in $G$, with $\beta = 0$.

Howe's argument gives that $G$ is the space of all polynomials. $\square$

The docstring of the theorem says that it "is used in place of Howe's duality theorem for real unitary pairs" and that it "is proved by Howe's argument (`New.IsJointHarmonic.howe_argument`) instead of through irreducibility".

Lib/Weil/Lift.lean applies these theorems at each infinite place, to `New.Fock.oscillatorPair_detTwist`.

**Remark (Formalization).** Several points of the formal statements differ from the textbook account.
1. *Howe duality is replaced, not proved.* No theorem of the source states that the theta correspondence is a bijection, that a theta lift is irreducible, or that the multiplicity of $\pi \otimes \pi'$ in $\omega$ is at most one. The smoothing theorem takes the place of these. The source does prove the uniqueness of the joint harmonic (Section 5), which is a multiplicity one statement for one $K$-type.
2. *The Fock space is the L¹ space.* The space `New.Fock.fockSpace` is the space of integrable functions $c$ on $\mathbb{C}^I$ that reproduce themselves against the vacuum, with the $L^1$ norm. The docstring says: "the space is the L¹ (Feichtinger) space of vacuum coefficients rather than the Hilbert Fock space". The analytic theorems of the previous volume need only a normed space with an invariant positive definite form.
3. *The operator $\pi(f)$ can be a junk value.* The operator `New.integratedRep` is `New.strongIntegral`, defined with `Function.invFun`. If no bounded operator agrees with $x \mapsto \int f(g)\pi(g)x\,dg$, it is an unspecified operator. The theorems here prove integrability first.
4. *The kernel can be $0$.* The formal degree `New.HCParam.formalDegree` is the inverse of the Bochner integral of $|c_\lambda|^2$. If $c_\lambda$ is not square integrable, the integral is $0$ in Lean, and so is its inverse. Then $e_\lambda = 0$. The large gap hypothesis, which matching gives, excludes this case.
5. *Choices.* The joint harmonic of the global argument is `New.jointHarmonicAt`, chosen by `Classical.epsilon`. It is an arbitrary polynomial if no joint harmonic exists. The existence theorem of Section 4 removes this case when the parameters correspond. Lib/Weil/Lift.lean picks the bump functions of the smoothing theorem with `choose`.
6. *Signs.* `New.jointHarmonicAt` uses the standard data on $n' \times n$ variables with the integers $\gamma$ and $-\gamma'$ and the parameters $l'$ and $-l$. The source docstring says that the results for $-\lambda$ follow by applying them to $-l$ and $-l'$, since "the kernel `e_{-λ}` is the conjugate of `e_λ`".

The source claims these results. Lean accepts them, if the reported checks hold.
