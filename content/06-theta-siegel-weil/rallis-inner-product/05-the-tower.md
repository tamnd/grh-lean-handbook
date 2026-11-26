---
title: The tower
lean:
  - Lib/SiegelWeil/Tower/ConstantTerm.lean
  - Lib/SiegelWeil/Tower/LineTerms.lean
  - Lib/SiegelWeil/Tower/LineGaussSums.lean
  - Lib/SiegelWeil/Tower/RealConeIntegral.lean
  - Lib/SiegelWeil/Tower/FiniteTateIntegral.lean
  - Lib/SiegelWeil/Tower/FunctionalEquation.lean
  - Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean
decls:
  - New.Exchange.constTermAt
  - New.Exchange.hasSum_constTermAt
  - New.Exchange.integral_thetaIntegral_lineRadical
  - New.Exchange.exists_unfold_constant_term
  - New.Exchange.lineTerm
  - New.Exchange.tsum_lineTerm
  - New.Exchange.exists_lineTerm_localDatum
  - New.Exchange.lValueProd
  - New.Exchange.lValueProdInt
  - New.Exchange.lSharp
  - New.Exchange.SplitTameChar.L_ne_zero
  - New.Exchange.lSharp_pos
  - New.Exchange.lValueProd_succ
  - New.Exchange.lValueProdInt_succ
  - New.Exchange.lValueProdInt_neg
  - New.Exchange.finTateIntegrand
  - New.Exchange.integral_finTateIntegrand
  - New.Exchange.exists_analytic_extension_functional_equation
  - New.Exchange.exists_analytic_extension_ne_zero
  - New.Exchange.coneIntegrand
  - New.Exchange.cone
  - New.Exchange.dualCone
  - New.Exchange.IsSchwartzVector
  - New.Exchange.planeConstantTerm
  - New.Exchange.exists_zetaIntegral
  - New.Exchange.exists_planeConstantTerm_eq_thetaLarge_cone
  - New.Exchange.exists_planeConstantTerm_eq_thetaLarge_dualCone
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The tower

This section compares theta integrals for two pairs of spaces. Add a hyperbolic plane $H$ to each space of a pair $(W, V)$. This gives a pair $(W', V')$ with $W' = W \oplus H$ and $V' = V \oplus H$. The new isotropic line of $W'$ has a parabolic subgroup, and a theta integral of $(W', V')$ has a constant term along it. The main result of the section says that on standard data this constant term is a scalar $\gamma$ times a theta integral of $(W, V)$. The modulus $|\gamma|$ is a positive constant times a Hecke $L$-value with factors at the ramified places. In the literature this is the *tower property* of theta lifts. In the source the isotropic orbit does not vanish. It gives a Tate integral, which gives the $L$-value.

### The setting

Let $W'$ and $V'$ be hermitian spaces over $E$. A splitting `A : W'.Splitting W Unit` writes $W'$ as a hyperbolic plane plus $W$, with dual isotropic vectors $k$ and $l$. A splitting `X : V'.Splitting V Unit` does the same for $V'$. The isotropic line of $W'$ is spanned by the vector $k$ of $A$. Its stabilizer has a unipotent radical, with coordinates $q = (q_1, q_2)$, where $q_1$ is a column with entries indexed by the frame of $W$ and $q_2$ is a scalar. The *constant term* of a function along the line is its mean over the radical modulo its rational points. 
### The constant term of the theta kernel

**Definition.** For a rational vector $x$ of $V$ and a datum $f$ on $\operatorname{Hom}(W', V)$, the *term of* $x$ is $0$ if $\langle x, x \rangle \neq 0$. If $x$ is isotropic, it is the mean over $q_1$ of the term of $x$ in the theta kernel of $f$ at the point $q = (q_1, 0)$ of the radical.

Lean: `New.Exchange.constTermAt` (Lib/SiegelWeil/Tower/ConstantTerm.lean).

The coordinate $q_2$ acts on the term of $x$ by $\psi(\operatorname{tr}(\langle x, x \rangle q_2))$, whose mean is $0$ unless $x$ is isotropic.

**Lemma.** For every datum $f$ on $\operatorname{Hom}(W', V)$ the terms of all rational vectors of $V$ have the sum
$$\sum_{x} c_x(f) = \int \theta(\omega(q, 1) f)\, dq,$$
the constant term of the theta kernel along the line. Suppose that the theta kernel grows at most like a power of the height on the group of $W'$, uniformly on the group of $V$. Then the constant term of the theta integral over $[U(V)]$ is the integral over $h \in [U(V)]$ of the sum of the terms for the datum moved by $(g, h)$.

Lean: `New.Exchange.hasSum_constTermAt`, `New.Exchange.integral_thetaIntegral_lineRadical` (Lib/SiegelWeil/Tower/ConstantTerm.lean).

The bound on the growth is the hypothesis `IsTargetBounded`.

Now take the target space $V'$ in place of $V$. The isotropic vectors of $V'$ fall into two kinds. The zero vector gives one term. A nonzero isotropic vector spans an isotropic line. By the theorem of Witt, all isotropic lines of $V'$ are in one orbit of $U(V')(E)$, the orbit of the line of $X$. The sum over the lines of this orbit unfolds the integral over $[U(V')]$ to an integral over the stabilizer of the line.

**Lemma (Unfolding along the isotropic lines).** There is a real number $c \neq 0$, which depends only on the splittings $A$ and $X$, with the following property. Let $a$, $b$ be characters of $[U(1)]$, let $f$ be a datum on $\operatorname{Hom}(W', V')$ and $g$ a point of $U(W')(\mathbb{A})$. Write $F(h) = \omega(g, h) f$. In Iwasawa coordinates $((u, h), \kappa)$, with $u$ an idele modulo $E^\times$, $h \in [U(V)]$ and $\kappa$ in the maximal compact subgroup of $U(V')$, put
$$\Theta((u, h), \kappa) = |u|^{\operatorname{rk} V + 1} \sum_{\xi \in E^\times} \theta\bigl(\ell_\xi(F(m(u, h)\kappa))\bigr),$$
where $m(u, h)$ is the Levi point and $\ell_\xi$ is the line term at $\xi$ defined below. If the term of the zero vector is $0$ for every $h$ and $\Theta$ is integrable, then
$$\int_{[U(V')]} \sum_{x} c_x(F(h))\, dh = c \int \Theta.$$

Lean: `New.Exchange.exists_unfold_constant_term` (Lib/SiegelWeil/Tower/ConstantTerm.lean).

*Proof.* Group the terms by the line that the vector spans. A line with a nonzero term is isotropic, so the theorem of Witt gives $\gamma \in U(V')(E)$ that carries it to the line of $X$. Only the lines of this orbit contribute. The sum over the orbit unfolds the integral over $[U(V')]$ to an integral over the stabilizer of the line of $X$ modulo its rational points. The integrand is invariant under the radical, and Iwasawa coordinates give the power of $|u|$ and $c$. $\square$

### Poisson's formula along the line

**Definition.** For an adele $\xi$ and a model $\beta \in \{\text{true}, \text{false}\}$, the *line term* $\ell^\beta_\xi$ is a map from data on $\operatorname{Hom}(W', V')$ to data on $\operatorname{Hom}(W, V)$. For $\beta = \text{true}$ it translates $f$ by $\xi$ times the vector $k$ of $X$ and then takes both zero terms. For $\beta = \text{false}$ the roles of the two lines of the plane are exchanged.

Lean: `New.Exchange.lineTerm` (Lib/SiegelWeil/Tower/LineTerms.lean).

**Lemma (Poisson's formula on the line).** For every datum $f$ on $\operatorname{Hom}(W', V')$ and each model $\beta$,
$$\sum_{\xi \in E} \theta\bigl(\ell^{\text{true}}_\xi f\bigr) = \sum_{\xi \in E} \theta\bigl(\ell^{\beta}_\xi f\bigr).$$

Lean: `New.Exchange.tsum_lineTerm` (Lib/SiegelWeil/Tower/LineTerms.lean).

*Proof.* The two models are the two mixed models of one hyperbolic plane of $\operatorname{Hom}(W', V')$. In each model the sum is the expansion of the theta functional of the zero term of $f$ along this plane. So both sums are equal to that theta value. $\square$

In the application neither side of Poisson's formula has a term at $\xi = 0$. So the Tate integral below is analytic on the whole real line.

### The local line terms

At the finite places the data are standard data. At the ramified places $S$ of a tame character $\chi$, the datum `stdRowDatum σ χ y` sends $x$ to $\chi^{-1}$ of the determinant of the matrix with the rows of $y$ and $x$ if that matrix is integral with an integral inverse, and to $0$ otherwise. At the other finite places the datum is the vacuum. The real part is a vector $v$ in the Fock space.

**Lemma.** Let $A$ and $X$ be adapted splittings. There are nonzero constants $l_\beta$ with the following property. For every tame character $\chi$ at a set $S$ of places there is a number $\gamma$ with $|\gamma|^2 = 1/\#R$, where $R$ is the residue ring at $S$. Put $a = \xi\alpha_0^{-1}$, where $\alpha_0$ is a fixed idele. Then $\ell^\beta_\xi$ maps the datum with real part $v$ and standard datum of $y$ at $S$ to
$$l_\beta\, \gamma\, \chi^{-1}(a)\, \chi(\varpi \bar a)$$
times the datum with real part $\ell^\beta_{a_\infty}(v)$ and the standard datum of $y$ for $(W, V)$ at $S$. This holds if the finite part of $a$ is integral off $S \cup \bar S$ and $a$ and $\varpi \bar a$ are units at $S$. Otherwise the image is $0$.

Lean: `New.Exchange.exists_lineTerm_localDatum` (Lib/SiegelWeil/Tower/LineGaussSums.lean).

The number $\gamma$ is a Gauss sum of $\chi$. The finite factor $\chi^{-1}(a)\chi(\varpi \bar a)$ is the test function of a Tate integral at the finite places.

### Products of $L$-values

The rest of the section uses a *split tame character* $\mathfrak{c}$. This is a character $\nu$ of $[U(1)]$ of positive weight $\mu$, tamely ramified exactly at a nonempty finite set $S$ of split places that is disjoint from its conjugate. Write $L^S(z, \nu)$ for the Euler product of the base change of $\nu$ without the factors at $S \cup \bar S$, and $q_w$ for the order of the residue field at $w$.

**Definition.** For $e \in \mathbb{N}$ put
$$L_*(e) = \Bigl(\prod_{w \in S} q_w\Bigr)^{e^2} \prod_{z = 1}^{e} |L^S(z, \nu)|^2,$$
and extend $L_*$ to all integers by $L_*(-e) = L_*(e)^{-1}$. For real $z$ put
$$L^\sharp(z) = |L^S(z, \nu)| \prod_{w \in S} q_w^{z - 1/2}.$$

Lean: `New.Exchange.lValueProd`, `New.Exchange.lValueProdInt`, `New.Exchange.lSharp` (Lib/SiegelWeil/Tower/FiniteTateIntegral.lean).

**Lemma.** For real $z \ge 1$, $L^S(z, \nu) \neq 0$ and $L^\sharp(z) > 0$. For every $z \in \mathbb{N}$,
$$L_*(z + 1) = L^\sharp(z + 1)^2\, L_*(z), \qquad L_*(-z) = L^\sharp(z + 1)^2\, L_*(-z - 1).$$

Lean: `New.Exchange.SplitTameChar.L_ne_zero`, `New.Exchange.lSharp_pos`, `New.Exchange.lValueProd_succ`, `New.Exchange.lValueProdInt_succ`, `New.Exchange.lValueProdInt_neg` (Lib/SiegelWeil/Tower/FiniteTateIntegral.lean).

*Proof.* The weight of $\nu$ is not zero, so the Euler product has no zero for $z \ge 1$. The factor over $S$ is a product of positive powers. For the first recursion,
$$\Bigl(\prod_{w \in S} q_w^{z + 1/2}\Bigr)^2 = \Bigl(\prod_{w \in S} q_w\Bigr)^{2z + 1} \quad\text{and}\quad (z + 1)^2 = z^2 + 2z + 1.$$
The second recursion follows from the first by taking inverses, as $L^\sharp(z + 1) \neq 0$. $\square$

**Example.** As $L_*(0) = 1$, the recursion gives $L_*(1) = L^\sharp(1)^2 = |L^S(1, \nu)|^2 \prod_{w \in S} q_w$.

### Tate's integral and the functional equation

**Definition.** For real $x$ the *Tate integrand* on the finite ideles is the finite factor $\chi^{-1}(a)\chi(\bar a)$ of the line term, read as $0$ off the integral units, times the base change of $\nu$ at $a$, times $|a|^x$.

Lean: `New.Exchange.finTateIntegrand` (Lib/SiegelWeil/Tower/FiniteTateIntegral.lean).

**Lemma.** Let $\rho$ be a Haar measure on the finite ideles and let $x > 1$. The Tate integrand is integrable, and its integral is $L^S(x, \nu)$ times the $\rho$-volume of the integral unit ideles.

Lean: `New.Exchange.integral_finTateIntegrand` (Lib/SiegelWeil/Tower/FiniteTateIntegral.lean).

The textbook result on these integrals is the theorem of Tate. Let $\chi$ be a Hecke character of a number field. Then the completed $L$-function $\Lambda(s, \chi)$ has a meromorphic continuation to $\mathbb{C}$, entire unless $\chi$ is a power of the norm, and it satisfies $\Lambda(s, \chi) = \varepsilon(s, \chi)\, \Lambda(1 - s, \chi^{-1})$, with $\varepsilon(s, \chi)$ an exponential in $s$ that has no zero.

It follows from the Main Theorem 4.4.1 of J. Tate, *Fourier analysis in number fields and Hecke's zeta-functions*, thesis (1950), printed in J. W. S. Cassels and A. Fröhlich (eds.), *Algebraic Number Theory* (1967). The source states a special case: real arguments and absolute values only.

**Theorem (Functional equation on a real interval).** Let $k \in \mathbb{N}$ with $k \le \mu_w$ at every infinite place $w$. There is a function $C$ on $\mathbb{R}$ with $C(z) > 0$ for $1 \le z < k + 1$ such that the following holds for every split tame character of weight $\mu$. There is a function $\Lambda$, real analytic on $(-k, \infty)$, with $\Lambda(x) = L^S(x, \nu)$ for $x \ge 1$, and
$$|\Lambda(1 - z)| \prod_{w \in S} q_w^{1 - z - 1/2} = C(z)\, L^\sharp(z) \qquad (1 \le z < k + 1).$$

Lean: `New.Exchange.exists_analytic_extension_functional_equation` (Lib/SiegelWeil/Tower/FunctionalEquation.lean).

*Proof.* Take Tate's zeta integral $\mathcal{Z}$ for a test function at the real places that is a product of $\bar a_w^{2\mu_w} e^{-|a_w|^2}$. By Poisson's formula, $\mathcal{Z}$ is analytic on $\mathbb{R}$, and for $x \ge 1$ both $\mathcal{Z}(x)$ and $\mathcal{Z}(1 - x)$ are $L^S(x, \nu)$ times explicit factors: a constant of fixed modulus, a power of $|\alpha_0|$, the product over $S$, a gamma integral and a fixed number $\kappa \neq 0$. The gamma integral is positive and analytic for $x > -k$, because $k \le \mu_w$. Put $\Lambda = \mathcal{Z}/F$, where $F$ is the product of the factors of $\mathcal{Z}(x)$ other than $L$. The quotient of the moduli of the factors at $1 - z$ and at $z$ is $C(z)$. $\square$

**Corollary.** In the same setting, $\Lambda(j) \neq 0$ for every integer $j > -k$.

Lean: `New.Exchange.exists_analytic_extension_ne_zero` (Lib/SiegelWeil/Tower/FunctionalEquation.lean).

*Proof.* For $j \ge 1$, $\Lambda(j) = L^S(j, \nu) \neq 0$. For $-k < j \le 0$, put $z = 1 - j$, so $1 \le z < k + 1$. If $\Lambda(j) = 0$, the functional equation gives $C(z) L^\sharp(z) = 0$. This is false, as $C(z) > 0$ and $L^\sharp(z) > 0$. $\square$

**Remark (Formalization).** The source does not prove the theorem of Tate for complex $s$. It treats only real $x > -k$ and only absolute values, and the root number is not computed. The function $C$ comes from an existence statement and is not given. It is positive only on $[1, k + 1)$; its values outside this interval are not used. The function $\Lambda$ also comes from an existence statement.

### The constant term on the large side

Now let $\operatorname{rk} W$ be even and put $e = \operatorname{rk} V - \operatorname{rk} W / 2$. The *plane datum* of a Fock vector $v'$ and an integral matrix $y$ at $S$ is the datum on $\operatorname{Hom}(W', V')$ with real part $v'$, the standard datum of $y$ composed with the projection to $W$ at $S$, and the vacuum elsewhere. Write $\Theta'$ for its theta integral over $[U(V')]$, with the twists given by $\nu$, and $\Theta'_A(u, g)$ for the constant term of $\Theta'$ along the line of $A$ at the Levi point $(u, g)$.

Lean: `New.Exchange.planeConstantTerm` (Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean).

At the real places the source uses a *cone integral*. For a Fock vector $v'$ and a real number $z$, the integrand at $(\kappa, a)$, with $\kappa$ in the maximal compact subgroup of $U(V')$ and $a$ an archimedean idele, is the real line term $\ell^\beta_a$ of $\kappa v'$ times $\prod_w (a_w/|a_w|)^{2\mu_w}$ times $|a|^z$. The cone integral $\operatorname{cone}(z, v')$ integrates this for $\beta = \text{true}$. The dual cone integral $\operatorname{cone}^\vee(z, v')$ does the same for $\beta = \text{false}$, on the other side of Poisson's formula. A Fock vector is a *Schwartz vector* if all its moments $\int (1 + \|y\|)^N |v(y)|\, dy$ are finite.

Lean: `New.Exchange.coneIntegrand`, `New.Exchange.cone`, `New.Exchange.dualCone` (Lib/SiegelWeil/Tower/RealConeIntegral.lean), `New.Exchange.IsSchwartzVector` (Lib/Weil/Fock/WeightedNorms.lean).

**Proposition (The zeta integral).** There are constants $C_\beta > 0$, for $\beta \in \{\text{true}, \text{false}\}$, such that for every split tame character there are $\varepsilon_\beta$ with $|\varepsilon_\beta| = C_\beta$ and the following property. Let $v'$ be a Schwartz vector, $y$ integral, and $(u, g)$ a Levi point with $u = 1$ or $\operatorname{rk} V = \operatorname{rk} W$. Then there is a function $\mathcal{Z}$, analytic on $\mathbb{R}$, with $\Theta'_A(u, g) = \mathcal{Z}(e + 1)$. For $x \ge 1$,
$$\mathcal{Z}(x) = \varepsilon_{\text{true}}\, |\alpha_0|^x \prod_{w \in S} q_w^{x - 1/2}\, L^S(x, \nu)\, I_{\text{true}}(x), \qquad \mathcal{Z}(1 - x) = \varepsilon_{\text{false}}\, |\alpha_0|^x \prod_{w \in S} q_w^{x - 1/2}\, L^S(x, \nu)\, I_{\text{false}}(x),$$
where $I_\beta(x)$ is the theta integral of $(W, V)$ at $g$ of the datum with the cone integral of side $\beta$ and exponent $x$ at the real places and the standard datum of $y$ at $S$.

Lean: `New.Exchange.exists_zetaIntegral` (Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean).

*Proof.* The plane datum has no term at the zero vector along $A$, so the unfolding lemma applies. It writes $\Theta'_A(u, g)$ as a constant times an integral over the ideles, which is $\mathcal{Z}(e + 1)$. The datum factors along the line, so for $x > 1$ the integral is a product. The local lemma gives the finite part, the Tate integrand, times the Gauss sum $\gamma$. Its integral is $L^S(x, \nu)$ times a volume. The real part gives the cone integral. The modulus of $\gamma \sqrt{\prod_{w \in S} q_w}$ is $1$, so $|\varepsilon_\beta|$ does not depend on the character. The value at $x = 1$ follows by continuity. $\square$

**Theorem (One plane).** Let $\operatorname{rk} W$ be even.

1. Let $e = z \ge 0$. There is $C > 0$ such that for every split tame character there is $\gamma$ with $|\gamma| = C\, L^\sharp(z + 1)$ and, for every Schwartz vector $v'$, integral $y$, and Levi point $(u, g)$ with $u = 1$ or $\operatorname{rk} V = \operatorname{rk} W$,
$$\Theta'_A(u, g) = \gamma\, \Theta_{W, V}\bigl(\operatorname{cone}(z + 1, v'),\, y\bigr)(g).$$
2. Let $e = -(z + 1) < 0$. The same holds with $\operatorname{cone}^\vee(z + 1, v')$ in place of $\operatorname{cone}(z + 1, v')$.

Lean: `New.Exchange.exists_planeConstantTerm_eq_thetaLarge_cone`, `New.Exchange.exists_planeConstantTerm_eq_thetaLarge_dualCone` (Lib/SiegelWeil/Tower/LargeSideConstantTerm.lean).

*Proof.* In case 1 take $x = z + 1 \ge 1$ in the proposition, side true, so $e + 1 = x$. In case 2 take $x = z + 1$, side false, so $e + 1 = -z = 1 - x$. Then $\gamma = \varepsilon_\beta |\alpha_0|^{z+1} \prod_{w \in S} q_w^{z + 1/2} L^S(z + 1, \nu)$, and its modulus is $C_\beta |\alpha_0|^{z+1} L^\sharp(z + 1)$. $\square$

In both cases $L$ occurs only at the point $z + 1 \ge 1$. In case 2 the constant term is $\mathcal{Z}$ at a point $1 - x \le 0$, but the proposition expresses $\mathcal{Z}(1 - x)$ by the dual cone and $L^S(x, \nu)$. Poisson's formula is applied before the integral is evaluated. So the functional equation of $L$ is not needed here. In case 2 the condition $\operatorname{rk} V = \operatorname{rk} W$ cannot hold, so only $u = 1$ occurs.

The squares of the constants of successive planes multiply as in the recursion for $L_*$. If $e$ grows by one at each step, the constants of the steps from $e = 0$ to $e = z$ contribute $L^\sharp(1)^2 \cdots L^\sharp(z + 1)^2 = L_*(z + 1)$, up to the constants $C$. The source uses `New.Exchange.lValueProdInt_succ` in this way in `New/Determinant/Exchange/RemovingPlanes.lean`.

**Remark (Formalization).** The constants $C$, $C_\beta$ and $c$ come from existence statements and are not computed. They do not depend on the character. Only the modulus of $\gamma$ is given. The theorem is proved only for standard data with the vacuum off $S$ and for a split tame character. The source cites S. Rallis, *On the Howe duality conjecture*, Compositio Math. 51 (1984), Theorem I.1.1, and C. Wu, *Irreducibility of theta lifting for unitary groups*, J. Number Theory 133 (2013), Proposition 3.1. In those results the lifted form is cuspidal and the isotropic orbit gives nothing. Here the lifted object is a character of $[U(1)]$, the data are ramified, and the isotropic orbit gives the Tate integral. The function `lSharp` is defined with the Euler product at every real $z$; for $z < 1$ this value is not the analytic continuation, and the source does not use it there.
