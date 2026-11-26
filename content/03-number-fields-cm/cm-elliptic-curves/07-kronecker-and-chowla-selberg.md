---
title: Kronecker's limit formula and Chowla-Selberg
lean:
  - Lib/CM/KroneckerLimit.lean
  - Lib/CM/ChowlaSelberg.lean
decls:
  - New.kronecker_limit
  - New.QuadField.eulerProd_one_eq_zeta_mul
  - New.hasSum_ideal_classes
  - New.CMLattice.riemannZeta₁_mul_entireL_eq_sum
  - New.CMLattice.sum_kronecker_terms
  - New.chowlaSelbergConst
  - New.QuadField.exists_mk_eq_and_prod_eq_one
  - New.CMLattice.exists_latticeModule_eq_scaledIdeal_mul
  - New.CMLattice.norm_prod_le_one
  - New.CMLattice.prod_norm_eq_one
  - New.CMLattice.prod_area_mul_norm_disc_galConjugate
  - New.CMLattice.chowla_selberg
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Kronecker's limit formula and Chowla-Selberg

This section gives the source form of the two classical formulas of Section 2: Kronecker's first limit formula and the formula of Chowla and Selberg. The source proves Kronecker's formula for every lattice, as a right derivative at $s = 1$ for real $s$. It sums the formula over the ideal classes of $K$ and gets the mean of $\log(A|\Delta|^{1/6})$ in terms of $L'/L(1, \chi_K)$. The good reduction of [Section 4](/decl/New.CMLattice.norm_disc_eq_one/) and the conjugate lattices of [Section 6](/decl/New.CMLattice.latticeModule_galConjugate_eq_mul/) then give one number $u$ that scales every conjugate lattice to the same area. The constant of this area is [the Chowla-Selberg constant](/chapter/weighted-prime-remainder/) of Volume 1. Volume 1 uses `New.CMLattice.sum_kronecker_terms` and `New.CMLattice.chowla_selberg`, which are stated here.

As before, $d$ is a prime with $d \equiv 7 \pmod 8$, $K = \mathbb{Q}(\sqrt{-d})$, and $\chi = \chi_K$ is the Legendre symbol $(\cdot/d)$. For a lattice $L$ write $A(L)$ for its area and $\Delta(L) = g_2^3 - 27g_3^2$ for its discriminant. For a CM lattice, $\Delta = a_1^4 - 64$ by [Section 3](/decl/New.CMLattice.disc_eq/).

### Kronecker's limit formula for real s

The classical form is in Section 2 (Siegel, *Lectures on Advanced Analytic Number Theory*, 1961, Chapter I, Theorem 1). The source uses the version with the area and the discriminant, which holds for every lattice, and adds a scale factor $k > 0$.

**Theorem (Kronecker's first limit formula).** Let $L$ be a lattice and $k > 0$. There is a function $F : \mathbb{R} \to \mathbb{R}$ such that:

1. $F(1) = \pi k$;
2. $F$ has the right derivative $F(1)\bigl(2\gamma - \log(A/(k\pi^2)) - \tfrac16\log|\Delta|\bigr)$ at $1$;
3. for $1 < s < 2$,
$$F(s) = (s - 1)\sum_{l \in L} \Bigl(\frac{|l|^2}{kA}\Bigr)^{-s}.$$

Lean: `New.kronecker_limit` (Lib/CM/KroneckerLimit.lean).

For $k = 1$ this is the expansion of Section 2,
$$\sum_{l \ne 0} \Bigl(\frac{|l|^2}{A}\Bigr)^{-s} = \frac{\pi}{s - 1} + \pi\Bigl(2\gamma - \log\frac{A\,|\Delta|^{1/6}}{\pi^2}\Bigr) + o(1), \qquad s \to 1^+.$$
For general $k$ the sum is $k^s$ times the sum for $k = 1$. The factor $k^s$ adds $\log k$ to the constant term, and this is the term $-\log(A/k)$ in (2).

*Proof.* Write $L = a(\mathbb{Z}\tau + \mathbb{Z})$ with $\tau = x + iy$, $y > 0$. Sum by rows. The row $m = 0$ is $2\zeta(2s)$. For $m \ge 1$, compare the row $\sum_n |m\tau + n|^{-2s}$ with the integral $\int |m\tau + t|^{-2s}\,dt$ (`New.hasSum_shiftedTerm`). The errors are bounded by the mean value theorem (`New.norm_rpow_sub_rpow_le`), so their sum is continuous on $[1, 2]$. The integrals sum to a multiple of $\zeta(2s - 1)$, which has a simple pole at $s = 1$. At $s = 1$ the cotangent series expresses the sum of the errors through $\log|\prod_n (1 - q^n)|$, $q = e^{2\pi i\tau}$ (`New.tsum_meanError_one`). The same product occurs in $\log|\Delta|$. $\square$

The source cites Siegel for the result, and F. Chamizo, *A simple evaluation of a theta value, the Kronecker limit formula and a formula of Ramanujan*, Ramanujan J. (2022), Proposition 3.1, for a proof of this shape.

**Remark (Formalization).** The Epstein zeta function is not continued analytically. Only real $s$ with $1 < s < 2$ occur, and the statement at $s = 1$ is a right derivative of $F$, not an expansion of a meromorphic function. The sum in (3) runs over all $l \in L$, including $l = 0$. In Lean, $0^{-s} = 0$ for real $s \ne 0$, so the term $l = 0$ is $0$. This is a junk value that happens to give the right sum. The Dedekind eta function does not occur. The discriminant is used in its place.

### The zeta function of K

**Theorem (Factorisation of the zeta function).** For real $s > 1$,
$$\prod_{\mathfrak{p}} \bigl(1 - N\mathfrak{p}^{-s}\bigr)^{-1} = \zeta(s)\, L(s, \chi).$$

Lean: `New.QuadField.eulerProd_one_eq_zeta_mul` (Lib/CM/ChowlaSelberg.lean).

*Proof.* Group the primes $\mathfrak{p}$ of $K$ by the rational prime $p$ below them. Only $d$ ramifies (`New.QuadField.eq_d_of_span_eq_sq`). If $p$ is inert, the factor of $K$ is $(1 - p^{-2s})^{-1}$ and $\chi(p) = -1$. If $p$ splits, there are two factors $(1 - p^{-s})^{-1}$ and $\chi(p) = 1$. If $p = d$, there is one factor $(1 - d^{-s})^{-1}$ and $\chi(d) = 0$. In each case the factor of $K$ at $p$ is $(1 - p^{-s})^{-1}(1 - \chi(p)p^{-s})^{-1}$. $\square$

This is the classical factorisation (Neukirch, *Algebraic Number Theory*, VII.5). In Lean, $\chi$ is `quadTwist (N := 1) 1 d`, the trivial character modulo $1$ twisted by the Legendre symbol, and $L(s, \chi)$ is `New.entireL` of it. Since $\chi$ is not principal, `New.entireL` is its $L$-function, an entire function. The proof is run under `seal Finset.prod`, which keeps definitional checks from unfolding the finite products. This has no effect on the statement.

**Theorem (Sum over the classes).** Let $E_c$ be CM lattices, one for each ideal class $c$, with $\Lambda(E_c) = u_c\mathfrak{a}_c$, where the ideals $\mathfrak{a}_c$ represent each class once. Let $k = 2/\sqrt d$, let $s > 1$ be real, and let $F_c$ be the sum of $(s - 1)(|l|^2/(kA(E_c)))^{-s}$ over $l \in \Lambda(E_c)$. Then
$$(s - 1)\zeta(s) \cdot \#\mathcal{O}_K^\times \cdot L(s, \chi) = \sum_c F_c.$$

Lean: `New.CMLattice.riemannZeta₁_mul_entireL_eq_sum` (Lib/CM/ChowlaSelberg.lean), with `New.hasSum_ideal_classes`.

*Proof.* The lattice $u\mathfrak{a}$ has the area $|u|^2N\mathfrak{a}\sqrt d/2$, by [the area formula](/decl/New.QuadField.area_eq_of_eq_scaledIdeal/). So for $y \in \mathfrak{a}$, $|uy|^2/(kA) = |N(y)|/N\mathfrak{a}$. The map $y \mapsto (y)\mathfrak{a}_c^{-1}$ takes $\mathfrak{a}_c \setminus \{0\}$ onto the integral ideals in the class of $\mathfrak{a}_c^{-1}$, and each ideal is hit $\#\mathcal{O}_K^\times$ times. The classes $\mathfrak{a}_c^{-1}$ run once through the class group. So $\sum_c F_c$ is $(s - 1)\#\mathcal{O}_K^\times\sum_I N(I)^{-s}$, which is $(s - 1)\#\mathcal{O}_K^\times\zeta_K(s)$. Apply the factorisation. $\square$

**Remark (Formalization).** In Lean the number of units is `Nat.card (𝓞 (QuadField d))ˣ`. The function `Nat.card` gives $0$ for an infinite type, so the lemma `New.hasSum_ideal_classes`, which is stated for every number field, would give $0$ for a field with infinitely many units. For $K = \mathbb{Q}(\sqrt{-d})$ the units are $\pm 1$. The number cancels in the next theorem, so its value is not needed. The factor $(s - 1)\zeta(s)$ is written `riemannZeta₁ s`. It is entire and has the value $1$ at $s = 1$.

### The constant term summed over the classes

**Theorem (Kronecker terms over the classes).** Let $E_c$ and $\mathfrak{a}_c$ be as above, and $h$ the class number. Then
$$\sum_c \Bigl(2\gamma - \log\frac{A(E_c)\sqrt d}{2\pi^2} - \frac16\log|a_1(E_c)^4 - 64|\Bigr) = h\,(2\gamma - C_d),$$
where $C_d = \gamma - \operatorname{Re}\, L'/L(1, \chi)$.

Lean: `New.CMLattice.sum_kronecker_terms` (Lib/CM/ChowlaSelberg.lean), with `New.chowlaSelbergConst` for $C_d$.

*Proof.* For each $c$, Kronecker's formula with $k = 2/\sqrt d$ gives a function $F_c$. On $(1, 2)$, the function $Z(s) = (s - 1)\zeta(s) \cdot \#\mathcal{O}_K^\times \cdot L(s, \chi)$ equals $\sum_c F_c(s)$, by the sum over the classes. The function $Z$ is differentiable at $1$. The values at $1$ give
$$\#\mathcal{O}_K^\times\, L(1, \chi) = h\pi k,$$
since $(s - 1)\zeta(s)$ is $1$ at $s = 1$. Its derivative at $1$ is $\gamma$. The right derivatives at $1$ give
$$\gamma\,\#\mathcal{O}_K^\times L(1, \chi) + \#\mathcal{O}_K^\times L'(1, \chi) = \pi k S,$$
with $S$ the left side of the claim. Divide by the first equation. Then $L'/L(1, \chi) = S/h - \gamma$, so $S = h(\gamma + L'/L(1, \chi)) = h(2\gamma - C_d)$. $\square$

**Example.** The first equation is the class number formula. With $\#\mathcal{O}_K^\times = 2$ and $k = 2/\sqrt d$ it reads $L(1, \chi) = \pi h/\sqrt d$. For $d = 7$, $h = 1$, and $L(1, \chi) = \pi/\sqrt 7 \approx 1.18741$. The source does not state this formula as a separate lemma. It occurs inside the proof.

**Remark (Formalization).** The constant $C_d$ is `New.chowlaSelbergConst d`, defined as $\gamma - \operatorname{Re}$ `logDeriv (entireL (quadTwist (N := 1) 1 d)) 1`. The real part is there for type reasons. $L(s, \chi)$ is real for real $s$, so the real part changes nothing. The statement has no Gamma values, and no Lerch formula. The evaluation of $C_d$ by Gamma values, which is the second equality of the classical theorem in Section 2, is not in this chapter. The proof uses `choose` to pick the functions $F_c$ of Kronecker's formula. The functions occur only in the proof, so the choice does not enter the statement.

### Ideals with product one

The last step needs CM lattices in every class that are related to one fixed lattice by isogenies whose ideals have product $(1)$.

**Lemma.** There are fractional ideals $\mathfrak{c}_{\mathcal{C}}$, one in each class $\mathcal{C}$, with $\prod_{\mathcal{C}} \mathfrak{c}_{\mathcal{C}} = (1)$.

Lean: `New.QuadField.exists_mk_eq_and_prod_eq_one` (Lib/CM/ChowlaSelberg.lean).

*Proof.* Choose $\mathfrak{b}_{\mathcal{C}}$ in each class $\mathcal{C}$, and put $\mathfrak{c}_{\mathcal{C}} = \mathfrak{b}_{\mathcal{C}^2}/\mathfrak{b}_{\mathcal{C}}$. It lies in the class $\mathcal{C}^2\mathcal{C}^{-1} = \mathcal{C}$. Squaring permutes the classes, by [the odd class number](/decl/New.QuadField.classGroup_sq_bijective/). So $\prod_{\mathcal{C}} \mathfrak{b}_{\mathcal{C}^2} = \prod_{\mathcal{C}} \mathfrak{b}_{\mathcal{C}}$, and the product of the $\mathfrak{c}_{\mathcal{C}}$ is $(1)$. $\square$

For each such ideal and each CM lattice $C$ there is a CM lattice $D$ and $\mu \in \mathbb{C}^\times$ with $\Lambda(D) = \mu\mathfrak{c}\Lambda(C)$ (`New.CMLattice.exists_latticeModule_eq_scaledIdeal_mul`). This follows from [the existence of CM lattices](/decl/New.QuadField.exists_cmLattice_latticeModule_eq_scaledIdeal/) in every class.

**Lemma (Product of isogeny factors).** Let $A_c$, $B_c$ be CM lattices with $\Lambda(B_c) = u_c\mathfrak{a}_c\Lambda(A_c)$, for $c$ in the class group, and let $\prod_c \mathfrak{a}_c = (1)$. Then for every prime $p$ and every embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$ in the sense of [Section 5](/decl/New.CMLattice.norm_le_one_of_mapsTo_lattice/),
$$\prod_c |\iota_p(u_c)| = 1.$$

Lean: `New.CMLattice.prod_norm_eq_one` (Lib/CM/ChowlaSelberg.lean), with `New.CMLattice.norm_prod_le_one`.

*Proof.* A number that maps one CM lattice into another is integral at $\iota_p$ (`New.CMLattice.norm_le_one_of_mapsTo_lattice`). So every element of $u_c\mathfrak{a}_c$ is integral, and so is every element of the product $\bigl(\prod_c u_c\bigr)\prod_c \mathfrak{a}_c$. This product contains $\prod_c u_c$, since $1 \in \prod_c \mathfrak{a}_c$. So $\prod_c |\iota_p(u_c)| \le 1$. The inverses $u_c^{-1}\mathfrak{a}_c^{-1}$ map $\Lambda(B_c)$ onto $\Lambda(A_c)$, and the same argument gives the inequality $\ge 1$. $\square$

### The formula of Chowla and Selberg

**Lemma (Conjugate products).** Let $C$ be a CM lattice, let $\Lambda(D_{\mathcal{C}}) = \mu_{\mathcal{C}}\mathfrak{c}_{\mathcal{C}}\Lambda(C)$ for CM lattices $D_{\mathcal{C}}$ with $\prod \mathfrak{c}_{\mathcal{C}} = (1)$, and let $u \in \mathbb{C}$ with
$$u^{12h} = \prod_{\mathcal{C}} \mu_{\mathcal{C}}^{12}\bigl(a_1(D_{\mathcal{C}})^4 - 64\bigr).$$
Then for every $\sigma \in \operatorname{Gal}(\mathbb{C}/K)$,
$$\prod_{\mathcal{C}} A(D_{\mathcal{C}}^\sigma)\,|\Delta(D_{\mathcal{C}}^\sigma)|^{1/6} = \bigl(A(C^\sigma)\,|\sigma(u)|^2\bigr)^h.$$

Lean: `New.CMLattice.prod_area_mul_norm_disc_galConjugate` (Lib/CM/ChowlaSelberg.lean).

*Proof.* By [the conjugate isogenies](/decl/New.CMLattice.latticeModule_galConjugate_eq_mul/), $\Lambda(D_{\mathcal{C}}^\sigma) = \sigma(\mu_{\mathcal{C}})\mathfrak{c}_{\mathcal{C}}\Lambda(C^\sigma)$. So $A(D_{\mathcal{C}}^\sigma) = |\sigma(\mu_{\mathcal{C}})|^2N\mathfrak{c}_{\mathcal{C}}A(C^\sigma)$. The norms $N\mathfrak{c}_{\mathcal{C}}$ have product $1$. The discriminant of $D_{\mathcal{C}}^\sigma$ is $\sigma$ of the discriminant of $D_{\mathcal{C}}$, since $a_1(D^\sigma) = \sigma(a_1(D))$. So $|\sigma(u)|^{12h} = \prod_{\mathcal{C}} |\sigma(\mu_{\mathcal{C}})|^{12}|\Delta(D_{\mathcal{C}}^\sigma)|$. Compare the sixth powers of both sides. $\square$

**Theorem (Chowla and Selberg, with a unit).** Let $C$ be a CM lattice for $d$. There is $u \in \mathbb{C}$ such that:

1. $|\iota_p(u)| = 1$ for every prime $p$ and every embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$;
2. for every $\sigma \in \operatorname{Gal}(\mathbb{C}/K)$,
$$A(C^\sigma)\,|\sigma(u)|^2 = \pi e^{C_d}\cdot\frac{2\pi}{\sqrt d}.$$

Lean: `New.CMLattice.chowla_selberg` (Lib/CM/ChowlaSelberg.lean).

The left side of (2) is the area of the lattice $\sigma(u)\Lambda(C^\sigma)$. So the theorem says that one number $u$, a unit at all finite places, scales all conjugates of $C$ to the same area, and the area is the right side of the classical formula.

*Proof.* Take ideals $\mathfrak{c}_{\mathcal{C}}$ with product $(1)$, one in each class, CM lattices $D_{\mathcal{C}}$ with $\Lambda(D_{\mathcal{C}}) = \mu_{\mathcal{C}}\mathfrak{c}_{\mathcal{C}}\Lambda(C)$, and a $12h$-th root $u$ of $\prod \mu_{\mathcal{C}}^{12}(a_1(D_{\mathcal{C}})^4 - 64)$. For (1), $\prod |\iota_p(\mu_{\mathcal{C}})| = 1$ by the product of isogeny factors, and $|\iota_p(a_1^4 - 64)| = 1$ by [good reduction](/decl/New.CMLattice.norm_disc_eq_one/). So $|\iota_p(u)|^{12h} = 1$. For (2), fix $\sigma$ and put $E_{\mathcal{C}} = D_{\mathcal{C}}^\sigma$. The lattice of $E_{\mathcal{C}}$ is $\sigma(\mu_{\mathcal{C}})\mathfrak{c}_{\mathcal{C}}\Lambda(C^\sigma)$, and $\Lambda(C^\sigma) = x\mathfrak{a}$ for some $x$ and $\mathfrak{a}$. The ideals $\mathfrak{c}_{\mathcal{C}}\mathfrak{a}$ represent each class once. So the Kronecker terms over the classes apply to the $E_{\mathcal{C}}$. With $B = A(C^\sigma)|\sigma(u)|^2$, the conjugate products give
$$\sum_{\mathcal{C}} \Bigl(\log A(E_{\mathcal{C}}) + \frac16\log|\Delta(E_{\mathcal{C}})|\Bigr) = h\log B.$$
Insert this into the Kronecker terms, and divide by $h$. Then $\log B = C_d + \log(2/\sqrt d) + 2\log\pi$, which is the claim. $B > 0$, since $u \ne 0$: the discriminants are not $0$. $\square$

**Example ($d = 7$).** Here $h = 1$, and there is one class. Take $\mathfrak{c} = (1)$, $D = C$ and $\mu = 1$. Then $u^{12} = a_1^4 - 64$. In [Section 4](/decl/New.CMLattice.norm_disc_eq_one/) we found $a_1^4 = 63$ for $d = 7$, so $\Delta = -1$ and $|u| = 1$. For $\sigma = 1$ the theorem gives $A(C) = 2\pi^2e^{C_7}/\sqrt 7$. This agrees with the classical form of Section 2, since $|\Delta(C)|^{1/6} = 1$, and the value is $13.08193$ to seven digits. The source takes the root $u$ that `exists_pow_nat_eq` chooses. Any two $12$-th roots of $-1$ differ by a $12$-th root of unity, which does not change $|u|$ or $|\sigma(u)|$.

**Remark (Formalization).** The statements of this section are exactly what the source proves, with these limits.

1. The number $u$ is a $12h$-th root chosen by `exists_pow_nat_eq` inside an existence statement. The source shows that $|\iota_p(u)| = 1$ for every $p$ and every embedding $\iota_p$. It does not show that $u$ is algebraic. A number with $|\iota(u)| = 1$ for all such $\iota$ would be algebraic, but the source does not derive this (see the remark in [Section 4](/decl/New.CMLattice.norm_disc_eq_one/)). The spec of the project lists this as finding F-064. It is not known from the spec whether the later volumes need $u$ algebraic.
2. In Volume 9 the unit is fixed by `choose`: `New.Parameters.chowlaSelbergUnit` is `P.cmCurve.chowla_selberg.choose`, in New/Derivatives/Vacuum/TightFrames.lean. Its two properties are `New.Parameters.norm_iota_chowlaSelbergUnit` and `New.Parameters.area_mul_norm_chowlaSelbergUnit_sq`. Nothing else is known about this number.
3. The constant is $C_d = \gamma - \operatorname{Re} L'/L(1, \chi)$. No Gamma values occur. The source cites Selberg and Chowla (J. reine angew. Math. 227, 1967) and B. Gross, *On the periods of abelian varieties*, arXiv 2005.04194, for the classical formula. The Lean statement is the formula with $L'/L(1, \chi)$, not the formula with Gamma values.
4. The conjugates $C^\sigma$ are the chosen lattices of `New.CMLattice.galConjugate`. Their lattices depend only on $\sigma(a_1)$, so the areas do not depend on the choice.
5. The proof uses Kronecker's formula only for real $s$, as stated above. The factor $\#\mathcal{O}_K^\times$ cancels. Its junk value for infinitely many units does not occur.
6. $\operatorname{Gal}(\mathbb{C}/K)$ is the group of all field automorphisms of $\mathbb{C}$ over $K$. The theorem holds for discontinuous $\sigma$, because all statements about $\sigma$ pass through Taylor coefficients and the numbers $a_1$, $\mu_{\mathcal{C}}$ and $u$.

The theorem does not use [class field theory](/chapter/class-field-theory/) or the Hecke character of the curve. The classical proof of Chowla and Selberg does not need them either. It uses only Kronecker's formula and the factorisation of $\zeta_K$. What the source adds is the unit $u$ and its conjugates, which come from good reduction and the conjugate isogenies of Section 6.
