---
title: The series represents the period
lean:
  - New/Spanning/Unfolding/BesselFormula.lean
  - New/Spanning/Unfolding/SeriesPeriod.lean
decls:
  - New.Filling.Fits.exists_integral_pi_eq
  - New.Filling.Fits.besselChar
  - New.Filling.Fits.exists_besselFn_eq_integral
  - New.Filling.Fits.besselChar_eq_unipotentChar
  - New.Filling.Fits.exists_dotProduct_besselFn_eq_integral
  - New.Filling.Fits.integral_classCutoff_integral_mul
  - New.Filling.Fits.isCutoff_sum_classWeight
  - New.Filling.Fits.exists_integral_besselMeasure_eq_sum
  - New.Filling.Fits.exists_integral_poincareSeries_eq_period
  - New.Data.exists_poincareAt_eq_poincareMap_comp
  - New.Data.poincare_eq_poincareMap_comp
status: drafted
drafted_by: writer@claude-opus-5-5
---

## The series represents the period

Theorem B uses the map $\mathfrak p$ that sends a source form $\varphi$ to the form on $Y_0$ that represents its Bessel period ([Theorem B: the plan](/chapter/theorem-b-plan/#unfolding-and-bounds)). This section proves that, for one choice of a real point $g_0$ and a linear form $t$, this form is the Poincaré series of the Bessel function. So the moments of $\mathfrak p$ are the moments of the Poincaré map of [the previous sections](/chapter/poincare-series/#poincar-series-and-the-petersson-formula).

The proof has three steps. First, the tensor product of the local Bessel functions is one integral over $R(F_\infty)$, with $R = U \rtimes H$ the Bessel group of $Y$. Second, the pairing of the series with a form $y$ unfolds to a sum over the classes of integrals over $U_c\backslash R(F_\infty)$. Third, the period is the same sum, because $[R]/J'$ is the disjoint union of the $U_c\backslash R(F_\infty)$, with $J' = R(\mathbb A_f) \cap J$.

### The Bessel function as one integral

Each local Bessel function is an average over the local Bessel group $\mathsf R_v$ ([Bessel functions as averages](/chapter/bessel-real-place/#bessel-functions-as-averages)). The group $R(F_\infty)$ is the product of the $\mathsf R_v$, through the isomorphism of topological groups `New.Filling.Fits.besselRealEquiv`.

**Lemma (Haar measures).** There is a real $c$ with $\int F\,d\bigl(\prod_v\mu_v\bigr) = c\int_{R(F_\infty)}F(\iota s)\,ds$ for all $F$, where $\mu_v$ is the Haar measure $du\,dh$ on $\mathsf R_v$ and $\iota$ is the isomorphism.
Lean: `New.Filling.Fits.exists_integral_pi_eq` (New/Spanning/Unfolding/BesselFormula.lean).

*Proof.* The product measure and the image of the Haar measure of $R(F_\infty)$ are both left Haar measures on $\prod_v\mathsf R_v$. So they differ by the Haar scalar factor $c$. $\square$

**Definition.** $\mathrm{bc}(r) = \psi_E\bigl(-(M\varpi)^{-1}\sigma(r)\bigr)$, with $\psi_E$ the standard additive character and $\sigma(r)$ the sum of the entries of $r$ at the simple roots.
Lean: `New.Filling.Fits.besselChar` (New/Spanning/Unfolding/BesselFormula.lean).

**Theorem (The Bessel function as one integral).** There are $g \in G(F_\infty)$ and a linear form $t$ on the Weyl module with
$$
\langle\zeta, W(y)\rangle = \int_{R(F_\infty)}\overline{e(g^{-1}sy)}\;\mathrm{bc}(s)^{-1}\;t(\check a\,\zeta)\,ds
$$
for all $y$ and $\zeta$. Here $W$ is the full, uncut Bessel function, $e$ is the kernel of the type, $s = na$ with $a$ the $H$ part of $s$, and $\zeta$ is carried to the dual of the values of $W$ by a fixed isomorphism.
Lean: `New.Filling.Fits.exists_besselFn_eq_integral` (New/Spanning/Unfolding/BesselFormula.lean).

*Proof.* At each place $v$ choose $a_v$, $x_v$ and $u_v$ with $W_v = a_v\int_{\mathsf R_v}\beta_v$, where $\beta_v(r, h) = d_{\lambda_v}(x_v^{-1}ry)\,\mathrm{wave}(-\sigma(r))\,\rho(h)^{-1}u_v$ is integrable. Take $g$ with components $x_v$, and $w = \bigotimes_v u_v$. A dot product with a tensor product of integrals is one integral over the product (`New.dotProduct_prod_integral`). The Haar lemma moves it to $R(F_\infty)$. At $s$ the product of the integrands is the product of the coefficients $d_{\lambda_v}$, times $\mathrm{bc}(s)^{-1}$ (the product of the waves), times the Kronecker product of the $\rho(a_v)^{-1}$ applied to $w$. The product of the coefficients is $\overline{e(g^{-1}sy)}$ divided by the product of the formal degrees, which is not $0$. Put $C = (\prod_va_v)\,c/\prod_v d(\lambda_v)$ and $t(\xi) = C\,\langle\xi, w\rangle$. $\square$

**Remark (Formalization).** The point $g$ and the form $t$ come from an existence statement. The constants $a_v$, the formal degrees and the Haar factor $c$ are absorbed in $t$, so $t$ is known only up to these constants. Theorem B needs only that some $g$ and $t$ exist.

### The character and the unfolding

**Lemma (The character extends $\psi_U$).** Let $\jmath\,c_Y = -(M\varpi)^{-1}$, with $\jmath$ the purely imaginary element of the Weil data and $c_Y$ the constant of the generic character $\psi_U$. Then $\mathrm{bc}(u) = \psi_U(u)$ for $u \in U(\mathbb A)$.
Lean: `New.Filling.Fits.besselChar_eq_unipotentChar` (New/Spanning/Unfolding/SeriesPeriod.lean).

*Proof.* For $u$ in the Bessel group, the trace that defines $\psi_U(u)$ is $c_Y(\sigma - \bar\sigma)$. The standard character at $z$ depends only on $(z + \bar z)/2$. Take $z = \jmath c_Y\sigma$. Since $\bar\jmath = -\jmath$ and $\bar c_Y = c_Y$, we have $\tfrac12(z + \bar z) = \tfrac{\jmath}{2}c_Y(\sigma - \bar\sigma)$. The hypothesis gives $z = -(M\varpi)^{-1}\sigma$. $\square$

With this hypothesis the source function $\mathcal W(ua) = \psi_U(u)\,t(\check a_\infty^{-1}\psi(a_f))$ is $\mathrm{bc}$ times the coefficient of $\psi$ at the $H$ part. Invert $s$ in the last theorem, which is allowed as $R(F_\infty)$ is unimodular.

**Corollary.** There are $g_0$ and $t$ such that for every algebraic form $\psi$, class $c$ and $x \in G(F_\infty)$,
$$
\langle\psi(c.\mathrm{out}), W(x)\rangle = \int_{R(F_\infty)}\overline{e(g_0^{-1}s^{-1}x)}\;\mathcal W(s, h_c)\,ds,
$$
with $\mathcal W$ the source function of the translate of $\psi$ by $\eta$.
Lean: `New.Filling.Fits.exists_dotProduct_besselFn_eq_integral` (New/Spanning/Unfolding/SeriesPeriod.lean).

**Lemma (Moving the quotient).** Let $y$ be a form of type $e$ and level $J$. Let $W$ on $R(F_\infty)$ be measurable, left invariant under $U_c$ and integrable against $\beta_c$. Then
$$
\int_{G(F_\infty)}\beta_c(x)\Bigl(\int_{R(F_\infty)}e(g_0^{-1}s^{-1}x)W(s)\,ds\Bigr)y(x, h_c)\,dx = \int_{R(F_\infty)}\beta_c(s)\,W(s)\,y(sg_0, h_c)\,ds.
$$
Lean: `New.Filling.Fits.integral_classCutoff_integral_mul` (New/Spanning/Unfolding/SeriesPeriod.lean).

*Proof.* Everything converges, since $y$ is bounded, $e$ is integrable and $W$ is integrable against $\beta_c$. Put $F(s, x) = W(s)\,e(g_0^{-1}s^{-1}x)\,y(x, h_c)$. It is invariant when $u \in U_c$ acts on both $s$ and $x$, because $y$ is invariant under $U_c$ at $h_c$ up to an element of $J$. So the cutoff can move from $x$ to $s$ (`New.integral_cutoff_swap`, see [unfolding](/chapter/reduction-theory/#unfolding)). Then the kernel $e$ reproduces $y$: $\int e(g_0^{-1}s^{-1}x)\,y(x, h_c)\,dx = y(sg_0, h_c)$. $\square$

### The period as a sum over classes

Let $\omega_c(r) = \beta_c(r_\infty)$ if $h_c^{-1}r_f \in J$, and $0$ otherwise.

**Lemma (Cutoff on $R(\mathbb A)$).** $\sum_c\omega_c$ is a cutoff for the action of $R(F)$ on $R(\mathbb A)$: it is measurable and it sums to $1$ over each orbit.
Lean: `New.Filling.Fits.isCutoff_sum_classWeight` (New/Spanning/Unfolding/SeriesPeriod.lean).

*Proof.* Write $r = na$ and $a_f\eta = \delta c k$ with $\delta$ rational, $c$ a class and $k$ in the level of the source forms. Approximate $n$ by a rational unipotent. This gives $\gamma \in R(F)$ with $\gamma r \in G(F_\infty) \times h_dJ$ for one class $d$. An element of $R(F)$ that keeps a point of $G(F_\infty) \times h_dJ$ in some $G(F_\infty) \times h_{d'}J$ has $d' = d$ and lies in $U_d$. So the orbit sum is $\sum_{u\in U_d}\beta_d(ur_\infty) = 1$. $\square$

**Theorem (Disjoint union).** There is $\mathrm{vol}_{J'} \neq 0$ such that, for every measurable $F$ on $R(\mathbb A)$ that is left invariant under $R(F)$, right invariant under $J'$ and integrable over $[R]$, each $s \mapsto \beta_c(s)F(s, h_c)$ is integrable and
$$
\int_{[R]}F = \mathrm{vol}_{J'}\sum_c\int_{R(F_\infty)}\beta_c(s)\,F(s, h_c)\,ds.
$$
Lean: `New.Filling.Fits.exists_integral_besselMeasure_eq_sum` (New/Spanning/Unfolding/SeriesPeriod.lean).

*Proof.* Compute $\int_{[R]}F$ with the cutoff $\sum_c\omega_c$. The term of $c$ lives on $R(F_\infty) \times h_cJ'$. There $F$ depends only on the real point, by the right invariance. So the finite integral gives the volume of $J'$, which is positive since $J'$ is open and compact. $\square$

**Theorem (Series and period).** Let $S$ be admissible and let $\jmath c_Y = -(M\varpi)^{-1}$. There are $g_0$ and $t$ such that for every source form $\psi$ and every form $y$ of the conjugate type and level $J$,
$$
\int_{[G]}y\cdot\mathcal P\psi = \int_{[R]}\mathcal W(r)\,y(rg_0)\,dr.
$$
Lean: `New.Filling.Fits.exists_integral_poincareSeries_eq_period` (New/Spanning/Unfolding/SeriesPeriod.lean).

*Proof.* Take $g_0$ and $t$ from the corollary, and replace $t$ by $(\mathrm{vol}_J/\mathrm{vol}_{J'})\,t$. The function $\mathcal W$ is continuous, invariant under $R(F)$ on the left and under $J'$ on the right. It is integrable over $[R]$, which is compact (`New.Grading.isCocompact_ratBessel`). By the Petersson unfolding of [the Poincaré series section](/chapter/poincare-series/#poincar-series-and-the-petersson-formula), $\int y\cdot\mathcal P\psi = \mathrm{vol}_J\sum_c\int\beta_c(x)\langle\psi(c.\mathrm{out}), W(x)\rangle y(x, h_c)\,dx$. Insert the corollary. The lemma on moving the quotient applies, because $\mathcal W(s, h_c)$ is invariant under $U_c$: a rational $u \in U_c$ moves $(s, h_c)$ to $(us, h_c)k$ with $k \in J$. This gives $\mathrm{vol}_J\sum_c\int\beta_c(s)\mathcal W(s, h_c)y(sg_0, h_c)\,ds$. The disjoint union theorem, applied to $F(r) = \mathcal W(r)y(rg_0)$, turns this into $(\mathrm{vol}_J/\mathrm{vol}_{J'})\int_{[R]}F$. $\square$

### The Poincaré map of the data

**Theorem.** For the data $D$ there are $g$ and $t$ with $\mathfrak p_{g,t} = \mathcal P\circ\mathrm{coords}$, where $\mathfrak p_{g,t}\varphi$ is the form that represents the Bessel period of $\varphi$ and $\mathrm{coords}$ gives the values of the central translate of $\varphi$ at the class representatives.
Lean: `New.Data.exists_poincareAt_eq_poincareMap_comp` (New/Spanning/Unfolding/SeriesPeriod.lean).

*Proof.* For the data, $\jmath c_Y = -(M\varpi)^{-1}$ holds by the definitions of the grading, the filling data and $M$. The filling data are admissible by [the last section](/chapter/poincare-series/#the-data-are-admissible). Two forms are equal if they have the same inner product with every $y$. The inner product of $y$ with $\mathfrak p_{g,t}\varphi$ is the period $\int_{[R]}\mathcal W\,\bar y(\cdot\,g)$. Apply the last theorem to $\psi$, the translate of $\varphi$ by the lattice scale, and to $\bar y$. Translating back by the inverse gives $\varphi$. The left side is the inner product of $y$ with $\mathcal P(\mathrm{coords}\,\varphi)$. $\square$

The map $D.\mathrm{poincare}$ is $\mathfrak p_{g,t}$ at the chosen point `New.Data.besselPoint` and the chosen form `New.Data.besselForm`.

**Corollary.** $D.\mathrm{poincare} = \mathcal P\circ\mathrm{coords}$.
Lean: `New.Data.poincare_eq_poincareMap_comp` (New/Spanning/Unfolding/SeriesPeriod.lean).

[Moments of the Poincaré map](/chapter/moments/) and [the proof of Theorem B](/chapter/proof-of-theorem-b/) use this corollary.

**Remark (Formalization).** The general theorem has the hypothesis $\jmath c_Y = -(M\varpi)^{-1}$. The register of findings lists it as F-080, open ([hypotheses and sizes](/chapter/register-of-findings/#hypotheses-and-sizes)). For the data it is proved inside `New.Data.exists_poincareAt_eq_poincareMap_comp`, at [SeriesPeriod.lean](lean:New/Spanning/Unfolding/SeriesPeriod.lean#L698). So the hypothesis does not remain in the statement for $D$. The point `New.Data.besselPoint` and the form `New.Data.besselForm` are chosen with `Exists.choose`. Their values are not given, only the identity of the corollary.
