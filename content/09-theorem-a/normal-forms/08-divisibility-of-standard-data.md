---
title: Integrality and divisibility of standard data
lean:
  - New/Derivatives/Vacuum/Divisibility.lean
decls:
  - New.Parameters.norm_jet_jetSeries_le_one
  - New.Parameters.norm_jet_jetSeries_le_pow
  - New.Parameters.isIntegralAbove_of_finiteImage_mem
  - New.Parameters.exists_hasNormalForm_jetSeries
  - New.Parameters.norm_jet_minorProd_jetSeries_le
  - New.Parameters.norm_schurJet_jetSeries_le_of_charges
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Integrality and divisibility of standard data

This section proves the three statements of Section 1. Integrality holds at every prime and for every level $\delta \ne 0$; it combines Section 7 with the integral jets of Section 6. Divisibility holds at the non-split primes and for level one; it combines Section 7 with the normal form and the count of Section 4.

Throughout, $V$ is a standard space over $E$ (all signs $+1$, the identity as adelic point), and $\iota_p \colon \mathbb{C} \to \mathbb{C}_p$ is fixed. A complex number $c$ is *$p$-integral* if $\iota_p(c)$ is integral.

### Integrality at every prime

**Lemma (Integral jets at the natural scale).** Let $\delta \ne 0$ and $f \in \mathrm{Std}_\delta(V)$. For every polynomial $Q$ with $p$-integral coefficients,

$$\big\|\iota_p\big(\mathrm{jet}(Q)\big(J_{\bar\delta\, d\, \mathrm{jetScale}} f\big)\big)\big\| \le 1.$$

Lean: `New.Parameters.norm_jet_jetSeries_le_one` (New/Derivatives/Vacuum/Divisibility.lean).

*Proof.* Multiplication by $\delta$ on the CM curve is an isogeny of some degree $N$, and comparing areas gives $\delta\bar\delta = N$. Section 7 gives a resolution $(u_j, m_j)$ with $\alpha^{-1}u_j$ integral above $p$ and $H \in \mathcal{M}(u^\dagger)$ with

$$J_{\bar\delta\,\mathrm{areaScale}/\Omega_0} f = (\Theta_{u^\dagger}^m)^N H.$$

Now $\bar\delta\, d\,\mathrm{jetScale} = a \cdot \bar\delta\,\mathrm{areaScale}/\Omega_0$ with $a = d \cdot \mathrm{periodFactor}$. Scale the variables by $\iota_p(a)$. The forms $u_j^\dagger z$ become $d\,\nu_j$ with $\nu_j = \iota_p(\mathrm{periodFactor})\, u_j^\dagger$, and these are integral by Section 6. The scaled $H$ lies in $\mathcal{M}(d\nu)$. So the series is $(\Theta_{d\nu}^m)^N H'$, and the theorem on integral jets of theta products applies. $\square$

**Theorem (Integrality at all primes).** Let $\delta \ne 0$, $f \in \mathrm{Std}_\delta(V)$, $c \in \mathbb{C}$, and $Q$ homogeneous of degree $l$ with $p$-integral coefficients. Then

$$\big\|\iota_p\big(\mathrm{jet}(Q)(J_{c\,\mathrm{jetScale}} f)\big)\big\| \le \Big\|\iota_p\Big(\frac{c}{\bar\delta d}\Big)\Big\|^l.$$

In valuations: $v(\mathrm{jet}(Q)(J_{c\,\mathrm{jetScale}} f)) \ge l \cdot v(c/(\bar\delta d))$.

Lean: `New.Parameters.norm_jet_jetSeries_le_pow` (New/Derivatives/Vacuum/Divisibility.lean).

*Proof.* Write $c\,\mathrm{jetScale} = (c/(\bar\delta d)) \cdot \bar\delta d\,\mathrm{jetScale}$. By the lemma on rescaled jets of Section 6 the jet is $(c/(\bar\delta d))^l$ times the jet at the natural scale, which is integral by the previous lemma. $\square$

**Remark (Formalization).** The factor $d$ in the natural scale comes from the jet ring of Section 6: the forms must be $d$ times integral forms so that the derivatives of $g'(\mu z)$ stay in the ring. The bound holds at every prime $p$, including the split primes and the primes dividing $q_1$. The statement uses `star` for the complex conjugate $\bar\delta$.

### The normal form at a non-split prime

**Lemma (Integrality without the idele).** Let $p \nmid q_1$ and let $y$ be a vector over $E$ with $\alpha^{-1}y$ integral above $p$. Then $y$ is integral above $p$.

Lean: `New.Parameters.isIntegralAbove_of_finiteImage_mem` (New/Derivatives/Vacuum/Divisibility.lean).

*Proof.* The adele $q_1\alpha$ is integral at every place. Above $p$ the number $q_1$ is a unit, so $\alpha$ is integral there, and $y = \alpha \cdot \alpha^{-1}y$. $\square$

**Theorem (Normal form of standard data).** Let $p$ be non-split, $f \in \mathrm{Std}_1(V)$, and $c$ $p$-integral. There are $\varpi \in \mathbb{C}_p$ with $v(\varpi) = \rho_p$ and integral coefficients $l$ such that $J_{c\,\mathrm{jetScale}} f$, read in $\mathbb{C}_p$, has the normal form for the exponents of $I_p^\circ$ and the partners $-p^e\tau$.

Lean: `New.Parameters.exists_hasNormalForm_jetSeries` (New/Derivatives/Vacuum/Divisibility.lean).

*Proof.* A prime that divides $q_1$ splits in $K$ (`New.Parameters.chiK_eq_one_of_dvd`), so $p \nmid q_1$. [The CM curve, its formal group and the normal form](/chapter/cm-formal-group/) gives $\varpi$ and $l$ such that $\Theta_\nu^m H$ has the normal form for every resolution $(u, m)$ integral above $p$ and every $H \in \mathcal{M}(\nu)$, where $\nu = u^\dagger$ (`New.Parameters.exists_hasNormalForm`). Section 7 with $\delta = 1$, $N = 1$, gives a resolution with $\alpha^{-1}u_j$ integral above $p$, and so $u_j$ integral above $p$ by the previous lemma, and $H$ with $J_{\mathrm{areaScale}/\Omega_0} f = \Theta_\nu^m H$. Since $p \nmid q_1$, $\iota_p(\mathrm{periodFactor})$ is a unit (`New.Parameters.norm_iota_periodFactor_eq_one`), so $c \cdot \mathrm{periodFactor}$ is integral. The series $J_{c\,\mathrm{jetScale}} f$ is the rescaling of $\Theta_\nu^m H$ by this number. The normal form is kept under rescaling by an integral number, with new coefficients $l$ (`New.HasNormalForm.rescale`). $\square$

**Remark (Formalization).** The theorem asserts only that $\varpi$ and $l$ exist. The coefficients $l$ after the rescaling are not the coefficients of the theta product. The count does not depend on $l$, and only $v(\varpi) = \rho_p$ enters its bound.

### Divisibility at a non-split prime

Let $n$ and $n'$ be finite sets of coordinates, and consider the space $\mathrm{Hom}(\mathrm{Std}(n), \mathrm{Std}(n'))$ of $n' \times n$ matrices over $E$, with the variable $(\tau, b, a)$ for the entry $(b, a)$ of the matrix $z_\tau$. Let $N = |n'|$, let $\kappa$ be the numbers of columns, and $B$ the number of boxes of $\kappa$ in columns of height below $N$.

**Theorem (Divisibility along products of minors).** Let $p$ be non-split, $f$ standard data of level one on the space of $n' \times n$ matrices, $c$ $p$-integral, $i'$ a filling and $y$ integral. Then

$$v\big(\mathrm{jet}(P_y)(J_{c\,\mathrm{jetScale}} f)\big) \ge D_p(\kappa) - fN^3\big(1 + \log_p \max(B,1)\big).$$

Lean: `New.Parameters.norm_jet_minorProd_jetSeries_le` (New/Derivatives/Vacuum/Divisibility.lean).

*Proof.* The previous theorem gives the normal form, and the count of Section 4 applies. $\square$

**Theorem (Divisibility of Schur entries with charges).** Let $p$ be non-split, $f$ and $c$ as before, and let $\kappa$ fit the ranks: $|n| \le |n'|$ and no column has a height strictly between them. Fix a set of erased places and charge exponents $w$ for every $e \in I_p^\circ$. Then for all fillings $i'$ and $i$,

$$v\big(\mathrm{schurJet}_\kappa(J_{c\,\mathrm{jetScale}} f)_{i',i}\big) + m \ge D_p(\kappa^\circ) + \gamma_p\big(B - B(\kappa^\circ)\big) - fN^3\big(1 + \log_p \max(B,1)\big),$$

where $\kappa^\circ$ is $\kappa$ without the columns of height one at the erased places and $m$ is the filling charge of $i'$.

Lean: `New.Parameters.norm_schurJet_jetSeries_le_of_charges` (New/Derivatives/Vacuum/Divisibility.lean).

*Proof.* Take the normal form of the previous theorem. Section 5 gives integral $y$ with $v(\mathrm{schurJet}_\kappa(F)_{i',i}) \ge v(\mathrm{jet}(P_y)(F))$, for $F$ the series read in $\mathbb{C}_p$; the Schur matrix commutes with $\iota_p$ under `FitsRanks` (`New.map_schur`, in [integral Weyl modules and branching](/chapter/weyl-modules/)). The count with charges of Section 4 bounds the right side. $\square$

**Remark (Formalization).** The theorem for Schur entries assumes the condition on $w$ for all heights and places (`New.IsChargeExponent`). The count with charges needs it only for the heights that occur in $\kappa$, and the proof passes the stronger hypothesis to it. The level is one in both divisibility theorems; for a level $\delta \ne 0$ the source gives only the integrality theorem above.

### A check on the numbers

Take $p$ inert, $c = 1$, one column of height one at one place, and no partner of that place equal to it. Integrality gives $v \ge 1 \cdot v(1/d) = 0$, since $p$ inert does not divide $d$. The divisibility theorem gives $v \ge \gamma_p - fN^3(1 + 0) = p/(p^2-1) - fN^3$, which is negative and so adds nothing for a single box. For a diagram with $B$ boxes whose places and partners do not interact, the prediction is $\gamma_p B$, and the bound exceeds the integrality bound once $\gamma_p B > fN^3(1 + \log_p B)$.
