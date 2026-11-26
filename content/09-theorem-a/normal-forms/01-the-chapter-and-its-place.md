---
title: The chapter and its place
lean:
  - New/Derivatives/Divisibility/Count.lean
  - New/Derivatives/Vacuum/Divisibility.lean
decls:
  - New.Parameters.norm_jet_minorProd_le_of_hasNormalForm
  - New.Parameters.norm_jet_jetSeries_le_pow
  - New.Parameters.norm_jet_minorProd_jetSeries_le
  - New.Parameters.norm_schurJet_jetSeries_le_of_charges
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

The divisibility half of Theorem A asks how often a prime $p$ divides the derivatives of a theta function at the origin. This chapter gives the answer that the later chapters use. The theta functions are those of *standard data*, the $p$-integral combinations of translates of the integral vacuum built in [the integral vacuum and tight frames](/chapter/integral-vacuum/). The derivatives are taken along products of minors and along entries of Schur matrices. The answer has two parts. At every prime the derivatives are integral after a fixed scaling. At a prime that does not split in $K$ they are divisible by a predicted power of $p$, up to a loss that grows only with the logarithm of the degree.

The plan of Theorem A is in [Theorem A and its plan](/chapter/theorem-a-plan/). The normal form, which is the main input of the count, is in [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/). The chapters that use the results of this one are [theta kernels and gauges](/chapter/theta-kernels-gauges/), [short columns and the gain](/chapter/short-columns-gain/), [the chain valuation](/chapter/chain-valuation/) and [divisibility prime by prime](/chapter/divisibility/).

### The setting

We keep the notation of [the integral vacuum and tight frames](/chapter/integral-vacuum/). The field is $K = \mathbb{Q}(\sqrt{-d})$ with $d \equiv 7 \pmod 8$ prime, and $E = K(\zeta)$ with $\zeta$ of order $q_1$. The set $\Phi$ of infinite places of $E$ has $f = \varphi(q_1)$ elements. A prime $p$ comes with a ring homomorphism $\iota_p \colon \mathbb{C} \to \mathbb{C}_p$. We write $\mathcal{O}$ for the valuation ring of $\mathbb{C}_p$, $v$ for its valuation with $v(p) = 1$, and we call an element of $\mathbb{C}_p$ *integral* if it lies in $\mathcal{O}$. The source writes every lower bound for a valuation as an upper bound for a norm: $v(x) \ge c$ is $\|x\| \le p^{-c}$.

For a polynomial $Q$ and a power series $F$ in the same variables, the *jet* is the number

$$\mathrm{jet}(Q)(F) = (Q(\partial) F)(0) = \sum_\alpha Q_\alpha\, \alpha!\, F_\alpha,$$

where $Q_\alpha$ and $F_\alpha$ are the coefficients of $X^\alpha$ and $\alpha! = \prod_x \alpha_x!$. The factor $\alpha!$ is the reason why divisibility is a question at all: an integral series can have jets that are far more divisible than its coefficients.

The theta function of a vector $f$ of the Weil model, written in Fock's coordinates and scaled by $a$, has a Taylor series $J_a f$ at the origin ([the integral vacuum and tight frames](/chapter/integral-vacuum/)). Its variables are $z_{\tau,i}$ for a place $\tau$ and a coordinate $i$. The scale that makes everything integral is $\mathrm{jetScale} = \mathrm{periodFactor} \cdot \mathrm{areaScale}/\Omega_0$, with $|\mathrm{jetScale}|^2 = \Omega_E^{-1}$.

The numbers attached to $p$ are those of [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/): $v(\pi_p)$ is $1/2$ if $p = d$ and $1$ otherwise; $\rho_p = v(\pi_p)/(q_p - 1)$, where $q_p$ is the norm of a prime of $K$ above $p$; and

$$\gamma_p = \frac{1}{p-1} - \rho_p,$$

which is $p/(p^2-1)$ if $p$ is inert and $1/(2d-2)$ if $p = d$. The set $I_p^\circ$ consists of the odd $e \ge 0$ if $p$ is inert and of all $e \ge 0$ if $p = d$, and $I_p$ is the set of its positive elements. The *partner* of a place $\tau$ at the exponent $e$ is $\tau' = -p^e\tau$, the place $\tau$ moved by the class of $-p^e$ in $\mathrm{Gal}(E/K) \cong (\mathbb{Z}/q_1)^\times$.

### The three statements

The chapter proves three results about standard data. Here is the form in which they are used.

**Integrality.** Let $f$ be standard data of level $\delta \ne 0$ on a standard space, and $Q$ a homogeneous polynomial of degree $l$ with $p$-integral coefficients. Then the jet of $J_{c \cdot \mathrm{jetScale}} f$ along $Q$ has valuation at least $l \cdot v(c/(\bar\delta d))$, for every $c \in \mathbb{C}$. It is proved in Section 8.

Lean: `New.Parameters.norm_jet_jetSeries_le_pow` (New/Derivatives/Vacuum/Divisibility.lean).

**The count.** Let $p$ be non-split and let $f$ be standard data of level one on the space of $n' \times n$ matrices, and let $c \in \mathbb{C}$ be $p$-integral. Fix diagrams with $\kappa_\tau(h)$ columns of height $h$ at each place $\tau$, a standard filling $i'$ of them by rows, and integral matrices $y_\tau$. Let $P_y$ be the product, over all columns of height $h < N = |n'|$, of the minor of $z_\tau y_\tau$ on the rows of the column and the first $h$ columns. Then

$$v\big(\mathrm{jet}(P_y)(J_{c\cdot\mathrm{jetScale}} f)\big) \ge D_p(\kappa) - f N^3\big(1 + \log_p \max(B, 1)\big),$$

where $B$ is the number of boxes in the columns of height below $N$ and $D_p(\kappa)$ is the predicted divisibility of Section 4. For series with the normal form the bound is the count of Section 4.

Lean: `New.Parameters.norm_jet_minorProd_jetSeries_le` (New/Derivatives/Vacuum/Divisibility.lean); for series with the normal form, `New.Parameters.norm_jet_minorProd_le_of_hasNormalForm` (New/Derivatives/Divisibility/Count.lean).

**Schur entries with charges.** The same bound holds for the entries of the Schur matrices, after the columns of height one at a set of marked places are removed and the rows carry powers of $p$ that pay for them (Section 8).

Lean: `New.Parameters.norm_schurJet_jetSeries_le_of_charges` (New/Derivatives/Vacuum/Divisibility.lean).

### The model case

Take $p$ inert in $K$. Then $v(\pi_p) = 1$, $\rho_p = 1/(p^2-1)$ and $\gamma_p = p/(p^2-1)$. Let $N \ge 2$, and take a single column of height one at one place $\tau$ and nothing elsewhere, so that $B = 1$ and $P_y$ is one linear form $\sum_a y_a z_{\tau,b,a}$. Section 4 shows that the predicted divisibility is

$$D_p = \sum_{e \text{ odd}} \frac{1}{p^e} = \frac{p}{p^2-1} = \gamma_p,$$

provided that no partner $-p^e\tau$ is equal to $\tau$. So the first derivative of the theta function of standard data is divisible by $p^{\gamma_p}$, up to the loss. The general count says that each box of a diagram gains $\gamma_p$, and that a box loses part of this gain when the partner places also carry columns. The loss term $fN^3(1 + \log_p \max(B,1))$ is large for one box, and the count is useful only when $B$ is large. This is the situation of the later chapters, where the gain grows linearly in $B$ and the loss only like $\log B$.

### Why the count is not obvious

The jet of an integral series along a homogeneous polynomial of degree $B$ has valuation at least about $B/(p-1)$, by Legendre's formula for the factorials $\alpha!$ (Section 2). If the theta series were integral, each box would gain $1/(p-1)$. It is not: the normal form says only that $F(\varpi z)$ is integral times an exponential, with $v(\varpi) = \rho_p$. Scaling back by $\varpi$ costs $\rho_p$ per box, which leaves $\gamma_p = 1/(p-1) - \rho_p$. The exponential is the second problem. It is $\exp(c_\varpi \Xi)$, with $\Xi$ a combination of the couplings $\Gamma_e = \sum z_{\tau}^{p^e} z_{\tau'}$ between a place and its partner, and it is integral only when $\pi_p$ divides the couplings. The count makes the couplings divisible by a linear change of variables, and pays for it with the determinants of the change. The total price is the *deduction*, and the predicted divisibility is $\gamma_p B$ less the deduction.

### The structure of the chapter

- Section 2 proves Legendre's bound for jets, defines products of minors and the new variables, and proves the chain rule.
- Section 3 changes the directions at each place so that the couplings with the partners become divisible by $\pi_p$, at the price of the deduction.
- Section 4 defines the predicted divisibility and proves the count, first with charges and then in its plain form.
- Section 5 replaces an entry of a Schur matrix by a product of minors.
- Section 6 relates the scale to the theta values and proves that jets of theta products are integral; it also proves that standard data are stable under the operators that keep them integral.
- Section 7 writes the theta series of standard data as a power of a theta product along a resolution of the identity, times an integral series.
- Section 8 proves the three statements above.
- Section 9 has exercises and notes.

All files of this chapter import only files of earlier chapters of Volume 9 and of Volumes 2 to 8. There is no forward import.
