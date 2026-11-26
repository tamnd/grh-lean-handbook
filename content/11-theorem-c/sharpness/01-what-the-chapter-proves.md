---
title: What the chapter proves
lean:
  - New/Derivatives/Sharpness/BoundAttained.lean
decls:
  - New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Volume 9 proves a lower bound for the divisibility of Taylor coefficients. At a prime $p$, every Taylor coefficient of a standard datum at the weights is divisible by a power of $p$ that is at least the forced divisibility $S_p$. That bound is in [divisibility prime by prime](/chapter/divisibility/). This chapter proves that the bound is sharp. At every prime $p$, some Taylor coefficient of an indicator datum has valuation at most $S_p + v(t)$, where $t \neq 0$ is one fixed number with small conjugates. The number $t$ does not depend on $p$.

The height argument of Theorem C needs both bounds. The lower bound makes a number divisible. The upper bound of this chapter says that the divisibility is not larger, so that a certain algebraic part is not too small. [Hecke values of character lifts](/chapter/hecke-values/) uses the main theorem of this chapter in this way. The overview is in [Theorem C and the height argument](/chapter/theorem-c-plan/).

### The setting

Let $P$ be parameters and $D$ admissible data for $P$. The field $K = \mathbb{Q}(\sqrt{-d})$ has the prime $d \equiv 7 \bmod 8$. The field $E = D.E$ is the extension of $K$ by the roots of unity of order $q_1$. The set $\Phi$ of infinite places of the CM type has $f = D.f$ elements. Each place $\tau$ has a weight $\kappa(\tau) = $ `D.weight τ`. The numbers $x$, $b$ are scales of the data, $m$ and $r$ are ranks, and $k = r + 1 - m$. The level $M = D.M$ is the product of two large primes, and $\pi_M = $ `D.piM` is an integer of $K$ of norm $M$. These objects are in [the data and their sizes](/chapter/data-and-sizes/).

For a prime $p$ we fix an embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$ (the class `PadicPlace p`). The valuation $v$ on $\mathbb{C}_p$ has $|x| = p^{-v(x)}$ and $v(p) = 1$.

The forced divisibility is the sum of local prime sums,

$$S_p = \sum_{\tau \in \Phi} s_p(\kappa(\tau), \tau), \qquad s_p(y, \sigma) = v(\pi_p)\sum_{e \in I_p}\Bigl(\frac{y}{p^e} - \kappa(-p^e\sigma)\Bigr)_+ .$$

Here $v(\pi_p)$ is $\frac12$ if $p = d$ and $1$ otherwise. The set $I_p$ is the set of odd $e \geq 1$ if $p$ is inert in $K$, the set of all $e \geq 1$ if $p = d$, and empty if $p$ splits. The place $-p^e\sigma$ is the partner of $\sigma$. The definition is in [Theorem A and its plan](/chapter/theorem-a-plan/) (`New.Data.localPrimeSum`). The sum $S_p$ is `New.Data.localPrimeSumTotal`. For a split prime, $S_p = 0$.

The space $\mathrm{Hom}(E, E^{12})$ of $12 \times 1$ matrices carries the adelic Heisenberg representation. For a modulus $\mathfrak{m}$ of $E$ and a class $y_0$ of matrices modulo $\mathfrak{m}$, the *indicator datum* is the vector whose part at infinity is the Gaussian, whose part at the places that divide $\mathfrak{m}$ is the indicator of $y_0$, and whose other parts are the vacuum (`New.Data.indicatorDatum`). Its rescaled Taylor series `New.Data.twelveTaylor` is a power series in variables $z_{\tau,b}$, for $\tau \in \Phi$ and $b < 12$. The constant `vacuumScale` makes the values of the vacuum integral. The integral vacuum and its constants are in [the integral vacuum](/chapter/integral-vacuum/).

### The main theorem

**Theorem (Sharpness).** Let $D$ be admissible data for $P$. Let $l : \Phi \to \mathbb{N}$ be degrees with $\kappa(\tau) \leq l(\tau) \leq \kappa(\tau) + x^{42}$ for every $\tau$. Then there is a complex number $t \neq 0$ with these properties:

1. $|\sigma(t)| \leq \exp(fmb/k)$ for every ring automorphism $\sigma$ of $\mathbb{C}$;
2. for every modulus $\mathfrak{m}$ of $E$ with ideal $(\pi_M)$, for every prime $p$ and every embedding $\iota_p$, there are an exponent $\gamma$ on the variables $z_{\tau,b}$ and a class $y_0$ modulo $\mathfrak{m}$ such that $\sum_{b < 12}\gamma(\tau, b) = l(\tau)$ for every $\tau$, and
$$p^{-S_p} \leq \Bigl|\iota_p\Bigl(\frac{\mathrm{vacuumScale}^{12}}{t}\prod_{\tau}l(\tau)!\;\mathrm{coeff}_\gamma\,\mathrm{twelveTaylor}(\mathrm{indicatorDatum}\,\mathfrak{m}\,y_0)\Bigr)\Bigr|.$$

Lean: `New.Data.exists_rpow_neg_localPrimeSumTotal_le_norm_coeff` (New/Derivatives/Sharpness/BoundAttained.lean).

In terms of valuations, the last line says $v\bigl(\mathrm{vacuumScale}^{12}\, l!\, c_\gamma\bigr) \leq S_p + v(t)$, where $l! = \prod_\tau l(\tau)!$ and $c_\gamma$ is the coefficient. The factor $l!$ turns the coefficient into a derivative. The proof is in [the indicator data and the bound](/chapter/sharpness/#indicator-data-and-the-bound).

**Remark (Formalization).** The number $t$ comes from an existence statement. In the proof it is $t = M^{12f}\prod_\tau B_\tau^2\, c_0$, where $B_\tau$ is a product of $\lceil 6b/k \rceil$ consecutive integers and $c_0$ is a nonzero value of the integral vacuum. The value $c_0$ comes from `New.exists_intVacuum_ne_zero`, so $t$ is not explicit. The quantifiers are in this order: $t$ first, then $\mathfrak{m}$, $p$ and $\iota_p$, then $\gamma$ and $y_0$. So one $t$ serves all primes, and $\gamma$ and $y_0$ may depend on $p$. The bound on $|\sigma(t)|$ is asked for every ring automorphism $\sigma$ of $\mathbb{C}$, not only for the embeddings of a number field.

**Remark (Formalization).** The degrees are asked to lie in $[\kappa(\tau), \kappa(\tau) + x^{42}]$. The register of findings lists this window together with the bound $\exp(x^{34})$ on the algebraic part in [hypotheses and sizes](/chapter/register-of-findings/) (F-095). The window enters this chapter at two points: $l(\tau) \leq 2b$, and $x^{42} \leq \lceil 6b/k \rceil$.

### The plan of the proof

The proof has four steps. Each step is one section of the chapter.

1. **One curve.** On the CM curve $\mathbb{C}/\Omega_0\mathcal{O}_K$ the ring $\mathfrak{o}[[y]]$ of integral power series in the coordinate $y$ is stable under derivatives. The source names the rate $\gamma_p$ after Katz. Here $\gamma_p$ is $0$ for split $p$, $p/(p^2 - 1)$ for inert $p$ and $1/(2p - 2)$ for $p = d$. Section 2 proves that this rate cannot be improved: for every $n$ some $g$ has $v(g^{(n)}(0)) \leq \gamma_p n$.
2. **Least valuations.** Let $w$ be a tight frame and $\Theta = \prod_i \theta(\mu_iz)^{c_i}$ the theta product along its linear forms. Section 3 defines the relation $\mathrm{val}_n(\nu) \leq r$. It says that some coefficient of degree $\nu$ in a product of $n$ copies of series $H\Theta$ has valuation at most $r$. Section 3 then proves two bounds on six copies: $\mathrm{val}_6(\nu) \leq \gamma_p|\nu| - v(\nu!)$ if one form has unit coefficients, and $\mathrm{val}_6(\nu) \leq 0$ at inert primes.
3. **Couplings.** At an inert prime the theta product has a normal form $\Theta(\varpi z) = W\exp(\kappa\Xi)$, with $|\kappa| > 1$ and a sum $\Xi$ of couplings $z_\tau^{p^e}z_{-p^e\tau}$. Section 4 shows that a product of couplings has a coefficient of valuation $-|j|$ on six copies.
4. **The cases and the reduction.** Sections 5 and 6 combine these bounds on twelve copies into $v(l!) + \mathrm{val}_{12}(l) \leq S_p + 2\sum_\tau v(B_\tau)$ for every prime. There are three cases: $p$ split, $p$ inert with $p > k$, and $p$ not split with $p \leq k$. Section 7 carries a bound on $\mathrm{val}_{12}$ to a Taylor coefficient of an indicator datum, by Fourier inversion.

### Why six and twelve copies

The theta function $\theta$ is not in $\mathfrak{o}[[y]]$. A product $\prod_c\theta(\delta_cz)$ is in $\mathfrak{o}[[y]]$ if $\sum_c\delta_c^2 = 0$ in $\mathbb{Z}_p$. Every $p$-adic integer is a sum of four squares, so $-1 = \sum_{i<4}a_i^2$. The vector $\delta = (1, a_0, a_1, a_2, a_3, 0)$ then has $\sum\delta_c^2 = 0$ and $\delta_0 = 1$. This is the source of the number six. The sixth entry is $0$, and the factor $\theta(0 \cdot z) = 1$ adds nothing.

On twelve copies, six copies carry one bound and six carry another. At an inert prime $p > k$, six copies carry the couplings and six copies have valuation at most $0$ in the remaining degree. At a non-split prime $p \leq k$, six copies carry the couplings of the near pairs and six copies carry the rate $\gamma_p$ in the remaining degree. At a split prime, six copies carry the rate $\gamma_p = 0$ and the other six are taken in degree $0$.

### What is new and what is background

The background is stated in one line with a link. The CM curve, $\mathfrak{o}[[y]]$, the integral group law and the formal parameter are in [CM elliptic curves](/chapter/cm-elliptic-curves/). The normal form, the couplings and the partners are in [the CM formal group](/chapter/cm-formal-group/). Tight frames, the integral vacuum and Fourier inversion are in [the integral vacuum](/chapter/integral-vacuum/). Near pairs, the loss products $B_\tau$ and the comparison with Legendre's formula are in [short columns gain](/chapter/short-columns-gain/), because Theorem A uses them too. The sparseness that makes near pairs disjoint is in [progression-free sets](/chapter/progression-free-sets/).

The five source files of this chapter are `OneCurve`, `LeastValuation`, `Couplings`, `Cases` and `BoundAttained` in the folder `New/Derivatives/Sharpness`. No file of this chapter imports a file of a later chapter of Volume 11.
