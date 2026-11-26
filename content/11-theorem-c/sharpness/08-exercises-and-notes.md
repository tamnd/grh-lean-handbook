---
title: Exercises
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $p$ be inert in $K$ and $|\varpi| = p^{-\rho_p}$. Use [the scalar lemma](/decl/New.CMLattice.norm_pow_div_of_inert/), $|\varpi^{p+1}/p| = p^{1 - 1/(p-1)}$, to find $\rho_p$. Then show that $\gamma_p = 1/(p-1) - \rho_p$ equals $p/(p^2 - 1)$. Compute $\gamma_{13}$ and compare it with $1/(p-1)$, the rate of Legendre's bound $v(n!) \leq n/(p-1)$.

*Hint.* $-(p+1)\rho_p + 1 = 1 - 1/(p-1)$ gives $\rho_p = 1/(p^2 - 1)$. Then $\gamma_p = (p + 1 - 1)/(p^2 - 1)$. For $p = 13$, $\gamma_{13} = 13/168$ and $1/12 = 14/168$.

**Exercise 2.** Let $p$ be odd. Show that there are $a, b \in \mathbb{Z}_p$ with $1 + a^2 + b^2 = 0$. Deduce that three scaled copies $\theta(z)\theta(az)\theta(bz)$ give a series in $\mathfrak{o}[[y]]$, by [products of scaled theta](/decl/New.CMLattice.prod_rescale_theta_mem/). Which argument for the existence of $\delta$ with $\delta_0 = 1$ and $\sum_c\delta_c^2 = 0$ works for every prime, $p = 2$ included?

*Hint.* Modulo $p$ the sets $\{a^2\}$ and $\{-1 - b^2\}$ each have $(p+1)/2$ elements, so they meet. Not both $a$ and $b$ are $0$ modulo $p$, so one partial derivative $2a$ or $2b$ is a unit, and Hensel's lemma lifts the solution. For every prime, use [four squares](/decl/New.padicInt_sum_four_squares/) for $-1$.

**Exercise 3.** Prove Legendre's formula in one step, $v(n!) = \lfloor n/p\rfloor + v(\lfloor n/p\rfloor!)$. Deduce $v(n!) \leq n/(p-1)$.

*Hint.* The multiples of $p$ up to $n$ are $p, 2p, \dots, \lfloor n/p\rfloor p$, with the product $p^{\lfloor n/p\rfloor}\lfloor n/p\rfloor!$. The other factors of $n!$ are prime to $p$. For the bound, use induction and $\lfloor n/p\rfloor \leq n/p$.

**Exercise 4.** Let $n = n^\sharp$ and $B(l) = (l^- + 1)\cdots(l^- + n)$ with $l^- = (l - n)_+$. Show that $l! = (l - n)!\,B(l)$ for $l \geq n$, and that $l!$ divides $B(l) = n!$ for $l < n$. Deduce $v(l!) \leq v(l^-!) + v(B(l))$ in both cases.

*Hint.* For $l \geq n$ the factors of $B(l)$ are $l - n + 1, \dots, l$. For $l < n$, $l^- = 0$.

**Exercise 5.** In the case $p > k$ of Section 6, put $i_t = \lfloor(l_t - n^\sharp)_+/p\rfloor$. Show that $(l_t - n^\sharp)_+ + \min(n^\sharp, l_t) = l_t$. Explain why the coupling count $j(\tau) = \min(i_\tau, l_{-p\tau})$ needs both terms of the minimum. What would go wrong with $j(\tau) = \lfloor l_\tau/p\rfloor$?

*Hint.* The place $t = -p\tau$ carries $p\,j(t)$ from its own couplings and $j(\tau)$ from the couplings that end at $t$. The bound $j(\tau) \leq i_\tau \leq n^\sharp$ uses [the quotient lemma](/decl/New.Data.div_le_lossFactorCount/), and $j(\tau) \leq l_t$ is the second term. With $\lfloor l_\tau/p\rfloor$, the place $t$ could receive $p\lfloor l_t/p\rfloor + \lfloor l_\tau/p\rfloor > l_t$.

**Exercise 6.** The sum $R_\tau$ of Section 5 is a `tsum` over all $e \in \mathbb{N}$. In Lean the `tsum` of a series that is not summable is $0$. Show that the terms $\min(\kappa(\tau)/p^e, \kappa(-p^e\tau))$ are at most $\kappa(\tau)/p^e$, so the series is summable. Which bound of Section 5 would become false, or vacuous, if the series were not summable?

*Hint.* Compare with a geometric series. The identity $\gamma_p\sum_\tau\kappa(\tau) - S_p = v(\pi_p)\sum_\tau R_\tau$ (`New.Data.mul_sum_weight_sub_localPrimeSumTotal`) needs the true value of each $R_\tau$. With the junk value $R_\tau = 0$ it would say $\gamma_p\sum_\tau\kappa(\tau) = S_p$, which need not hold.

**Exercise 7.** In [twelve copies](/decl/New.Data.leastValLE_twelve/), check which hypotheses each case uses. Show that the split case uses neither the tight frame nor the degree window, and that the case $p > k$ does not use the unit form. Where does the main theorem use that the multiplicities of the frame are at least $6fb$?

*Hint.* Read the three statements in Section 6. The multiplicities enter only through $3|l| \leq c_i$ in [the reduction to the curve](/decl/New.Data.exists_le_norm_coeff_indicatorDatum/), where $3e_b(i) \leq c_i$ makes $y^{e}\theta^{c}$ a monomial section.

## Notes and references

The source names Katz, *Divisibilities, congruences, and Cartier duality*, J. Fac. Sci. Univ. Tokyo Sect. IA Math. 28 (1981), 667 to 678, for the rate $\gamma_p$ at inert primes. The source claims that the rate on one curve, with slope $p/(p^2 - 1)$ in infinitely many degrees, is known in the literature. Section 2 proves the form that this chapter needs, for every degree $n$.

For related work the source names Bannai and Kobayashi, *Algebraic theta functions and the p-adic interpolation of Eisenstein-Kronecker numbers*, Duke Math. J. 153 (2010), 229 to 295 (the source cites the arXiv version of 2006); Schneider and Teitelbaum, *p-adic Fourier theory*, Doc. Math. 6 (2001), 447 to 481; Bannai, Kobayashi and Yasuda, *Radius of convergence of the p-adic sigma function* (2017); and Bannai and Kobayashi, *Integral structures on p-adic Fourier theory* (2016). We give the last two as the source names them.

Legendre's formula for $v(n!)$ is classical. The three-part bound of Section 5 and the loss products are in [short columns gain](/chapter/short-columns-gain/), because Theorem A uses them too. The sparseness of the $b$-places is in [progression-free sets](/chapter/progression-free-sets/#where-the-argument-uses-them).

The main theorem is used in [Hecke values of character lifts](/chapter/hecke-values/). The register of findings records the degree window $[\kappa, \kappa + x^{42}]$ of the main theorem under F-095 in [hypotheses and sizes](/chapter/register-of-findings/).

Status: drafted by a model. No person has checked this chapter against the Lean source.
