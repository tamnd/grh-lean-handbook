---
title: Theta functions at a nonsplit prime
lean:
  - New/Derivatives/FormalGroup/FrobeniusCongruence.lean
  - New/Derivatives/FormalGroup/Exponent.lean
  - New/Derivatives/FormalGroup/Resolution.lean
  - New/Derivatives/FormalGroup/ThetaProducts.lean
  - New/Derivatives/Divisibility/NormalForm.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theta functions at a nonsplit prime

This chapter studies the theta function of a CM elliptic curve at a prime $p$ that does not split in $K = \mathbb{Q}(\sqrt{-d})$. Its Taylor series, read in $\mathbb{C}_p$, does not have integral coefficients after a natural scaling of the variable. The chapter proves that the failure has an exact form. After the scaling, the series is an integral series times one exponential, and the exponent is known modulo a prime element. For products of theta functions along a resolution of the identity, the exponent is a series in a few fixed polynomials, the couplings. This statement is the normal form. The next chapter counts the divisibility of jets of series in the normal form.

### Where the chapter sits

[Theorem A and its plan](/chapter/theorem-a-plan/) states Theorem A and its three inputs. The place of Theorem A in the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/). The first input is the divisibility of a chain of theta lifts, prime by prime. At a split prime the needed bound is simple. At a nonsplit prime the source claims a gain: the theta lifts are more divisible than the plain bound says. The local prime sum $s_p(y, \sigma)$ of [the three inputs](/chapter/theorem-a-plan/) measures this gain. It is a sum over $e \in I_p$ that compares a place $\sigma$ with the place $u(-p^e)\sigma$. This chapter is where these places first meet the theta functions. The place $u(-p^e)\tau$ is the *partner* of $\tau$, and the coupling $\Gamma_e$ joins each coordinate at $\tau$ with the coordinate at the partner.

The chapters of Volume 9 that use this one are [the count and the divisibility of standard data](/chapter/normal-forms/), which reads the divisibility of jets from the normal form, and through it the later chapters on the valuation of a chain.

### What the chapter uses

We use the following background. Each item is one line, with the place where it is proved.

- The CM lattice $C$, its theta function $\theta$, the coordinates $x$ and $y$, and the model $y^2 + a_1 xy = x^3 + x$ are in [sigma, theta and the curve](/decl/New.CMLattice.weierstrass_equation/) of Volume 3.
- The ring $\mathfrak{o}[[y]]$ of integral series in $y$ is defined in [Volume 3](/decl/New.CMLattice.integralSeriesRing/). The integrality of $\theta(\alpha z)/\theta^{N}$ for an isogeny $\alpha$ of degree $N$ is the [theorem on isogenies](/decl/New.CMLattice.exists_rescale_theta_eq_theta_pow_mul/).
- The formula $g'' = g''(0) + x$ for $g = -\log\theta$ is the [lemma on the logarithm of theta](/decl/New.CMLattice.derivative_derivative_negLogTheta/).
- The formal parameter $T$ and the scale $\varpi$ with $T(\varpi z) = \varpi Y$ are in the [theorem on the formal parameter](/decl/New.CMLattice.exists_scaled_formalParam/).
- The exponential bound $v(j!) \le j/(p-1)$ and the integrality of $\exp g$ when $v(g) \ge 1/(p-1)$ are in [the other tools](/decl/New.norm_coeff_expSubst_le_one/) of Volume 7.
- The series $\sum_{i \in I} X^{p^i}$ over a ring of characteristic $p$ is the [prime power series](/decl/New.primePowerSeries/) of Volume 7.
- The field $E = K(\zeta)$, its group $\Phi$ of infinite places, and the place $u(\nu)$ of an integer $\nu$ are in [fields, places and twists](/decl/New.Parameters.placeOfInt/).
- The Frobenius modulo a prime, as a statement about ring maps from $\mathcal{O}_E$, is [Lemma](/decl/New.Parameters.forall_map_galOfPlaceInt_eq_pow_iff/) of [the field E at the primes](/chapter/field-at-primes/).
- The CM curve $\mathcal{E} = \mathbb{C}/\Omega_0\mathcal{O}_K$ of the argument, `New.Parameters.cmCurve`, is fixed in [the integral vacuum and tight frames](/chapter/integral-vacuum/).

### Notation

Throughout, $d$ is a prime with $d \equiv 7 \bmod 8$ (the class `New.PrimeSevenModEight d`), and $K = \mathbb{Q}(\sqrt{-d})$. The character $\chi_K(p) = (p/d)$ is the Legendre symbol. The prime $2$ splits in $K$, since $-d \equiv 1 \bmod 8$. A prime $p$ is *nonsplit* if $\chi_K(p) \ne 1$. Then $p = d$ (ramified, $\chi_K(p) = 0$) or $p$ is inert ($\chi_K(p) = -1$), and $p$ is odd.

The map $\iota_p : \mathbb{C} \to \mathbb{C}_p$ is a ring homomorphism, given by an instance of `New.PadicPlace p`. We write $\mathfrak{o}$ for the valuation ring of $\mathbb{C}_p$ (`New.valRingCp p`), $|\cdot|$ for the norm of $\mathbb{C}_p$ with $|p| = 1/p$, and $v$ for the valuation with $v(p) = 1$. A series is *integral* if its coefficients lie in $\mathfrak{o}$. In Lean a series over $\mathfrak{o}$ is a separate object, and `New.seriesToCp` maps it to a series over $\mathbb{C}_p$. We write $\exp g$ for `New.expSubst g`, the exponential series at a series $g$ with $g(0) = 0$.

The numbers at $p$ are as in Volume 3:

- $\pi_p = \sqrt{-d}$ if $p = d$, and $\pi_p = p$ otherwise (`New.piPrime`). Its image in $\mathfrak{o}$ is `New.piPrimeInt`.
- $q_p = p^2$ if $p$ is inert, and $q_p = p$ otherwise (`New.primeNorm`).
- $v(\pi_p)$ is $1/2$ if $p = d$, and $1$ otherwise (`New.piPrimeValuation`).
- $\rho_p = v(\pi_p)/(q_p - 1)$ (`New.varpiValuation`). So $\rho_p = 1/(p^2 - 1)$ for inert $p$, and $\rho_p = 1/(2p - 2)$ for $p = d$.
- $I_p^\circ$ is the set of all $e \in \mathbb{N}$ if $p = d$, and the set of odd $e$ if $p$ is inert (`New.partnerExponents`). The set $I_p$ of [the three inputs](/chapter/theorem-a-plan/) is the set of positive elements of $I_p^\circ$.
- For $\varpi \in \mathbb{C}_p$, $c_\varpi = \varpi^{p+1}/p$.

The letter $\varpi$ here is the $p$-adic scale of Volume 3. It is not the generator of the different in [the field E at the primes](/chapter/field-at-primes/).

### A model case

Take $d = 7$ and $p = 3$. The squares modulo $7$ are $1$, $2$ and $4$, so $\chi_K(3) = -1$ and $3$ is inert. Then $\pi_p = 3$, $q_p = 9$, $\rho_p = 1/8$, and $|\varpi| = 3^{-1/8}$. The constant $c_\varpi = \varpi^4/3$ has $|c_\varpi| = 3^{1 - 1/2} = 3^{1/2}$. So $c_\varpi$ is not integral, but $|c_\varpi \pi_p| = 3^{-1/2} = p^{-1/(p-1)}$. This is exactly the bound of the integrality lemma for the exponential: $\exp(c_\varpi \pi_p h)$ is integral for every integral series $h$ with $h(0) = 0$.

The theorem of Section 4 gives integral series $W$ and $\Xi$ with $\theta(\varpi z) = W \exp(c_\varpi \Xi)$, and
$$\Xi \equiv \lambda \sum_{e \text{ odd}} \sum_{j \ge 0} \bigl(z^{3^e} z\bigr)^{3^j} = \lambda\bigl(z^4 + z^{12} + z^{28} + z^{36} + \cdots\bigr) \pmod{3},$$
with $\lambda$ a unit. The first term already shows that $\theta(\varpi z)$ is not integral. Indeed $W(0) = 1$, and $\exp(c_\varpi \Xi) = 1 + c_\varpi \Xi_4 z^4 + \cdots$, since $\Xi$ starts in degree $4$. So the coefficient of $z^4$ in $\theta(\varpi z)$ is $W_4 + c_\varpi \Xi_4$. Here $|W_4| \le 1$ and $|c_\varpi \Xi_4| = 3^{1/2}$, so this coefficient has norm $3^{1/2}$.

The reason for the shape of $\Xi$ is the following. The series $Y = T(\varpi z)/\varpi$ is $\equiv z + z^9 + z^{81} + \cdots$ modulo $3$, and $\Xi \equiv \lambda Y^4 = \lambda Y^3 Y$. In characteristic $3$ the cube is additive, so $Y^3 \equiv z^3 + z^{27} + \cdots$. The product of the two sums is a sum of $z^{3^a + 3^b}$ with $a$ odd and $b$ even, and each such term is $(z^{3^e} z)^{3^j}$ with $e = |a - b|$ odd and $j = \min(a, b)$.

Now take many variables $z_{(\tau, c)}$ and a product $\prod_j \theta(u_j^\dagger z)^{m_j}$ along linear forms. Each factor gives $\Xi(u_j^\dagger z)$ in the exponent. Modulo $3$, a $3^j$-th power is additive, so the exponent is a sum of $\lambda\bigl(\sum_j m_j (u_j^\dagger z)^{3^e}(u_j^\dagger z)\bigr)^{3^j}$. If the $u_j$ form a resolution of the identity, the inner sum is the coupling $\Gamma_e$ modulo $3$. This is the normal form.

### A sketch of the proof

The chapter has four steps.

1. *The Frobenius congruence* (Section 2). For nonsplit $p$, $\theta(\pi_p z) = \theta(z)^{q_p}(1 + \pi_p H)$ with $H \in \mathfrak{o}[[y]]$. The proof writes $\theta(\pi_p z)/\theta^{q_p}$ as a polynomial $R$ in $x$ of degree less than $q_p/2$, and checks $R \equiv 1$ in the low degrees, where $\pi_p g$ is integral.
2. *The supersingular coefficient* (Section 3). For inert $p$, the coefficient of $z^{p-1}$ in $x$ is a unit. The proof is a recursion for the coefficients of $z^{p-1}$ in the powers $x^n$.
3. *The exponent on one curve* (Section 4). Average $g = -\log\theta$ over the $(q_p - 1)$-th roots of unity. This keeps the part $g^\flat$ of $g$ in the degrees $\equiv p + 1 \bmod q_p - 1$, and $\theta \exp g^\flat$ is integral in $y$. The Frobenius congruence gives a functional equation for $\Xi_1 = -g^\flat(\varpi z)/c_\varpi$. Its solution modulo $\pi_p$ is $\lambda Y^{p+1}$ or $\lambda(Y^2 - z^2/2)$. Step 2 shows that $\lambda$ is a unit at inert $p$.
4. *Couplings and the normal form* (Sections 5 and 6). The couplings $\Gamma_e$ and the normal form are defined for any rule of partners. For a resolution of the identity by vectors integral above $p$, the congruence $\tau(\alpha)^{p^e} \equiv \overline{\tau'(\alpha)}$ modulo $\pi_p$, for the partner $\tau'$ of $\tau$, turns $\sum_j m_j (u_j^\dagger z)^{p^e}(u_j^\dagger z)$ into $\Gamma_e$. Then the exponents of the factors add up to a series in the couplings.

Section 7 has exercises and the notes.

**Remark (Formalization).** The results on one curve (Sections 2 to 4) hold for every CM lattice $C$ of `New.CMLattice d` and every prime $d \equiv 7 \bmod 8$. They also hold for every ring homomorphism $\iota_p$; the source does not choose a canonical one. The normal form (Section 6) is stated for the chosen curve `New.Parameters.cmCurve` of the parameters `P`, with $d = $ `P.d`. In that setting $d$ satisfies the congruences of the parameters, but the proofs of this chapter use only $d \equiv 7 \bmod 8$ and $p \nmid q_1$.
