---
title: The chapter and its place
lean:
  - New/UpperBound/Kernels/JetConjugatesAndBounds.lean
  - New/UpperBound/Kernels/ThetaLiftGauge.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter studies one theta kernel at a time. A theta kernel takes a datum, a vector in the space of the Weil representation of a definite dual pair, and gives a linear map from vectors of weight $(\kappa, e)$ in rank $n$ to vectors of weight $(\kappa, e_a)$ in rank $n'$. The matrix of this map is a matrix of jets: derivatives at $0$ of the theta function of the datum, along the polynomial entries of a Schur matrix. The chapter proves two kinds of bounds for these jets. The archimedean bounds control every conjugate $\sigma(\text{jet})$, for all automorphisms $\sigma$ of $\mathbb{C}$. The $p$-adic bounds say how much the kernel can raise the $p$-adic gauge of a vector. Together they say that a kernel with integral vacuum data maps integral vectors to integral vectors, up to an explicit factor, and that its conjugates have an explicit size.

### Where the chapter sits

The plan of the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/), and the plan of Theorem A is in [Theorem A and its plan](/chapter/theorem-a-plan/). Theorem A bounds the norm of a short form in two ways. One bound comes from divisibility prime by prime, and the other from an archimedean size. Both bounds are first proved for one kernel, in this chapter, and then summed over chains and Hecke operators in later chapters:

- the archimedean bound for Schur jets is used in [the archimedean size of the composite lift](/chapter/archimedean-size/), and the bound for one translate of the integral vacuum is used for the comparison operator in Volume 11;
- the gauge bounds at a non-split prime and for standard data are used in [divisibility prime by prime](/chapter/divisibility/) and in [marked primes and the valuation of a chain](/chapter/chain-valuation/);
- the results on data built from functions modulo an ideal are used in the same places and in Volume 11.

The model case of [Theorem A and its plan](/chapter/theorem-a-plan/) is the theta series of the lattice $\mathcal{O}_K$. There the coefficients are integers, so they are integral at every prime, and their conjugates are the coefficients themselves, so one size bound is enough. In the general case the jets are algebraic numbers only after a fixed scale is put in, and their conjugates are different numbers. The main work of the first half of the chapter is to bound all conjugates at once. The tool is a semilinear operator $L$ on the data that realizes $\sigma$ on the jets.

### What the chapter uses

The chapter uses these results of earlier chapters. Each is stated in one line where it is used.

- From [the integral vacuum and tight frames](/chapter/integral-vacuum/): the integral vacuum $\theta^\circ = c_s^{\,n}\,\mathrm{vac}$, the bound $|\sigma(\theta^\circ(\mathrm{fin}(x)))| \le \exp(C_{\mathrm{vac}}\,q_1^2)^{n}$ for its conjugate values, the standard data $\mathrm{SD}_p(V, \delta)$, and the theorem on conjugate jets of translates.
- From [the count and the divisibility of standard data](/chapter/normal-forms/): the $p$-adic bounds for jets of standard data, along homogeneous integral polynomials and along products of minors. These are results of an earlier chapter of this volume that is written at the same time as this one.
- From [the seesaw identity, part 1](/chapter/seesaw-identity-1/): admissible combinations of translates and the expansion of a Schrödinger datum $\Psi \otimes \mathrm{vac}$ as such a combination.
- From Volume 6, [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/): abstract kernels, the theta kernel, and the Galois law for a semilinear map that scales translations.
- From Volume 4, [automorphic forms](/chapter/automorphic-forms/): the $p$-adic gauge and its invariance under rational points and under points integral above $p$.
- From Volume 5, [Weyl modules](/chapter/weyl-modules/): Schur matrices, the Gram norm on Weyl modules, and the bound for the Gram norm of a Schur matrix.

The two Lean files of the chapter import only files of earlier chapters of this volume and of earlier volumes. No result of a later chapter of Volume 9 is used.

### Notation

Fix the parameters $P$ of the argument, with $K = \mathbb{Q}(\sqrt{-d})$ for the prime $d$. Fix the exponent $s$, and let $E = K(\zeta)$ with $\zeta$ a primitive root of unity of order $q_1 = q_1(s)$. Let $\Phi$ be the set of infinite places of $E$ and $f = |\Phi|$. $\mathrm{Gal}(\mathbb{C}/K)$ is the group of field automorphisms of $\mathbb{C}$ that fix $K$. For a hermitian space $V$ of rank $n$ over $E$:

- $\mathcal{S}(V)$ is the space of data, with the Heisenberg representation $\varrho$ and the Weil representation $\omega$, as in [the Weil representation](/chapter/weil-representation/); a datum $F$ has values $F(y) = \theta(\varrho(y)F)$ at adelic vectors $y$, where $\theta$ is the theta functional;
- $\mathrm{fin}(x)$ is the adelic vector with archimedean part $0$ and finite part $\alpha x$, for a finite adelic vector $x$ and the idele $\alpha$ of the Weil data, and $\varrho^\pm(x)$ is $\varrho(\mathrm{fin}(x))$ times a root of unity;
- $V^{\mathrm{fin}}$ is the span of the vectors $\varrho(\mathrm{fin}(x))\,\mathrm{vac}$, the finite part;
- $J_t F$ is the Taylor series at scale $t$ of the theta function of $F$, a power series in variables $X_{\tau, i}$ for $\tau \in \Phi$ and $i$ in the index set of $V$; for a polynomial $Q$ and a power series $G$, $\partial_Q G$ is the value at $0$ of $Q(\partial)G$, the *jet* of $G$ along $Q$;
- $t_0 = \mathrm{jetScale}$ is the fixed scale of [the integral vacuum and tight frames](/chapter/integral-vacuum/), and $\Omega_E = e^{C_d}\,2\pi/\mathrm{rd}(E)$ is the period constant there;
- $C_P = \mathrm{constantBound}$ is the constant of [the sizes at a glance](/chapter/sizes/): it is $C_{\mathrm{vac}} + (2d + 6)$ plus a nonnegative term that depends only on $q_0$ and $d$.

For two index sets $n$ and $n'$, $V_n$ and $V_{n'}$ are the standard definite spaces, and $H = \mathrm{Hom}(V_n, V_{n'})$ is the space of $n' \times n$ matrices. Its variables are $X_{\tau, j, i}$ with $\tau \in \Phi$, $j \in n'$, $i \in n$. A weight $\kappa$ counts columns: $\kappa(\tau, h)$ is the number of columns of height $h$ at the place $\tau$. The number of boxes in the columns of height below $N$ is
$$\mathrm{boxes}(\kappa, N) = \sum_{\tau \in \Phi} \sum_{h < N} h\,\kappa(\tau, h).$$

### A sketch

The chapter has five steps.

1. *Conjugation.* For $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ there is a $\sigma$-semilinear map $L$ on $\mathcal{S}(V)$ that keeps the finite part, turns translation by $x$ into translation by $b x$, and conjugates the jets: $\sigma$ applied to $J_{t_0} F$ is $J_t(LF)$, with the places renamed, at a scale $t$ with $|t|^2 = \Omega_E^{-1}$. This is Section 2. It assembles the conjugate jets of [the integral vacuum and tight frames](/chapter/integral-vacuum/) into one operator.
2. *Values.* The values of $L\,\varrho(\mathrm{fin}(x))\,\omega(g)\,\theta^\circ$ are bounded by $\exp(C_P (q_1 n + 1)^2)$, uniformly in $x$, $g$ and the point. This is Section 3. It rests on a packing bound for a lattice whose squared lengths are integers.
3. *Jets.* A jet is a Gaussian integral of a polynomial against the values of $LF$, by the Fock model. So Cauchy's estimate bounds $|\sigma(\partial_Q J F)|$ by the growth of $Q$. With Schur polynomials this gives a bound for the conjugates of the Schur jet matrix in the Gram norm. This is Section 4.
4. *Gauges.* At a prime $p$, a kernel *raises gauges by $c$* if it maps a vector of gauge $1$ at $g$ to a vector of gauge at most $\max(c, 0)$ at $h$, for all $g$ and $h$. Weak approximation moves the two gauges to the identity, where the claim is an entrywise bound for the jet matrix. With the $p$-adic bounds for jets of standard data this gives explicit factors. This is Section 5.
5. *Data modulo an ideal.* A function $\Psi$ on matrices modulo an ideal $\mathfrak{m}$, put at the places of $\mathfrak{m}$, gives a datum. An integer multiple of it is standard at the primes prime to $q$, and it is a combination of translates of the integral vacuum with coefficients of controlled size. This is Section 6.

Section 7 has exercises and the notes.

**Remark (Formalization).** The two files of the chapter are New/UpperBound/Kernels/JetConjugatesAndBounds.lean and New/UpperBound/Kernels/ThetaLiftGauge.lean. The source also has a file DefiniteKernelSize in the same folder. It belongs to Volume 11 and is not treated here. Many statements below quantify over all $\sigma$ in the group of ring automorphisms of $\mathbb{C}$, and some only over $\mathrm{Gal}(\mathbb{C}/K)$. The two are linked by a lemma of [the integral vacuum and tight frames](/chapter/integral-vacuum/): each automorphism of $\mathbb{C}$ has the same absolute values as some automorphism over $K$, because $K$ has one infinite place.
