---
title: The chapter and its place
lean:
  - New/UpperBound/Divisibility/LocalDivisibility.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter proves the divisibility input of Theorem A. For each prime $p$ it finds a submodule $S_p$ of the integral ramified source forms with two properties. Its colength is a power $p^l$ with $l \le \mathrm{err}(p)\,D_X$, where $D_X$ is the dimension of the space of source forms. On $S_p$ the composite lift $B_{\vartheta,\Psi}$ is divisible by $p^{\mathrm{gain}_p - \mathrm{err}(p)}$, for every twist $\vartheta$ of level prime to $p$ and every chain datum $\Psi$. The numbers $\mathrm{err}(p)$ are the allowed losses of [the archimedean size](/chapter/archimedean-size/), and their weighted sum $\sum_p \mathrm{err}(p)\log p$ is at most $f a \log^3 b$.

### Where the chapter sits

The plan of the whole book is in [the theorem and the plan](/chapter/theorem-and-plan/). The plan of Theorem A is in [Theorem A and its plan](/chapter/theorem-a-plan/), and its Section 3 states the theorem of this chapter as Input 1, [the divisibility of the composite lift](/decl/New.Data.exists_err_gaugeLe_compositeLift/). The same theorem is the divisibility part of Theorem A in [the normalized map](/chapter/theorems-a-b-c/). Section 7 of this chapter states it again and proves it. The proof of Theorem A in [Theorem A and its plan](/chapter/theorem-a-plan/) then compares the index of the submodules $S_p$ with the size of the lifts.

### What the chapter uses

The objects are those of [the objects of the upper bound](/chapter/upper-bound-objects/): the hermitian spaces $X_0, \dots, X_m$ with $m = 2(\varrho+1)$, the levels $K_j$, the source forms, the lift kernels, the chain data, the composite lift and the restriction $\mathrm{res}$ to $Y_m$. The sizes are those of [the data and their sizes](/chapter/data-and-sizes/). From earlier volumes the chapter uses:

- the $p$-adic gauge, the relation $\mathrm{GaugeLe}(d, c, \varphi)$ and the modules of integral forms, from [the p-adic gauge](/chapter/automorphic-forms/) (one line: $\mathrm{GaugeLe}(d,c,\varphi)$ says that for every $g$ the gauge of $\varphi(g)$ at $g d$ is at most $c$);
- the colength relations $\mathrm{ColengthDvd}$ and $\mathrm{IsOntoUpToColength}$, from [colength](/chapter/twisted-lattices/);
- the split Hecke operators $T_{\mathfrak l, i}$ and the Hecke polynomial, from [Iwahori and Satake](/chapter/iwahori-satake/);
- the kernels that raise gauges and the bound for standard data, from [theta kernels and gauges](/chapter/theta-kernels-gauges/).

From the chapters of this volume it uses the lift laws modulo $N$ ([upper bound objects](/chapter/upper-bound-objects/)), the marked sets, the scaled Hecke operators, the gauge bound for chains and the expansion of the gluing ([marked primes and the valuation of a chain](/chapter/chain-valuation/)), the gain, the loss and the divisibility bound of one lift ([short columns and the gain](/chapter/short-columns-gain/)), and the theorem on elementary divisors ([elementary divisors of a Hecke operator](/chapter/elementary-divisors/)). Each result from these chapters is stated where it is used.

### The notation

Fix a prime $p$ and a ring embedding $\iota_p : \mathbb C \to \mathbb C_p$. Let $\mathcal O_\iota$ be the ring of complex numbers $z$ with $|\iota_p z| \le 1$. The *integral source forms* $\mathcal A_\iota$ are the source forms $\varphi$ with $\mathrm{GaugeLe}(1, 1, \varphi)$. They form an $\mathcal O_\iota$-module. A form $F$ *has valuation at least* $v$ if $\mathrm{GaugeLe}(1, p^{-v}, F)$. The exponents are real numbers, and $p^{x}$ means $\exp(x \log p)$.

The prime $N$ is the level. It splits in $K$ as $N = \pi\bar\pi$. The places of $E$ above $N$ have degree one. For an infinite place $\tau \in \Phi$, $\iota_p\circ\tau$ induces a prime $w_\tau$ of $E$ above $p$. The *a-places* $\Phi_a$ are the places of class $1$ modulo $q_0$, and $a$ is the length of their long row. The weight is $b$ at the b-places, and $f = |\Phi|$.

The four kinds of primes are the following. Let $\mathcal S$ be the set of primes $p < x_1$ with $\chi_K(p) \ne 1$ (the small nonsplit primes).

1. $p \ne N$ and $p \notin \mathcal S$. Then $\mathrm{gain}_p = 0$ and $\mathrm{err}(p) = 0$.
2. $p \in \mathcal S$ and $p$ is not exceptional. Then $\mathrm{err}(p) = 2\,\mathrm{loss}(p)$ and $S_p = \mathcal A_\iota$.
3. $p \in \mathcal S$ and $p$ is exceptional. Then $\mathrm{err}(p) = 2\,\mathrm{loss}(p)$ and $S_p$ is the image of a power of a product of scaled Hecke operators, plus $p^{j_p}\mathcal A_\iota$.
4. $p = N$. Then $\mathrm{gain}_N = 0$, $\mathrm{err}(N) = 2mfb$, and $S_N$ is the set of integral forms $\varphi$ such that $\mathrm{Up}^{m/2}\varphi$ is integral for a smaller lattice $L_0$.

Here $\mathrm{loss}(p) = f \log^2 b \cdot (a/p) \cdot \mu_p$, with $\mu_p = m$ if $p \equiv \pm 1 \bmod m$ and $\mu_p = 1$ otherwise, and $j_p = \lceil 2mfa/p\rceil$.

### A sketch of the proof

Away from $N$, the composite lift of a chain datum equals the restricted chain of a weak chain datum ([the expansion of the gluing](/decl/New.Data.IsChainDatum.exists_isWeakChainDatum_compositeLift_eq/)). For a weak chain datum the gauge of the chain is bounded by the sum of the bounds of its $m$ lifts ([the gauge bound for chains](/decl/New.Data.IsWeakChainDatum.gaugeLe_chain/)). So it suffices to bound one lift at a time.

In case 1 each lift is integral, so the chain is integral. In case 2 each lift gives at least $\mathrm{gain}_p/m$ less a small error, and the only large error is the collision sum. A collision is a pair of a-places that the Frobenius at $p$ links. If $p$ is not exceptional, the collisions are paid by $\mathrm{loss}(p)$.

Case 3 is the hard case. Here an a-place $\tau$ and its partner $[-p^{o_0}]\tau$ are both a-places, and one lift can lose about $a$ powers of $p$ at each such pair. The proof chooses a full mark $\Lambda$: one prime from each conjugate pair of primes induced by a-places. At each prime $\mathfrak l \in \Lambda$ it applies the Hecke operator $T_{\mathfrak l, r_p}$, scaled by $p^{A_{\mathfrak l}}$, once before each lift. The Hecke operator moves through the lifts and onto their data, where it turns the vacuum into a neighbour vacuum. At the neighbour the long rows at the places inducing $\mathfrak l$ no longer lose. So on the image of the scaled operators the chain is divisible by $p^{\mathrm{gain}_p - 2\mathrm{loss}(p)}$. The theorem on elementary divisors shows that this image, plus $p^{j_p}\mathcal A_\iota$, has small colength. On $p^{j_p}\mathcal A_\iota$ the crude bound of case 2 suffices.

Case 4 is a computation at the level. The gluing of the lifts in pairs at $N$ is undone by the lift laws: on ramified forms the glued chain equals a scalar times the chain of direct lifts after $\mathrm{Up}^{m/2}$. Each direct lift loses at most $fb$ powers of $N$, and the scalar loses at most $mfb$. The colength of the forms with $\mathrm{Up}^{m/2}\varphi$ integral for $L_0$ is bounded by a mean degree of the weight.

### The order of the sections

Section 2 sets up the level $N$: the places $\Sigma_N$, the points $\delta_j$ and the module $\mathcal A'$. Section 3 bounds the colength of $\mathcal A'$. Section 4 proves the bound for the composite lift at $N$. Section 5 moves the scaled Hecke operators through the chain at an exceptional prime. Section 6 bounds the colength of the image of one scaled Hecke operator. Section 7 puts the four cases together. Section 8 has exercises and notes.
