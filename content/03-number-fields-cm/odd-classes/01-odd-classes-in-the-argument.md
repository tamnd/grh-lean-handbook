---
title: Odd classes in the argument
lean:
  - Lib/Cyclotomic/OddSha.lean
  - New/Congruences/FirstOrder/TraceRelations.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Odd classes in the argument

This chapter explains one bound of the source. Let $E$ be a CM field inside a cyclotomic field $\mathbb{Q}(\mu_N)$, and let $t \ge 0$. The source proves that one nonzero integer $X$, with $X \le 2^{4(N+t+3)^{27}} h_E$, controls a module of odd Galois cocycles of $E$ at every prime $\ell$ at once. Here $h_E$ is the class number of $E$. For each prime $\ell$, each ring $\mathcal{O}$ of integers of a finite extension of $\mathbb{Q}_\ell$ that has enough roots of unity, each $e < t$ and each $n \ge 0$, the length of the module of odd cocycles $\mathrm{Gal}(\bar{\mathbb{Q}}/E) \to \mathcal{O}/\ell^n(-e)$ is at most the valuation of $X$ in $\mathcal{O}$. The statement is [Theorem](/decl/New.exists_length_shaOdd_le/). The rest of the chapter explains its statement, its proof and its classical background.

### Why the argument needs a bound of this kind

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). One step of it builds congruences between Galois representations, and it counts the length of modules of Galois cohomology classes with coefficients in Tate twists $\mathcal{O}/\ell^n(-e)$. The count is made in Volume 12, in [the denominator bound](/chapter/denominator-bound/). There an error term $e_\ell$ collects all the losses at the prime $\ell$. Its first term is $t \cdot v_\ell(X)$, where $X$ is the integer of this chapter. The later steps need the sum of these losses, weighted by $\log \ell$, to be small compared with the size parameter $x$ of [the data and its sizes](/chapter/data-and-sizes/). So the argument needs three things from the bound:

1. One integer $X$ serves for all primes $\ell$. A separate bound for each $\ell$ is not enough, because the argument sums over $\ell$.
2. $X$ has an explicit size. The source uses $\log X \le 4(N+t+3)^{27}\log 2 + \log h_E$, and it bounds $\log h_E$ separately.
3. The bound holds for the twists $e = 0, 1, \dots, t-1$ together, and for every level $\ell^n$.

The classical theory gives bounds of this kind through the main conjecture of Iwasawa theory, proved by Mazur and Wiles. That route gives a bound for each prime $\ell$, in terms of the $\ell$-adic valuation of a Bernoulli number or an $\ell$-adic L-function. The source does not take that route. It proves a weaker statement, an upper bound at finite level, by a direct method. The method is the Euler system of Gauss sums of Kolyvagin and Rubin, combined with Voronoi's congruence for Bernoulli numbers. Section 2 recalls the classical theory. Sections 3 to 7 explain the proof of the source.

### What the source proves and what it does not prove

The object that the source bounds is a module $\text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, e, n)$ of cocycles. For $e \ne 0$ it consists of the continuous cocycles $z : \mathrm{Gal}(\bar{\mathbb{Q}}/E) \to \mathcal{O}/\ell^n(-e)$ that are unramified outside $\ell$, that vanish on a set of local elements above $\ell$, and that change sign under conjugation by a complex conjugation. For $e = 0$ it consists of the everywhere unramified homomorphisms. Section 7 gives the exact definition. The module is a model of the odd part of the Tate-Shafarevich group $\text{Ш}^1(E, \mathcal{O}/\ell^n(-e))$. The source does not prove that the model agrees with the group. The source also does not prove the main conjecture, and no $\ell$-adic L-function appears. This chapter states only what the source proves. The remarks on the formalization mark each place where the source object differs from the classical object.

### What the chapter uses

The chapter uses three earlier chapters of this volume.

- [CM fields](/chapter/cm-fields/): CM fields, the fixed algebraic closure $\Omega = \bar{\mathbb{Q}}$, the cyclotomic character, and the places of $\Omega$ as valuation rings with their decomposition and inertia groups and Frobenius elements.
- [Class field theory on finite ideles](/chapter/class-field-theory/): the Chebotarev density theorem, in its form as an existence statement, and the bound for ray class groups.
- [Local duality and the Greenberg-Wiles count](/chapter/local-duality/): the Selmer modules of cocycles, which this chapter uses only through their definition.

It also uses the Dirichlet L-functions of Volume 2, in [Dirichlet L-functions](/chapter/dirichlet-l-functions/), at negative integers. The chapter on [CM elliptic curves](/chapter/cm-elliptic-curves/) is not used.

### A sketch of the proof

The proof has five steps. Each step has its own section, and step 4 has two.

1. **Bernoulli numbers.** For $e \ge 1$, the source finds one nonzero integer $X_e \le 2^{(N+e+3)^6}$ with two properties. First, for each odd character $\psi$ of the right parity, $X_e$ is, up to an explicit factor, a multiple of the twisted Stickelberger sums $\sum \lfloor ca/(Nm) \rfloor a^e \psi(a)$ modulo every $m$. Second, $X_e$ is divisible by explicit factors $(c^e - 1)(c^{e+1} - 1)$. The tool is Voronoi's congruence, and $X_e$ is the determinant of an integer matrix whose eigenvalues are the generalized Bernoulli numbers. This is Section 3.
2. **Gauss sums.** For a prime $p$ and a place $B$ above $p$, quotients of Gauss sums over $\mathbb{F}_p$ give a family $J(x)$ of algebraic numbers, indexed by the torsion points $x$ of $\mathbb{Q}/\mathbb{Z}$. The order of $J(x)$ at $B$ is $\lfloor c\langle x \rangle \rfloor - \lfloor c \langle -x \rangle \rfloor$. This is the input of Stickelberger's theorem. This is Section 4.
3. **Kolyvagin's derivatives.** From $\ell^n$-th roots of the $J(x)$, the source builds Kolyvagin's derivative cocycles $\kappa_S$, one for each finite set $S$ of auxiliary primes. They form a Kolyvagin system: at a prime $q \notin S$, the value of $\kappa_S$ at a Frobenius is a value of $\kappa_{S \cup \{q\}}$ on inertia. This is Section 6.
4. **Components.** For each odd character $\mathrm{cyc}^e\psi$, a module of cocycles over $\mathbb{Q}$ is killed by $4X_e^2$. For $\ell > N + e + 3$, at most $v_\ell(X_e) + 1$ elements of $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ detect it. This is Sections 5 and 6.
5. **The odd part.** The module $\text{Ш}_{\mathrm{odd}}$ over $E$ splits, up to the factor $4\varphi(N)$, into these components. A count of detecting elements turns an annihilator into a bound for the length. Small primes $\ell \le (N+t+3)^2$ use a crude count of generators of a ray class group. For $e = 0$ the class number $h_E$ serves. This is Section 7.

Section 7 also shows where the argument uses the result. Section 8 has the exercises and the notes.
