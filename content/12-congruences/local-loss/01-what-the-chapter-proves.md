---
title: What the chapter proves
lean:
  - New/Congruences/LocalLoss/CrystallineCocycles.lean
  - New/Congruences/LocalLoss/CrystallineDefect.lean
  - New/Congruences/LocalLoss/LocalLattices.lean
  - New/Congruences/LocalLoss/TateDualBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter bounds the loss of the crystalline condition at a place above $\ell$. A Selmer class of the argument is built from a congruence modulo $\ell^M$. Its restriction to a decomposition group above $\ell$ need not be crystalline. It is only a cocycle modulo $\ell^M$ that passes every linear test that crystalline cocycles pass. The chapter bounds, by Tate local duality, how far such a cocycle can be from the reduction of a true crystalline cocycle. The bound is the term $\mathrm{localDefectBound}$ of [the denominator budget](/chapter/regular-families-plan/#the-denominator-budget). The plan of the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/). Together with [exponent lattices and Kummer charts](/chapter/exponent-lattices/) and [cup products on Kisin modules](/chapter/cup-products/), this chapter is the fourth deep input of [the chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof).

### Notation

Fix a prime $\ell$ and put $G_\ell = \mathrm{Gal}(\bar{\mathbb{Q}}_\ell/\mathbb{Q}_\ell)$. Let $\Gamma$ be a topological group with an open embedding $j : \Gamma \to G_\ell$. Let $O$ be the ring of integers of a finite Galois extension of $\mathbb{Q}_\ell$ in $\bar{\mathbb{Q}}_\ell$. A *lattice* $L$ is a free $O$-module of finite rank with a continuous action of $\Gamma$. Its Tate dual is $L^\vee(1) = \mathrm{Hom}_O(L, O)(1)$. The module $Z_f(L)$ of *crystalline cocycles* is the module of maps $c : \Gamma \to L$ that become coboundaries in $B_{\max} \otimes L$. For a class $\mathcal{Q}$ of lattices, the *dual defect* $\delta_{\mathcal{Q}}(L)$ is the length of $Z_f(L)$ modulo the crystalline cocycles whose cup products with all crystalline cocycles of all members of $\mathcal{Q}$ are coboundaries. These notions are in [local duality, crystalline cocycles](/chapter/local-duality/#duality-for-crystalline-cocycles). We write $\lambda_O$ for the length normalised so that $O/\ell$ has length $1$.

The data $D$ and its sizes are in [the data and its sizes](/chapter/data-and-sizes/). We use $r = D.r$, $m = D.m$, $k = r + 1 - m$, $t = D.t = 5r$, the half gap $h_2 = r^8$, the gap $\Delta = 2h_2$, the weight $b$ at the b-places and the weight $G$ off them. The *crystalline loss* is
$$\lambda = \mathrm{crysLoss}(h_2, b, \ell) = v_\ell\Big((2b)!\,\Big(\prod_{\max(b - 30h_2^3,0) < n \leq b + 30h_2^3} n\Big)^{h_2^3}\Big),$$
and the *defect bound* is $\mathrm{defectBound}(\ell) = 10^6 \frac{m}{k}\big(b\,v_\ell(M) + \lambda\big)$, with $M = p_0p_1$. Both are defined in [weights, signs and b-places](/chapter/main-summands/#weights-signs-and-b-places).

### The main theorem

The main result of the chapter is a bound at one place. Let the multisets $J(\sigma)$, for the complex embeddings $\sigma$ of $E$, be the weights of a main summand. Let $L_c$, for $c$ in $\{\mathrm{none}\} \cup \{0, \dots, t-1\}$, be lattices: $L_{\mathrm{none}}$ is the main summand, with rank $r$ and jumps $J(\sigma_{e,g})$ at the embedding $c_g$ of $O$, and $L_c$ has the single jump $c$. Let the class $\mathcal{Q}$ be tame at a level prime, or crystalline. Then for large $O$ and each $c$ with $L_c \in \mathcal{Q}$,
$$\lambda_O\big(\delta_{\mathcal{Q}}(L_c^\vee(1))\big) \leq [G_\ell : j(\Gamma)] \cdot \mathrm{rank}(L_c) \cdot \frac{\mathrm{defectBound}(\ell)}{x},$$
with $x = 1$ for the main summand and $x = t$ otherwise. This is [the defect at a place](/decl/New.Selmer.summand_defect_le_at_place/) in [Section 5](/chapter/local-loss/#the-defect-at-a-place-above-l).

The second result links the defect to the cocycles of the argument. For a family of lattices $u_x$ and a lattice $\rho$ in the class, the cocycles modulo $\ell^m$ that obey the relations of the family, modulo those that obey the relations of crystalline cocycles, have length at most $\delta_{\mathcal{Q}}(L^\vee(1))$. This is [the Ribet cocycle bound](/decl/New.Selmer.relLength_ribetCocycles_le/) of [Section 7](/chapter/local-loss/#tate-duality-and-ribet-cocycles). Section 6 builds the local lattices to which both results apply.

### The model case

Let $\Gamma = G_\ell$, $O = \mathbb{Z}_\ell$, and let $\ell$ be much larger than all jumps that occur. In this range one expects from the theory of Fontaine and Laffaille that crystalline classes behave like classes over a field: reduction modulo $\ell$ loses nothing, and the cup product of two crystalline classes is crystalline. The source proves the form of this that it needs. If $\ell$ divides no nonzero integer near the windows of the jumps, and the negative jumps are far from $0$, then the defect is $0$. This is the third regime of [Section 4](/chapter/local-loss/#three-regimes-of-the-prime). If also $\ell > 2b + 30h_2^3$ and $\ell \nmid M$, then $\lambda = 0$ and $\mathrm{defectBound}(\ell) = 0$, so the main theorem says that the defect is $0$. The difficulty of the chapter is the small and middle primes, where $\ell$ divides an integer near a jump.

### What the chapter uses

- From [local duality](/chapter/local-duality/#duality-for-crystalline-cocycles): the classes $\mathrm{InClass}(F, K, U)$, the cup orthogonal, the dual defect, cup exponents, and the divisibility of indices from a perfect pairing.
- From [period rings](/chapter/period-rings/#the-bloch-kato-rank-formula): the Bloch-Kato rank formula for $Z_f$ over $\mathbb{Z}_\ell$.
- From [Kisin frames](/chapter/kisin-frames/#charts-and-kummer-charts): Kummer charts, their letters, ramification $e$ and residue degree $f$.
- From [side points](/chapter/exponent-lattices/#side-points): windows of jumps and the condition that $\ell$ has no multiple near a point.
- From [cup products](/chapter/cup-products/): four bounds on cup products for a Kummer chart. We state them once in Section 4.
- From [main summands](/chapter/main-summands/): signs, b-places, main summand weights, the defect bound, the crystalline colength and the Ribet cocycles.
- From Volume 2, [progression-free sets](/chapter/progression-free-sets/): the sparse set of b-places, through the lemma on short arcs.

No file of this chapter imports a file of a later chapter of Volume 12. Two results of [the denominator bound](/chapter/denominator-bound/) use this chapter. We state them in Section 7.

### The sketch

Section 2 proves two general facts. The rank of $Z_f(L)$ over $O$ is $\mathrm{rank}\,L$ plus the number of negative jumps. A cup exponent $k$, that is $\ell^k Z_f(L)$ inside the cup orthogonal, gives a defect at most $2k\,\mathrm{rank}\,L$ times the index.

Section 3 collects the arithmetic of the crystalline loss $\lambda$ and the size conditions on $(Q, m, h, G, b, \delta, \eta, W)$.

Section 4 is the core. It proves the bound for crystalline classes in three regimes of $\ell$, with $Q = kt$:

1. $\ell \leq Q$ (small primes). The Kummer chart may be ramified. The b-places are sparse along Frobenius orbits, and the sparse thick bound of [cup products](/chapter/cup-products/) gives a cup exponent.
2. $\ell > Q$ and $\lambda \geq h^3$. The chart is unramified, and the bound for any pattern gives a cup exponent.
3. $\ell > Q$ and $\lambda < h^3$. Then $\ell$ divides no integer near the windows. The defect is $0$ or is bounded by the number of low jumps.

Section 5 checks the hypotheses of Section 4 for the data $D$, handles the tame classes at the level primes, and proves the main theorem. Section 6 restricts a global lattice to a place above $\ell$ and checks that it lies in the right class. Section 7 proves the Tate duality bound for Ribet cocycles.

### The status

All four files of the chapter have full proofs in the source. They contain no `sorry` and no axiom. The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.
