---
title: What the chapter proves
lean:
  - Lib/Shimura/Eigenspace.lean
  - Lib/Shimura/CongruenceRelation/EichlerShimura.lean
  - Lib/Shimura/HeckeTower/Model.lean
  - Lib/GaloisRep/Main/Defs.lean
  - Lib/GaloisRep/Main/SeedRepresentation.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter attaches a Galois representation to a system of Hecke eigenvalues. The input is an integral model of a tower of Shimura varieties of unitary type, with its Hecke correspondences, and a system $\theta$ of Hecke eigenvalues at the safe places. The output is a continuous representation $\rho$ of $\operatorname{Gal}(\bar E/E)$ over $\bar{\mathbb{Q}}_\ell$. At each safe place $w$ the representation is unramified (or crystalline, above $\ell$), and the Hecke polynomial of $\theta$ at $w$ kills the image of a geometric Frobenius. Some Hodge-Tate weights of $\rho$ at one embedding are also controlled.

The key step is the congruence relation of Eichler and Shimura. In characteristic $p$, a Hecke correspondence at a place above $p$ becomes a sum of Frobenius twists of simpler maps. On cohomology this turns into a polynomial identity between Hecke operators and the Frobenius element. The identity is the Hecke polynomial.

The place of the chapter in the argument is described in [the theorem and the plan](/chapter/theorem-and-plan/). Briefly: the source proves Theorem A for the Rankin-Selberg L-functions that it needs by building Galois representations for certain automorphic forms on unitary groups. This chapter is the geometric core of that construction. The chapters [on complex abelian varieties](/chapter/complex-abelian-varieties/) and [on the integral model](/chapter/integral-model/) build the model. This chapter uses the model. The chapter [on attached representations](/chapter/attached-representations/) explains the local conditions that the output satisfies, and the chapter [on building the representations](/chapter/building-representations/) carries the output to all the forms that the source needs.

### The model case: modular curves

The model case is the classical relation for the modular curve $X_0(N)$ and a prime $p \nmid N$. Diamond and Shurman, *A First Course in Modular Forms*, Section 8.7, state it as follows. In characteristic $p$ the Hecke correspondence $T_p$ on $X_0(N)$ is the sum of the Frobenius correspondence and the transpose of Frobenius composed with the diamond operator $\langle p \rangle$. On the $\ell$-adic cohomology $H^1$ of the curve, with $\ell \neq p$, this gives
$$\operatorname{Frob}_p^2 - T_p \operatorname{Frob}_p + p \langle p \rangle = 0,$$
where $\operatorname{Frob}_p$ is a geometric Frobenius element. Take the quotient of $H^1$ on which the Hecke operators act by the eigenvalues of a newform $f$ with $T_p f = a_p f$ and $\langle p \rangle f = \chi(p) f$. On this quotient the Frobenius is killed by $X^2 - a_p X + p\chi(p)$. This is the theorem of Eichler, Shimura and Deligne in weight 2 (Deligne, *Formes modulaires et représentations l-adiques*, Séminaire Bourbaki 355, 1969).

Three steps carry the classical proof, and the source follows all three.

1. A pointwise statement. Let $E$ be an ordinary elliptic curve in characteristic $p$, with a level structure, and lift it to characteristic $0$. The $p + 1$ subgroups of order $p$ of the lift give the $p + 1$ points of $T_p$. In the reduction, one of them becomes the kernel of Frobenius, and the quotient is the Frobenius twist $E^{(p)}$. The other $p$ become one and the same étale subgroup, and the quotient is the twist $E^{(1/p)}$ by the inverse of Frobenius. So the formal sum $T_p(x)$ of points is $[F(x)] + p\,[F^{-1}(x)]$, up to the diamond operator. The supersingular points need a separate argument.
2. A cohomological statement. A relation between correspondences gives a relation between their actions on cohomology. The Frobenius of the special fibre acts on the cohomology of the general fibre through a Frobenius element of the Galois group.
3. Linear algebra. Restrict to the Hecke eigenquotient, where $T_p$ acts by the scalar $a_p$.

### The general case in the source

The source works with a tower of models of Kuga-Sato type for a unitary similitude group of signature $(1, n - 1)$, over a CM field $E$. The data is a [Model](/decl/New.Variety.Model/), with a base $Z$, level covers $W_i$, and legs $p_g : W_i \to Z$. The chapter [on the integral model](/chapter/integral-model/) constructs it. At a split safe place $w$ with residue field $k_w$ of order $q$, the Hecke elements are indexed by the subspaces $A$ of $k_w^n$. Step 1 becomes the following relation (Section 3): for every geometric point $x$ of the special fibre,
$$\sum_{A \leq k_w^n} (-1)^{\dim A} q^{\binom{\dim A}{2}} \left[\operatorname{Frob}^{(n - \dim A) f}(p_{g_A}(x))\right] = 0,$$
where $q = p^f$ and $g_A$ is the Hecke element of $A$. Write $u_A = p_{g_A}$ and $F$ for the $q$-power Frobenius. For $n = 2$ the relation reads $[F^2 u_0(x)] - \sum_L [F u_L(x)] + q\,[u_{k^2}(x)] = 0$, with a sum over the $q + 1$ lines $L$. This has the shape of the classical relation $X^2 - T X + q S = 0$.

Step 2 is the theorem [congruence_relation](/decl/New.Variety.ellAdicCohom.congruence_relation/) of Section 2. Step 3 is Sections 4 and 6. The polynomial that comes out is
$$P_w(X) = \sum_{j = 0}^{n} (-1)^j q^{\binom{j}{2}} t_j X^{n - j},$$
the [Hecke polynomial](/decl/New.heckePoly/), where $t_j$ is the eigenvalue of the Hecke operator $\tau_{w, j}$, the sum over the $j$-dimensional subspaces.

### What the chapter uses

The chapter uses three bodies of work from other chapters.

* The cohomology $V^n(X) = \mathbb{Q}_\ell \otimes H^n(X_\Omega, \mathbb{Z}_\ell)$ of the source, with smooth and proper base change and with a Lefschetz formula. This is the cohomology as Ext on test rings of [Volume 7, Chapter 2](/chapter/cohomology-ext/). The book does not compare it with the étale cohomology of SGA 4, and the source does not either.
* The crystalline comparison for this cohomology, from [the comparison theorems](/chapter/comparison-theorems/), for the places above $\ell$.
* The model itself, with its congruence relation, from [the integral model](/chapter/integral-model/). This chapter proves the pointwise step that the model uses, but the model is assembled there.

It also uses the trace formula on the definite unitary group, in a finite form that the source proves itself (Section 5).

### The main theorem in one paragraph

The theorem is [exists_galois_rep](/decl/New.Variety.Model.exists_galois_rep/). Let $X$ be a model at a neat level $\mathfrak{N}$, over a localization $R$ of $\mathcal{O}_E$ in which the safe places are not inverted. Let $\theta$ be a system of eigenvalues at the safe places, and let $J$ be a multiset of weights $h \geq 0$ in which $\theta$ occurs. Then there is a continuous $\ell$-adic representation $\rho$ such that at every safe place $w$, $\rho$ is good at the places above $w$, each $h \in J$ is a Hodge-Tate jump of $\rho$ at the given embedding of $E$ into $\mathbb{C}$, and $P_w$ (moved to $\bar{\mathbb{Q}}_\ell$) kills every geometric Frobenius above $w$. Section 6 states it exactly.

The dimension of $\rho$ is not controlled. It can be $0$. The source uses the theorem only through the jumps: a representation with a jump has positive dimension. The chapter on [building the representations](/chapter/building-representations/) explains how the source gets a representation of the right dimension from it.

### How the source uses this chapter

The source does not apply the theorems of this chapter by name in `New/`. It reaches them through one chain. A private lemma of the seed representation file calls the model of the chapter [on the integral model](/chapter/integral-model/) and then `exists_galois_rep` ([SeedRepresentation.lean, line 544](lean:Lib/GaloisRep/Main/SeedRepresentation.lean#L544)). The theorem [exists_rep_of_cuspidal_type](/decl/New.GaloisRep.exists_rep_of_cuspidal_type/) builds on that lemma, and the rest of `Lib/GaloisRep` builds on it in turn. So `congruence_relation` and `exists_galois_rep` are load-bearing, but only through this chain.

### The plan

Section 2 proves the congruence relation on cohomology from a pointwise relation. Section 3 proves the pointwise relation, by a Möbius cancellation over subspaces and a geometric step at each point. Section 4 builds the eigenquotient and proves its three properties. Section 5 explains when a system of eigenvalues occurs in a weight, through a comparison of two finite counts. Section 6 puts the parts together. Section 7 has the exercises and the notes.

Lean accepts the theorems of this chapter, if the checks that the source reports hold. This book did not rerun the checks (Volume 0, Chapter 2).
