---
title: Exercises and notes
lean:
  - Lib/Shimura/HeckeTower/Model.lean
  - Lib/Shimura/HeckeTower/HeckeData.lean
  - Lib/Shimura/IntegralModel/TowerExistence.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $E = \mathbb{Q}(i)$ and $n = 1$, so that $(2|n|)^{[E:\mathbb{Q}]} = 4$. List the units $y$ of $\mathbb{Z}[i]$. For each prime $w$ of $\mathbb{Z}[i]$ with $q_w \le 4$, find a unit $y \neq 1$ with $y \equiv 1 \pmod w$. Then show that no such $y$ exists for $q_w = 5$. This is the arithmetic step in the proof of [the theorem on neat levels](/decl/New.Variety.eventually_isNeat/). That theorem itself asks for a field with at least two infinite places, so it does not apply to $\mathbb{Q}(i)$.

*Hint.* The units are $\pm 1, \pm i$. The prime $1 + i$ has $q = 2$, and $-1 \equiv 1$ modulo it. For $q = 5$, use $|N(y - 1)| \le 4$.

**Exercise 2.** Let $k = \mathbb{F}_q$ and $n = 2$. Compute $\sum_A (-1)^{\dim A} q^{\binom{\dim A}{2}}$ over all subspaces $A$ of $k^2$. Then let $W$ be a line, and compute $F(B) = \sum_{A + W = B} \mu(A)$ for $B = W$ and $B = k^2$. Check that both are $0$, as in [the Möbius lemma](/decl/New.Variety.cancels_moebius_of_factorsThrough_sup/).

*Hint.* There are $q + 1$ lines. The first sum is $1 - (q + 1) + q = 0$. For $B = W$, the $A$ are $0$ and $W$.

**Exercise 3.** The field `covering` of [the model](/decl/New.Variety.Model/) asks the torsor condition only for points over fields of characteristic $0$. Give a map $c : W \to Z$ of schemes over $\mathbb{Z}$ with an action of $\mathbb{Z}/2$ that satisfies this condition but is not étale over $\mathbb{F}_2$.

*Hint.* Take $W = Z = \operatorname{Spec} \mathbb{Z}[t, t^{-1}]$, the map given by $t \mapsto t^2$ on coordinates and the action $t \mapsto -t$. In characteristic $0$ the fibre over $b \neq 0$ is $\{a, -a\}$ with $a \neq -a$. Over $\mathbb{F}_2$ the map is purely inseparable. Explain why the point $t = 0$ must be removed.

**Exercise 4.** In the theorem on extension of homomorphisms over an arc, the source uses $k \in \{1, 2\}$ so that $\mu + k$ is a unit of the valuation ring $O$. Prove that one of $\mu + 1$ and $\mu + 2$ is a unit for every $\mu \in O$. Give an example in which $\mu + 1$ is not a unit.

*Hint.* If both lie in the maximal ideal, so does their difference. For the example take $\mu = -1$.

**Exercise 5.** Take $n = 1$ in the [theorem on the base](/decl/New.Variety.UniversalFamily.smooth_and_isDenseFamily_and_exists_comp_eq_act/). Compute the relative dimension of $Z$ in terms of $\nu$ and $[E : \mathbb{Q}]$. Explain why the part of the dimension that comes from the ball is $0$.

*Hint.* The dimension is $|n| - 1 + \nu \cdot \mathrm{abelianDim}$, and $\mathrm{abelianDim} = |n| [E : \mathbb{Q}] / 2$ (Section 1).

**Exercise 6.** The lemma on large congruences asks $(2|n|)^{[E:\mathbb{Q}]} < N(I)$. Show by an example with $E = \mathbb{Q}(\zeta_3)$ and $n = 1$ that the arithmetic step of its proof fails for an ideal with $N(I) = 3$.

*Hint.* Take $y = \zeta_3$ and $I = (1 - \zeta_3)$.

## Notes and references

The textbook construction of integral models of PEL Shimura varieties is in Kottwitz, *Points on some Shimura varieties over finite fields*, J. Amer. Math. Soc. 5 (1992), §5, and for the unitary groups used here in Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties* (2001), Chapter III. Lan, *Arithmetic compactifications of PEL-type Shimura varieties* (2013), Chapter 1, treats the general case. The theory of theta functions and of the theta group is in Mumford, *On the equations defining abelian varieties I*, Invent. Math. 1 (1966), and in Mumford, *Abelian Varieties*, §23. The congruence relation in the form used here goes back to Eichler and Shimura for modular curves. Its use for unitary Shimura varieties is in Harris and Taylor, Chapter III, as cited by the source. This book has not compared the source with these works step by step. It does not claim that the source follows any of them.

The construction of the source replaces the moduli problem by closures of theta-null points. This book does not know a published account of an integral model built in this way.

Findings of this chapter, from a reading of the source at pin 72fead1:

1. The source defines an abelian scheme without asking for connected fibres. Section 5 shows that the definition implies connected geometric fibres, by an argument on the finite component group. That argument is not in the source.
2. The source does not compare its model with the moduli space of Kottwitz. No result states that the closure of Section 6 is the textbook model or is isomorphic to it.
3. The object `New.Variety.UniversalFamily` has no universal property. The name refers to the construction only.
4. `New.Variety.IsGaloisCovering` asks the torsor condition only on points over fields of characteristic $0$. It does not ask for finiteness or étaleness.
5. The source makes the fields of theta families global instances, in Lib/Shimura/IntegralModel/ThetaFamilyRigidity.lean (lines 106 and 141), in PELThetaTori.lean (lines 168 and 442), and in UniversalFamily.lean (line 575). A reader of a single file can miss these instances.
6. Two line numbers in the plan of this chapter are off: `New.PEL` is at line 89, not 85, and `New.Variety.exists_thetaFamily_of_points` is at line 1022, not 1017.
7. The literature citations in the docstrings of the source have not been checked by this book against the cited works.

Status: drafted by a model. No person has checked this chapter against the Lean source.
