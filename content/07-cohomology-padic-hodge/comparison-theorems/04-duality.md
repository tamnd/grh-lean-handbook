---
title: Duality on products of projective lines
lean:
  - Lib/PadicComparison/Duality/LineIntegration.lean
  - Lib/PadicComparison/Duality/GoodPairs.lean
  - Lib/Cohomology/SmoothBaseChange.lean
  - Lib/Cohomology/ProjectiveLine/ChernClass.lean
decls:
  - New.Variety.TorsionCoeff.HasLineFormula
  - New.Variety.ComparedTheory
  - New.Variety.ComparedTheory.IsFiniteLerayHirsch
  - New.Variety.ComparedTheory.isClosedClass_isFiniteLerayHirsch
  - New.Variety.ComparedTheory.isFiniteLerayHirsch_iff_of_isCohomEquiv
  - New.Variety.ComparedTheory.isFiniteLerayHirsch_of_retract
  - New.Variety.ComparedTheory.isFiniteLerayHirsch_topPoints_of_surjective
  - New.Variety.ComparedTheory.isFiniteLerayHirsch_iff_of_locally_bijective
  - New.Variety.ComparedTheory.isFiniteLerayHirsch_of_prod_projLine
  - New.Variety.ComparedTheory.isFiniteLerayHirsch_principal_open
  - New.Variety.ComparedTheory.isFiniteLerayHirsch_standard_etale
  - New.Variety.IsCharting
  - New.Variety.ComparedTheory.mem_of_isClosedClass_of_isCharting
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Duality on products of projective lines

This section gives the formal machine that carries a comparison of two cohomology theories from a point to all charted schemes. Section 5 uses it once, to prove the primitive comparison and the finiteness of cohomology with $\mathbb{F}_p$-coefficients on a charted scheme over $\Omega$. The source also uses it for smooth base change in `Lib/Cohomology/SmoothBaseChange.lean`, with a prime $\ell$ different from $p$. That use belongs to [the chapters on cohomology](/chapter/cohomology-ext/).

### The classical idea

In topology, the Leray-Hirsch theorem says the following. Let $E \to B$ be a fibre bundle with fibre $F$, and let $c_i$ be classes on $E$ whose restrictions to each fibre form a basis of $H^*(F)$. Then $H^*(E)$ is a free $H^*(B)$-module with basis $c_i$. See Hatcher, *Algebraic Topology* (2002), Theorem 4D.1. For the projective line, the classes are $1$ and the Chern class $\eta$ of $\mathcal{O}(1)$. This gives the projective line formula $H^*(\mathbb{P}^1 \times S) = H^*(S) \oplus \eta \, H^*(S)$.

The source uses the formula to compare two theories. Suppose that two theories satisfy the projective line formula, and that a family of maps compares them at a point. Excision and the formula carry the comparison to products of lines and to their open parts. A class on the diagonal of $(\mathbb{P}^1)^d$ then gives a duality, and the duality carries the comparison to standard étale charts. The source names SGA 4, Exposé XVI, the finiteness theorems of SGA 4½, and the duality of Dold and Puppe as the sources of the method. The step is common to several comparison theorems. The source does not claim that the form here is new.

### Theories with the line formula

All functors in this section live on the category $\mathrm{Test}_A$ of tests over a ring $A$ in which a prime $\ell$ is a unit. A torsion coefficient along a functor $g : \mathcal{C} \to \mathrm{Test}_A$ is a functor on $\mathcal{C}$ to abelian groups, killed by $\ell$, with Zariski descent for the rings $g(c)$. A theory is a torsion coefficient that also behaves well on closed loci. The locally constant functions to $\mathbb{Z}/\ell$ give a theory, and [the chapter on cohomology](/chapter/cohomology-ext/) treats the class $\eta$ for every torsion coefficient.

**Definition (Projective line formula).** A torsion coefficient $M$ along $g$ satisfies the projective line formula if, for every functor $S$ to abelian groups on $\mathcal{C}$, the classes $1$ (degree $0$) and $\eta$ (degree $2$) form a Leray-Hirsch basis. That is, every total Ext class from $S$ over the points of $\mathbb{P}^1$ is $a \cdot 1 + b \cdot \eta$ for unique classes $a$ and $b$ restricted from the base.
Lean: `New.Variety.TorsionCoeff.HasLineFormula` (Lib/Cohomology/ProjectiveLine/ChernClass.lean).

When the formula holds, integration over the line is the map $a \cdot 1 + b \cdot \eta \mapsto b$. The source calls it `New.Variety.TorsionCoeff.HasLineFormula.integrate`.

**Definition (Compared theory).** A compared theory along $g$ is a theory $\Theta$ along $g$ with an index set $I$ and classes $b_i$ of degree $0$ from the locally constant $\mathbb{Z}/\ell$-valued functions (restricted along $g$) to the coefficient of $\Theta$, such that both $\Theta$ and the theory of locally constant functions satisfy the projective line formula.
Lean: `New.Variety.ComparedTheory` (Lib/PadicComparison/Duality/LineIntegration.lean).

**Definition (Good functor).** Let $D$ be a compared theory and let $N$ be a functor from $\mathrm{Test}_A$ to abelian groups. Write $L$ for the locally constant $\mathbb{Z}/\ell$-valued functions and $F$ for the coefficient of $D$. Then $N$ is good for $D$ if:

1. the Leray-Hirsch map $(w_i)_i \mapsto \sum_i g^*(w_i) \cdot b_i$, from finitely supported families of total Ext classes from $N$ to $L$, to the total Ext group from $N \circ g$ to $F$, is bijective; and
2. the total Ext group from $N$ to $L$ is finite.

Lean: `New.Variety.ComparedTheory.IsFiniteLerayHirsch` (Lib/PadicComparison/Duality/LineIntegration.lean).

For a pair $U \subseteq Y$ of set-valued functors, the source writes $\mathbb{Z}[Y]/\mathbb{Z}[U]$ for the quotient of free abelian group functors. The pair is good if this quotient is good.

### Permanence

**Theorem (Closed class).** Goodness for $D$ is a closed class. It holds for zero functors. In a short exact sequence $0 \to X_1 \to X_2 \to X_3 \to 0$ with $X_1$ good, $X_2$ is good if and only if $X_3$ is good.
Lean: `New.Variety.ComparedTheory.isClosedClass_isFiniteLerayHirsch` (Lib/PadicComparison/Duality/LineIntegration.lean).

*Proof.* The bijectivity half is a closed class by the five lemma, applied to the long exact sequences degree by degree. For finiteness, the long exact sequence of total Ext groups puts the group of $X_2$ between those of $X_1$ and $X_3$. A group between two finite groups in an exact sequence is finite. In the other direction, the group of $X_3$ lies between those of $X_2$ and of $X_1$ shifted by one degree. $\square$

The source also proves the two-out-of-three property in the third direction: if $X_2$ and $X_3$ are good, then $X_1$ is good (`New.Variety.ComparedTheory.isFiniteLerayHirsch_of_shortExact`).

**Theorem (Cohomological equivalence).** Let $\alpha : N \to N'$ be a map such that, for every $g'$ and every coefficient $F$ with Zariski descent along $g'$, pull-back along $\alpha$ is a bijection of all Ext groups into $F$. Then $N$ is good if and only if $N'$ is good.
Lean: `New.Variety.ComparedTheory.isFiniteLerayHirsch_iff_of_isCohomEquiv` (Lib/PadicComparison/Duality/LineIntegration.lean).

**Theorem (Retracts by operations).** Let $N$ have flat values, and write $N/\ell$ for its cokernel of multiplication by $\ell$. Let $r_i : N/\ell \to N'$ and $\rho_i : N' \to N$ be natural operations without parameters, such that $\sum_i \rho_i(r_i(x))$ is always the pull-back of $x$ along $N \to N/\ell$. If $N'$ is good, then $N$ is good.
Lean: `New.Variety.ComparedTheory.isFiniteLerayHirsch_of_retract` (Lib/PadicComparison/Duality/LineIntegration.lean).

A natural operation with $d$ parameters (`New.Variety.NaturalOp`) is an additive map of total Ext groups for every theory with the line formula and every family of $d$ points of $\mathbb{P}^1$, and it commutes with restriction along functors. Integration of the first parameter over the line turns an operation with $d + 1$ parameters into one with $d$ parameters.

**Theorem (Pairs in a power of the line).** Let $I$ be a compatible family of ideals on the points of $(\mathbb{P}^1)^m$, let $U$ be the locus where $I$ is the unit ideal, and let $Q = \mathbb{Z}[(\mathbb{P}^1)^m]/\mathbb{Z}[U]$. Let $\theta_i$ be classes over the points of $(\mathbb{P}^1)^m$, from $N$ to the locally constant functions modulo those that die where $I = 0$. If the Leray-Hirsch map of the $\theta_i$ on $Q$ is surjective and $N$ is good, then $Q$ is good.
Lean: `New.Variety.ComparedTheory.isFiniteLerayHirsch_topPoints_of_surjective` (Lib/PadicComparison/Duality/LineIntegration.lean).

*Proof sketch.* The lemma `New.Variety.IdealFamily.exists_move_kernel` moves a kernel class from one point $q$ of $(\mathbb{P}^1)^m$ to a second point $q'$. It multiplies by the classes $\eta(q_j) + \eta(q'_j)$, one coordinate at a time. By surjectivity, the moved kernel is a sum $\sum_i \beta_i \cdot \theta_i$. Integration over the parameters then gives an identity that writes each class on $Q$ through classes on $N$, and the retract argument applies. $\square$

### Good pairs

The second file applies the machine to concrete pairs. Write $\mathrm{off}(Y)$ for the part of $Y$ on tests in which the maximal ideal of $A$ generates the unit ideal, that is, the part away from the special fibre.

**Theorem (Excision).** Let $u : E \to Y$ and let $U \subseteq Y$. Assume that, Zariski locally, every point of $Y$ lies in the image of $u$ or in $U$, and that two points of $E$ with the same image have the same class modulo $u^{-1}(U)$. Then $(E, u^{-1}(U))$ is good if and only if $(Y, U)$ is good.
Lean: `New.Variety.ComparedTheory.isFiniteLerayHirsch_iff_of_locally_bijective` (Lib/PadicComparison/Duality/GoodPairs.lean).

*Proof.* The kernel and the cokernel of $\mathbb{Z}[E]/\mathbb{Z}[u^{-1}U] \to \mathbb{Z}[Y]/\mathbb{Z}[U]$ are Zariski locally zero. Under Zariski descent, the map is then a cohomological equivalence, and the theorem on cohomological equivalence applies. $\square$

**Theorem (Product with the line).** Let $V \subseteq Y$, and let $S \subseteq \mathbb{P}^1$ be the complement of the point $(0 : 1)$. If the product pair $(Y \times \mathbb{P}^1, V \times \mathbb{P}^1 \cup Y \times S)$ is good, then $(Y, V)$ is good.
Lean: `New.Variety.ComparedTheory.isFiniteLerayHirsch_of_prod_projLine` (Lib/PadicComparison/Duality/GoodPairs.lean).

*Proof sketch.* The class $\eta$ dies on $S$, so it lifts to a relative class $\xi$ on the pair $(\mathbb{P}^1, S)$. Multiply by $\xi$, restrict to the graph of the tautological point of the line, and integrate over the line. This sends a class on $\mathbb{Z}[Y]/\mathbb{Z}[V]$ modulo $\ell$ to its pull-back, so the retract theorem applies. $\square$

**Theorem (Alexander duality for principal opens).** Let $T$ be presented as a polynomial ring in $d$ variables over $A$, and embed $\mathrm{Spec}\, T$ in $(\mathbb{P}^1)^d$. Let $a \in T$. Assume that the pair of the point and its part away from the special fibre is good. Then the pair of $(\mathbb{P}^1)^d$ and $\mathrm{Spec}\, T[1/a] \cup \mathrm{off}((\mathbb{P}^1)^d)$ is good.
Lean: `New.Variety.ComparedTheory.isFiniteLerayHirsch_principal_open` (Lib/PadicComparison/Duality/GoodPairs.lean).

*Proof sketch.* Up to Zariski descent, the open part is the locus where a multihomogeneous form of $a$ does not vanish on the special fibre. The theorem on pairs in a power of the line applies. The classes $\theta_i$ that it needs come from proper base change, and the goodness of the coefficient on the zero set comes from the hypothesis on the point. $\square$

**Theorem (Standard étale charts).** Let $R[X]$ be presented as a polynomial ring in $d$ variables over $A$, and let $(f, g)$ be a standard étale pair over $R$. Assume that the pair of the point and its part away from the special fibre is good. Then the pair of $Y = \mathrm{Spec}\,(R[X]/f)[1/g]$ and $\mathrm{off}(Y)$ is good.
Lean: `New.Variety.ComparedTheory.isFiniteLerayHirsch_standard_etale` (Lib/PadicComparison/Duality/GoodPairs.lean).

*Proof sketch.* Let $E$ be the functor of pairs $(y, x)$ with $x$ in $\mathrm{Spec}\, R[X][1/g]$ and $y$ a root of $f$ near $x$. One map sends $(y, x)$ to $x$, and a second map sends it to $(y, x - y)$ in $Y \times \mathbb{P}^1$. Both maps satisfy the hypotheses of excision for subfunctors with the same preimage in $E$. The principal open theorem, applied to $g$ and to $gf$, gives the first pair through a short exact sequence. The theorem on the product with the line descends from $Y \times \mathbb{P}^1$ to $Y$. $\square$

### From charts to charted schemes

**Definition (Charting).** A subfunctor $V$ of a functor $X$ on $k$-algebras is a charting if (a) $V$ is all of $X$ Zariski locally, and (b) $\mathbb{Z}[V]$ lies in every closed class that contains $\mathbb{Z}[\mathrm{Hom}(R, -)]$ for the ring $R$ of each chart of $X$ étale over a torus.
Lean: `New.Variety.IsCharting` (Lib/General/Geometry/EtaleCharts.lean).

**Theorem (Charted functors).** Let $A$ be a valuation ring and a $k$-algebra in which $\ell$ is a unit. Let $D$ be a compared theory and $P$ a closed class of functors on $\mathrm{Test}_A$, such that $P(\mathbb{Z}[Y])$ holds exactly when $(Y, \mathrm{off}(Y))$ is good for $D$. If $P$ holds at the point and the functor $X$ on $k$-algebras has a charting, then $P$ holds at $\mathbb{Z}[X]$, restricted to tests over $A$.
Lean: `New.Variety.ComparedTheory.mem_of_isClosedClass_of_isCharting` (Lib/Cohomology/SmoothBaseChange.lean).

*Proof sketch.* The proof reduces from $X$ to $V$, from $V$ to the affine charts, and from a chart to a finite cover by standard étale pieces. The theorem on standard étale charts applies to each piece. Excision passes from a locally full subfunctor $U$ of $Y$ to $Y$. $\square$

**Remark (Formalization).** Condition (b) of a charting builds the induction over charts into the definition. So the theorem on charted functors is short, and the geometric content sits in the claim that a given scheme has a charting. The class `New.Variety.IsCharted` asks for this claim for the functor of points of a scheme over $k$. This chapter takes the class as a hypothesis, and the theorems of Sections 5 and 7 state it as an instance argument.

**Remark (Formalization).** In Section 5 the source applies the theorem with $\ell = p$ and $A = \Omega$, an algebraic closure of $\mathbb{Q}$. The prime $p$ is a unit in $\Omega$. A field is a valuation ring, and its maximal ideal is zero. So the part away from the special fibre has points only over the zero ring, and goodness of $\mathbb{Z}[Y]$ is the same as goodness of the pair (`New.Variety.ComparedTheory.isFiniteLerayHirsch_freeAb_iff_relFreeAb`). The special fibre plays a role only in smooth base change, where $A$ is a valuation ring of residue characteristic different from $\ell$.

**Remark (Formalization).** Several proofs in the two files carry the line `seal CategoryTheory.Abelian.Ext in`, and both files set `backward.isDefEq.respectTransparency false`. The comments in the source say that without the seal, unification unfolds the Ext groups into the derived category and is slow. These are options of the elaborator. They do not change the statements.
