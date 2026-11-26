---
title: Exercises and notes
lean:
  - Lib/General/Groups/ProfiniteCharacters.lean
  - Lib/General/Groups/CharacterTheory.lean
  - Lib/General/Measure/HaarModulus.lean
  - Lib/General/Measure/HaarNormalisation.lean
  - Lib/General/Measure/FibreMeasure.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 8. Throughout, $p$ is a prime.

**Exercise 1.** Let $a \in \widehat{\mathbb{Z}}$ be a unit of the finite adeles $\mathbb{A}_f$, with components $a_p \in \mathbb{Z}_p$. Show that $\iota(a) = \prod_p p^{v_p(a_p)}$, and that only finitely many factors differ from $1$. Deduce that $\Delta_{\mathbb{A}_f}(a) = \prod_p |a_p|_p$.

*Hint.* Use the proposition $\iota(a) = |O/aO|$ with $O = \widehat{\mathbb{Z}}$. The quotient $\widehat{\mathbb{Z}}/a\widehat{\mathbb{Z}}$ is the product of the groups $\mathbb{Z}_p/a_p\mathbb{Z}_p$. A unit of $\mathbb{A}_f$ has $a_p \in \mathbb{Z}_p^\times$ for almost all $p$.

**Exercise 2.** Let $R = \mathbb{Q}_p \times \mathbb{Q}_p$ and $a = (p, 0)$. Show that $\iota(a) = 0$. Show that multiplication by $a$ sends $\mathbb{Z}_p \times \mathbb{Z}_p$ to a set of Haar measure $0$. So the convention for non-units agrees with the scaling for this $a$. Explain why the theorem $\Delta_{R^n}(g)^{-1} = \iota(\det g)$ does not apply to $g = a$ with $n = 1$.

*Hint.* The element $a$ is a zero divisor, so it is not a unit. The image lies in $\mathbb{Q}_p \times \{0\}$. The theorem needs $g$ invertible.

**Exercise 3.** Let $A$ be a finite abelian group. Show directly that $|\mathrm{Hom}(\mathbb{Z}/n, \mathbb{Q}/\mathbb{Z})| = n$, and deduce $|\mathrm{Hom}(A, \mathbb{Q}/\mathbb{Z})| = |A|$ from the structure theorem. Then show that $A \to \mathrm{Hom}(\mathrm{Hom}(A, \mathbb{Q}/\mathbb{Z}), \mathbb{Q}/\mathbb{Z})$ is an isomorphism.

*Hint.* A homomorphism from $\mathbb{Z}/n$ is fixed by the image of $1$, which must be killed by $n$. For the last part, the map is injective by [the separation lemma](/decl/New.QZ.eq_zero_of_forall_hom_eq_zero/), and both sides have $|A|$ elements.

**Exercise 4.** Let $\psi$ be a character of $\mathbb{Q}_p$ with $\psi = 1$ on $\mathbb{Z}_p$ and $\psi \neq 1$ on $p^{-1}\mathbb{Z}_p$. Let $dx$ be the Haar measure with $\operatorname{vol}(\mathbb{Z}_p) = 1$. Show that $\int_{\mathbb{Z}_p} \psi(ax) \, dx$ is $1$ if $a \in \mathbb{Z}_p$ and $0$ otherwise.

*Hint.* Apply the orthogonality proposition of Section 6 to the character $x \mapsto \psi(ax)$ and the open subgroup $M = \mathbb{Z}_p$. If $a = p^{-k} u$ with $k \geq 1$ and $u$ a unit, then $x = p^{k-1} u^{-1}$ is in $\mathbb{Z}_p$ and $ax = p^{-1}$. Choose $u$ so that $\psi(ax) \neq 1$, using that $\psi$ is not $1$ on $p^{-1}\mathbb{Z}_p$.

**Exercise 5.** Show that Lebesgue measure on $\mathbb{C}^n$ has Gaussian integral $(n, \sum_i |z_i|^2)$. Deduce that
$$\int_{\mathbb{C}^n} (1 + |z|^2)^{-s} \, dz = \frac{\pi^n \, \Gamma(s - n)}{\Gamma(s)} \quad \text{for } s > n.$$
Check the case $n = 1$, $s = 2$ by polar coordinates.

*Hint.* Use the instance for $\mathbb{C}$ and the power case. For $n = 1$ and $s = 2$, both sides are $\pi$.

**Exercise 6.** Show that the zero measure is below every fibre measure. Show that if $l$ is below the fibre measure of $\pi$ over $b$ and $l' \leq l$, then $l'$ is below it too. Give an example where $l$ is below the fibre measure and $l$ is not the fibre measure.

*Hint.* For the first two parts, the conclusion $\int K \, dl' \leq \int K \, dl \leq C$ is monotone in $l$. Compare [the monotonicity lemma](/decl/New.LeFibreMeasure.mono/). For the example take $l = 0$ and $\pi$ the projection $\mathbb{R}^2 \to \mathbb{R}$.

**Exercise 7.** Let $G$ be a finite abelian group and $S$ a set of characters $G \to \mathbb{C}^\times$. Show that
$$e_S = \frac{1}{|G|} \sum_{g \in G} \sum_{\chi \in S} \overline{\chi(g)} \, g$$
is a central projection of $\mathbb{C}[G]$. Show that $|e_S(g)| \leq |S|/|G|$, and compare with the bound $|e(g)| \leq 1$ of Section 8.

*Hint.* Expand $e_S^2$ and use $\frac{1}{|G|} \sum_g \overline{\chi(g)} \chi'(g) = \delta_{\chi\chi'}$. For the bound, each $|\chi(g)| = 1$.

## Notes and references

The congruence subgroups of $\mathrm{SL}_2(\mathbb{Z})$ and their indices are in Diamond and Shurman, *A First Course in Modular Forms*, Section 1.2. The module of an automorphism of a locally compact group is in Weil, *Basic Number Theory*, Chapter I, Section 2, and in Bourbaki, *Intégration*, Chapter VII, Section 1. Elementary divisors over a principal ideal domain are in Lang, *Algebra*, Chapter III, Section 7. Baer's criterion and the injectivity of divisible groups are in Weibel, *An Introduction to Homological Algebra*, Section 2.3. Duality for finite abelian groups is in Serre, *A Course in Arithmetic*, Chapter VI, Section 1. Pontryagin duality for profinite groups is in Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter I, Section 1. The layer cake representation is Lieb and Loss, *Analysis*, Theorem 1.13. Fibre measures are in Weil, *Sur la formule de Siegel dans la théorie des groupes classiques*, Acta Math. 113 (1965), no. 6. The character theory of finite groups follows Serre, *Linear Representations of Finite Groups*, Sections 2.3, 2.5 and 2.6.

The chapter found these points where the register of findings can be made more exact.

First, row F-023 lists global instances, but not those of the files of this chapter. The file on congruence subgroups declares global instances for the topology, the measure and compactness of unitary groups and matrices (Section 3). The file on profinite characters makes the closedness of a topological closure an instance and declares that a compact totally disconnected group is nonarchimedean (Section 4). Row F-026 explains the local instance that turns finiteness into an enumeration, and its list of files does not include the file on finite characters (Section 8). None of these instances adds an axiom.

Second, question Q-68 asks whether $\mathrm{wave}(c) = \exp(c - \bar c)$ agrees with the additive character at the infinite places. The register lists it as open and refers to F-034, which is about a different subject. [The lemma on the rescaled wave](/decl/New.Filling.wave_two_pi_I_mul/) answers the question: $\mathrm{wave}$ is a rescaling of the standard character (Section 6).

Third, two definitions of the chapter are particular to the source and are not connected to Mathlib. [The definition of irreducible character](/decl/New.IsIrreducibleChar/) agrees with the textbook notion by a classical theorem, but the source does not prove the agreement (Section 8). [The class of places](/decl/New.Floors.Place/) is a hypothesis, and the disintegration of quadrics holds for every instance of it, as F-085 says (Section 7).

The Smith form of the source states no divisibility among the diagonal entries, and its docstring says so. The modulus theorem of Section 5 does not need the divisibility.

The plan of the volume and the links to Theorems A, B and C are in [the theorem and the plan](/chapter/theorem-and-plan/). The adeles and the unitary groups are in [the first chapter of this volume](/chapter/adeles-hermitian-spaces/).

Status: drafted by a model. No person has checked this chapter against the Lean source.
