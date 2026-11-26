---
title: Exercises
lean:
  - Lib/General/Algebra/FittingIdealsAndLengths.lean
  - Lib/General/Algebra/BlockFittingBound.lean
  - Lib/General/NumberTheory/CoefficientRings.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $R = \mathbb{Z}_p$ and let $N \subseteq R^2$ be spanned by $(p^2, 0)$ and $(0, p)$. Compute $\operatorname{Fitt}(N)$. Let $v = (p, 0)$. Check that $p v \in N$, compute $\operatorname{Fitt}(N + R v)$, and verify the proposition on adding one vector of Section 5 with $r = p$. Show that no $r$ of smaller valuation works.

*Hint.* $\operatorname{Fitt}(N) = (p^3)$ and $\operatorname{Fitt}(N + R v) = (p^2)$. If $r p^2 \in (p^3)$, then $p \mid r$.

**Exercise 2.** Prove the reverse of the base change inclusion: $\operatorname{Fitt}(N) \subseteq \operatorname{Fitt}(N + I R^\iota)$. Conclude that $\operatorname{Fitt}(N + I R^\iota) + I = \operatorname{Fitt}(N) + I$, which is the statement of Stacks Tag 07ZA for $R \to R/I$.

*Hint.* The Fitting ideal is monotone in $N$.

**Exercise 3.** Let $R$ be an $\ell$-adic integer ring. Find modules $X$ and $Y$ with $\operatorname{Nat.card} X \leq \operatorname{Nat.card} Y$ and $\operatorname{len} X > \operatorname{len} Y$. Which hypothesis of `New.length_le_of_card_le` fails? Show that the same pair does not contradict `New.length_le_of_card_dvd`.

*Hint.* Take $X = R$ and $Y = 0$. Then $\operatorname{Nat.card} X = 0$.

**Exercise 4.** In the main theorem of Section 5, take $V$ to be all functions $G \to O/p$. Show that the relative length in property 1 is $0$, so $c$ is a unit. Show directly that $K = N$ satisfies property 2 in this case.

*Hint.* Every $\Psi$ has $\Psi \circ z \in V$. A vector $v$ killed by every linear $\Psi \colon O^n \to O/p$ lies in $p O^n$, and $\Phi(p O^n) \subseteq N$.

**Exercise 5.** Take $A = M_2(O)$, $\psi$ the identity, $\iota$ a point, and $N = A t$ for a matrix $t$ with $\det t \neq 0$. Show that the solutions $w \in (K/O)^2$ of $t w = 0$ form a module of length $v(\det t)$. Conclude that the divisible form of Section 6 is sharp in this case.

*Hint.* Put $t$ in diagonal form with invertible matrices, and use that the $a$-torsion of $K/O$ is $\operatorname{divQuot}_a(O/a)$.

**Exercise 6.** Let $\ell$ be odd and $O$ the ring of integers of $\mathbb{Q}_\ell(\sqrt{\ell})$. Show that $O$ is a coefficient ring. Compute $\operatorname{addVal}_O(\ell)$, $v(\varpi_O)$, and the normalized lengths of $O/\ell$ and of $O/\varpi_O$.

*Hint.* A quadratic extension is Galois. $\varpi_O = \sqrt{\ell}$ up to a unit, $\operatorname{addVal}_O(\ell) = 2$, $v(\varpi_O) = 1/2$. The normalized lengths are $1$ and $1/2$.

**Exercise 7.** Let $\ell$ be odd, $\alpha = 1 + \ell \in \mathbb{Z}_\ell$ and $N \geq 1$. Compute $v\bigl(\sum_{i < \ell^N} \alpha^i\bigr)$ and compare it with `New.Selmer.pow_dvd_geom_sum` for $r = 1$.

*Hint.* The sum is $((1 + \ell)^{\ell^N} - 1)/\ell$, and $v((1+\ell)^{\ell^N} - 1) = N + 1$. The valuation is $N$, so the lemma is sharp here.

## Notes and references

Fitting ideals are due to Fitting, *Die Determinantenideale eines Moduls*, Jahresbericht der DMV 46 (1936). The standard modern reference is Eisenbud, *Commutative Algebra with a View Toward Algebraic Geometry*, Section 20.2, which proves that the ideals do not depend on the presentation. The base change rule is The Stacks Project, Tag 07ZA. The product rule for exact sequences and the use of Fitting ideals for Iwasawa modules and Selmer groups are in Mazur and Wiles, *Class fields of abelian extensions of $\mathbb{Q}$*, Invent. Math. 76 (1984), Appendix. Ribet's method of making unramified extensions from congruences is in Ribet, *A modular construction of unramified $p$-extensions of $\mathbb{Q}(\mu_p)$*, Invent. Math. 34 (1976). Lengths and discrete valuation rings are in Atiyah and Macdonald, *Introduction to Commutative Algebra*, Chapters 6 and 9. The theorem on elementary divisors is in Lang, *Algebra*, Chapter III, Section 7. Local fields are in Serre, *Local Fields*, Chapters I and II.

This treatment differs from the textbooks in four ways. The Fitting ideal is defined for a fixed free module, and only the inclusions that the argument uses are proved. The bound of a Fitting ideal by a length is relative and dual: it measures the change of the ideal by forms modulo $p$, not the ideal itself. The theorem on elementary divisors is used without the divisibility of the diagonal entries. Lengths over different coefficient rings are compared through the normalized length $\lambda_O$, not through a fixed ring.

The files cite their sources in a section "Relation to the literature". For `FittingIdealsAndLengths.lean` this names Stacks Tag 07ZA and the three properties of Section 5. For `BlockFittingBound.lean` and `SharpMinors.lean` it names only "elementary divisors".

The review of the chapter found these points. They do not change any statement of the source.

1. `Lib/General/NumberTheory/CoefficientRings.lean` lowers, at line 30, the instance priority of six Mathlib instances on subalgebras for every importing file, not only for itself (Section 7).
2. The theorem on elementary divisors of the source has no divisibility of the diagonal entries (Section 4). No proof needs it.
3. Three results are not used by name in `New`: `New.Selmer.exists_rows_addVal_det_le`, `New.Selmer.fittingIdeal.mul_mem_of_smul_mem` and `New.exists_matrix_addVal_det_le_length`. Each one is used in a proof in `Lib`, so none is dead code.
4. The plan line of this chapter, "the algebra for Selmer bounds", and the single bullet in research note h §4 describe a smaller scope than the chapter source in `volume.yaml`, which is all of `Lib/General/Algebra` and `Lib/General/NumberTheory`. The `source` line of the volume names `Lib/General/Algebra` but not `Lib/General/NumberTheory`.

### A summary of Volume 7

Volume 7 describes the cohomology and $p$-adic Hodge theory of the source. [Schemes through their points](/chapter/schemes-through-points/) gives schemes as functors on rings, line bundles, the Picard group, projective embeddings and a case of Serre's theorem. [Cohomology as Ext on test rings](/chapter/cohomology-ext/) defines $\ell$-adic cohomology as an Ext group of sheaves on test rings, with base change, Hodge cohomology and the Woods Hole formula. [Period rings](/chapter/period-rings/) gives $A_{\inf}$, $B_{\max}$ and $B_{\mathrm{dR}}^+$, admissibility, Hodge and Tate jumps and the Bloch and Kato rank formula. [Kisin frames](/chapter/kisin-frames/) gives Kisin frames and limits of crystalline representations. [The comparison theorems](/chapter/comparison-theorems/) proves almost descent, the primitive comparison, the Hodge and Tate map and the crystalline comparison on test objects. This chapter gives the commutative algebra for Selmer bounds.

The cost of the volume is the same in each chapter. The cohomology of the source is never compared with étale cohomology. "Crystalline" means admissible for $B_{\max}$, not for $B_{\mathrm{cris}}$. The source proves the properties it uses for its own objects and imports no theorem stated for the classical objects. The cohomology reaches the main argument through one chain of declarations, while the algebra of this chapter reaches it through many short uses in Volume 12. The volume explains what the source claims. It does not say that the claims are correct.

Status: drafted by a model. No person has checked this chapter against the Lean source.
