---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $|n| = 2$ and let a spherical vector at the split place $w$ have an exponent for unramified characters $\theta_0, \theta_1$, with $\alpha = \theta_0(\varpi)$ and $\beta = \theta_1(\varpi)$. Show that its Hecke polynomial is $X^2 - (\alpha + \beta) X + \alpha\beta$.

*Hint.* By Section 2, $t_0 = 1$, $t_1 = \alpha + \beta$ and $t_2 = q_w^{-1} \alpha\beta$. Put these in $t_0 X^2 - t_1 X + q_w t_2$.

**Exercise 2.** Let $\rho : \Gamma_E \to \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ be continuous and semisimple, and let $S$ be a finite set of places with $\det(X - \rho(s)) = \iota_\ell(P_w)$ for every $w \notin S$ and every geometric Frobenius $s$ at a place over $w$. Write out in full the proof that $\rho$ is attached to $P$ in the sense of Section 4, with $j$ the identity. At which places do you use the hypothesis?

*Hint.* Condition 2 is the Example of Section 4 on semisimple representations, and condition 3 holds since the identity is open. For condition 4, apply `New.eventually_mostFrobenii` (Section 3) to the property "$w \notin S$". The difference in condition 4 is then $0$, which is at most $\eta$. You use the hypothesis only at places of prime norm.

**Exercise 3.** Let $a : G \to k$ be a nonzero additive character, and let $r(g) = \begin{pmatrix} 1 & a(g) \\ 0 & 1 \end{pmatrix}$. Show that $r$ does not have a non-degenerate trace form. Show that $r$ and the trivial representation of dimension $2$ have the same trace and are not conjugate. Which hypothesis of the Brauer-Nesbitt theorem of Section 7 fails?

*Hint.* The matrix unit $e_{12}$ is $(r(g) - 1)/a(g)$ for $g$ with $a(g) \neq 0$, so it is in the span. Compute $\mathrm{tr}(e_{12}\, r(g))$.

**Exercise 4.** Compute the Newton polynomials $N_{2,1}$ and $N_{3,1}$ of Section 7. Check that $N_{2,1}(p) = 2 e_2$ and $N_{3,1}(p) = 6 e_3$ for the power sums $p$ of a multiset. For $|n| = 1$, which trace identity is $N_{2,1}$?

*Hint.* $N_{1,m} = X_m$, $N_{2,m} = X_m X_1 - X_{m+1}$, so $N_{2,1} = X_1^2 - X_2$ and $N_{3,1} = X_1^3 - 3 X_1 X_2 + 2 X_3$. For a $1 \times 1$ matrix $x$, the identity says $\mathrm{tr}(x)^2 = \mathrm{tr}(x^2)$.

**Exercise 5.** Let $X$ be a Hausdorff space and let $f, h : \Gamma_E \to X$ be continuous. Suppose that $f(s) = h(s)$ for most Frobenius data $(w, A, s)$. Show that $f = h$. Deduce that two attached representations of Section 4 have the same trace.

*Hint.* The set where $f = h$ is closed, since $X$ is Hausdorff. By the density theorem of Section 3, it is dense. For the second part, compare with `New.GaloisRep.Attached.trace_eq` of Section 4, which uses the limits along $\mathcal{F}_E(g)$ in place of density.

## Notes and references

The definition of this chapter is `New.GaloisRep.Attached` in `Lib/GaloisRep/Main/AttachedRepresentations.lean`, with the filter `New.mostFrobenii` of `Lib/GaloisRep/Main/Defs.lean`. The local conditions are `New.GaloisRep.IsCompatibleAt` and its parts, and the rank-one comparison is in `Lib/GaloisRep/Main/AttachedRepresentations.lean`. The pseudocharacter results of Section 7 are in `Lib/GaloisRep/Pseudocharacter/`.

The textbook notion of a Galois representation attached to an eigenform, with "all Frobenius elements at almost all places", is the one of the classical theory. The source does not cite a reference for it, and this chapter does not either. For Brauer-Nesbitt in the finite case, see Serre, *Linear Representations of Finite Groups*, Section 2.3, Theorem 4, Corollary 2. For pseudo-representations, the source cites R. Taylor, *Galois representations associated to Siegel modular forms of low weight*, Duke Math. J. 63 (1991), Theorem 1, and R. Rouquier, *Caractérisation des caractères et pseudo-caractères*, J. Algebra 180 (1996), and a note of K. Conrad. The source proves a weak form of the theorem of Procesi and Taylor, in which all trace identities are hypotheses.

The chapter addresses four items of the [register of findings](/chapter/register-of-findings/).

1. F-049. The representation of an isotypic component, `New.Patching.Isotypic.galRep`, is an epsilon object (Section 4). If no attached representation exists, its value is junk. The choice of the eigenvalues before it is a second choice.
2. F-053. "Attached" is an approximate condition along the filter of most Frobenius data (Sections 3 and 4). The filter is strictly larger than the textbook family of sets, and the textbook notion implies the source notion (Exercise 2). The converse is not stated in the source.
3. F-054. `GalRep` has no continuity clause, and the local conditions ask that a polynomial kills the Frobenius element, not that it is the characteristic polynomial; there is no monodromy operator (Section 5).
4. Q-59. The question whether the source needs exact characteristic polynomials or Frobenius semisimplicity beyond `Attached` and `PolyKillsAt` stays open. Section 5 states the one result that upgrades "kills" to equality, `New.card_eq_and_charpoly_eq`, and its use in `Lib/GaloisRep/Main/SeedRepresentation.lean`. This chapter does not check every use of the local conditions.

Question Q-46 asks whether "most Frobenii" is used only through Chebotarev, or with a finite set that may depend on a twist. The definition lets the finite set of exceptional places depend on the open set and on $\eta$ (Sections 3 and 4). This chapter does not settle the question.

The research note g, Section 9, has one error. It says that the existence of a local datum at a place "is proved (`exists_inducesPlace`)". That lemma takes the embedding as a hypothesis. The existence of the embedding is `New.exists_comap_intQpBar_eq` (Section 5).

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
