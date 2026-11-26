---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $T$ be a cell of Section 2. Show that $T$ contains a compatible system $(p^{1/p^n})_n$ of $p$-power roots of $p$. Show that this system gives an element $p^\flat$ of the tilt $T^\flat = \varprojlim_{x \mapsto x^p} T/p$, and that $p^\flat$ is neither zero nor a unit.

*Hint.* Absolute integral closure gives roots of $X^p - a$. The component $p^{1/p}$ is not divisible by $p$ in the valuation ring $T$. The component of index $0$ is zero in $T/p \neq 0$.

**Exercise 2.** In the twisted structure of Section 7, let $N = 1$, so $\sigma = \varphi^3$. Check by hand that $p^3$ divides the image of $\mu$ in $A_{\max}$. Where does the proof use the bound $\max(N, 3) \ge 3$?

*Hint.* Write $[\varepsilon] = 1 + \xi \tau$ and expand $\sigma(\mu) = [\varepsilon]^{p^3} - 1$ by the binomial theorem. Each term lies in $(p, \xi)^3$, and $p$ divides the image of $\xi$.

**Exercise 3.** Let $S$ be a ring in which the integers prime to $p$ are units, for example a $p$-complete ring. Show that $p \in \mathfrak{d}(S)$, the ideal of Section 7. Deduce that $\mathfrak{d}(\mathbb{Z}_p) = p \mathbb{Z}_p$.

*Hint.* By Legendre's formula, the $p$-adic valuation of $n!$ is less than $n / (p - 1)$, so at most $n$. A unit $u$ fails the condition at $n = p$.

**Exercise 4.** In the theorem on the congruence relation, take the empty index set. Write down the relation that remains, and explain why `CongruenceRelation` holds. This is the call in `New.Variety.Model.exists_galois_rep`.

*Hint.* The sum over the empty set is $0$ in the free abelian group, and the Weil pair hypothesis is a statement about the empty set.

**Exercise 5.** The proof of the congruence theorem in Section 7 shows that the residue ring $k$ is finite. Let $k$ be a domain, and let $f > 0$ with $z^{p^f} = z$ for every $z \in k$. Prove that $k$ is a finite field with at most $p^f$ elements. Which hypothesis of the theorem gives such an $f$?

*Hint.* Every element of $k$ is a root of $X^{p^f} - X$, and a polynomial over a domain has at most as many roots as its degree. The integer $f$ comes from a Frobenius element of the decomposition group, through a Weil pair of positive degree.

## Notes and references

For the primitive comparison and the role of almost mathematics, the source cites Scholze, *Étale cohomology of diamonds*, arXiv 1709.07343, Theorem 8.7 and Proposition 8.8, and Bhatt and Scholze, Invent. Math. 209 (2017), Theorem 4.1. For the crystalline comparison it cites Faltings (1989) and Bhatt, Morrow and Scholze, Publ. Math. IHÉS 128 (2018), Theorem 1.1(i). For the Frobenius relation it cites Scholl, Invent. Math. 100 (1990), §4.2.3, Katz and Messing, Invent. Math. 23 (1974), Theorem 2(2), and Berthelot and Ogus, Invent. Math. 72 (1983). The Künneth argument of Section 4 is a form of the Leray-Hirsch theorem, Hatcher, *Algebraic Topology*, Theorem 4D.1.

The treatment differs from the literature in three ways. There are no sites or sheaves, only functors on categories of test rings. The comparisons are stated with existential maps and bijections on cohomology, not with natural isomorphisms of cohomology theories. The period ring of the crystalline part is Colmez's $B_{\max}$, not Fontaine's $B_{\mathrm{cris}}$, and the source does not compare the two. The comparison on charts works one coordinate at a time, through the root systems of one unit, as in the line lemma that the source attributes to Andreatta and Brinon, Comment. Math. Helv. 88 (2013). The results are the minimum that `Lib/Shimura/Eigenspace.lean` needs: there is no integral form, no Hodge-Tate decomposition and no identification with crystalline cohomology.

The findings of this chapter are the following.

1. The notes of the plan say that `New.Variety.Model.exists_galois_rep` uses the Woods Hole formula at line 458 and the crystalline result at line 674 of `Lib/Shimura/Eigenspace.lean`. These lines are in two lemmas that it calls: line 458 is in `New.Variety.Model.isNullHecke_mul_of_kills_weight`, and line 674 is in `New.Variety.Model.isKilledBy_heckePoly_of_isEigenQuotient`. The theorem itself uses the crystalline result at lines 743 to 746 and `New.Variety.ellAdicCohom.continuous_galoisAction` at line 737. The notes do not list `New.Variety.exists_hasHodgeTateWeight` (line 461) or the continuity result.
2. The finiteness theorem `New.Variety.finite_padic_cohomology` uses almost descent only with the trivial module $N = \mathrm{Unit}$.
3. The period map `New.Variety.exists_period_map` is bijective, but the Hodge-Tate map $\lambda_h$ is not proved injective or bijective (finding F-056 of the plan). The two must be kept apart.
4. A $p$-adic test is a nonempty product of cells, and the product can be infinite.
5. The operator `New.Period.linearFrob` is a `Classical.epsilon` value. The relation of Section 7 has content only because the same theorem proves that the representation is crystalline.

Status: drafted by a model. No person has checked this chapter against the Lean source.
