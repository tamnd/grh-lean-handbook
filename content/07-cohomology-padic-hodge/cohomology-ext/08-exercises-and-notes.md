---
title: Exercises and notes
lean:
  - Lib/Cohomology/WoodsHole.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $A$ be an object of a category $\mathcal{C}$ and let $h_A$ be the represented space of Section 2. Show that $\mathbb{Z}[h_A]$ is a projective object of $\operatorname{Fun}(\mathcal{C}, \mathbf{Ab})$. Deduce that $H^n(h_A, F) = 0$ for every coefficient $F$ and every $n > 0$, and that $H^0(h_A, F) \cong F(A)$.

*Hint.* By the additive Yoneda lemma, $\operatorname{Hom}(\mathbb{Z}[h_A], -)$ is evaluation at $A$. Evaluation is exact, because kernels and cokernels of functors are computed objectwise.

**Exercise 2.** Let $A_1$ and $A_2$ be test rings. Composition with the two projections gives a map $h_{A_1} \sqcup h_{A_2} \to h_{A_1 \times A_2}$ of spaces over rings. Show that this map induces bijections on $H^n(-, \Lambda)$ for all $n$, where $\underline{\Lambda}$ is the coefficient of locally constant functions of Section 3. Is the map an isomorphism of spaces?

*Hint.* Use Exercise 1 on both sides, with $\mathbb{Z}[h_{A_1} \sqcup h_{A_2}] = \mathbb{Z}[h_{A_1}] \oplus \mathbb{Z}[h_{A_2}]$. Then use $\operatorname{Spec}(A_1 \times A_2) = \operatorname{Spec} A_1 \sqcup \operatorname{Spec} A_2$. For the last question, evaluate both sides at $B = A_1 \times A_2$ and look at the identity map.

**Exercise 3.** Let $W = Y = \mathbb{P}^1$ over a field of characteristic $0$, with $c = \mathrm{id}$ and $u(z) = 1/z$. Find the fixed points, the tangent polynomials and the local terms of weights $h = 0$, $1$ and $2$, in the form $\operatorname{coeff}_h(P)/P(1)$ of Section 7. Compare with the classical values for $h = 0$ and $h = 1$.

*Hint.* The fixed points are $1$ and $-1$, and the derivative is $-1$ at both. So $P(t) = 1 + t$ at both points, and the sums are $1$, $1$ and $0$. Classically, the value for $h = 1$ is $-1$, by the sign $(-1)^h$.

**Exercise 4.** Let $P$ be a tangent polynomial of rank $d$ with $P(1) \neq 0$. Show three facts. (a) $P(0) \neq 0$. (b) The local term $\operatorname{coeff}_h(P)/P(1)$ does not change if $P$ is multiplied by a nonzero scalar. (c) The local term is $0$ for $h > d$.

*Hint.* Use the identity $P(t) = P(0)\det(1 - tB)$ for all $t$. For (c), $\det(1 - tB)$ is a polynomial function of degree at most $d$ in $t$. Over an infinite field a polynomial is determined by its function.

**Exercise 5.** Let $d \geq 1$, and suppose that $c = u_i$ for some $i$ with $a_i \neq 0$, and that $W$ has a $k$-point. Show that no tangent polynomial $P$ of $c$ and $u_i$ at a $k$-point has $P(1) \neq 0$. Explain why the condition of Definition 7.11 then holds for this $c$ without content.

*Hint.* From $c(f(x)) = c(f(Bx))$ and the injectivity of $x \mapsto c(f(x))$, deduce $B = 1$. Then $\det(1 - B) = 0$. The definition is an implication whose premise fails.

**Exercise 6.** Let $k = \mathbb{F}_p$ and $h = 1$. Show that no linear form $L$ on the functions $k \to k$ has the property of Lemma 7.13. Then explain why the field $k$ of Theorem 7.12 meets the hypothesis of Lemma 7.13.

*Hint.* The functions $t \mapsto t^p$ and $t \mapsto t$ are equal on $\mathbb{F}_p$, but the coefficients of $X$ in $X^p$ and in $X$ differ. In Theorem 7.12 the field $k$ is algebraically closed, so it is infinite.

## Notes and references

The definition of cohomology as Ext in a category of functors on test objects is the frame of the source. For Ext in abelian categories and the Yoneda description, see C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced Mathematics 38, Cambridge University Press, 1994, Chapter 3. The classical proper base change theorem is SGA 4, Exposé XII, and the classical smooth base change theorem is SGA 4, Exposé XVI (M. Artin, A. Grothendieck and J.-L. Verdier, Lecture Notes in Mathematics 305, Springer, 1973). The source replaces both with statements on test rings, and Sections 4 and 5 compare the forms. The Leray-Hirsch theorem in topology is Theorem 4D.1 of A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002.

The holomorphic Lefschetz formula is in M. F. Atiyah and R. Bott, A Lefschetz fixed point formula for elliptic complexes II, Ann. of Math. 88 (1968) 451-491. The source also cites G. Kondyrev and A. Prikhodko, Holomorphic Atiyah-Bott formula for correspondences, Arnold Math. J. (2022), and SGA 5, Exposé III, 6.12. For the diagonal class and the transformation law of Grothendieck symbols, the source cites the Stacks Project (tags 0BEC and 0G82), A. Chatzistamatiou and K. Rülling, Algebra Number Theory 5 (2011) 693-775, Sections 2 and 3, V. Srinivas, Proc. Indian Acad. Sci. Math. Sci. 103 (1993) 209-247, and R. Hartshorne, *Residues and Duality*, Lecture Notes in Mathematics 20, Springer, 1966, Chapter III, Section 9. This chapter has not checked that each of these citations matches the statement that it supports.

The source states only the vanishing half of the Woods Hole formula, and it computes no trace. It states no comparison of its cohomology with étale or coherent cohomology. Chapter 1 of this volume (/chapter/schemes-through-points/) treats schemes through their points. The Hodge-Tate map comes from /chapter/comparison-theorems/. The findings F-020, F-021, F-023, F-051, F-108, F-109 and F-112 of /chapter/register-of-findings/ concern this chapter. They cover the settings and instances, the junk values, and summaries of the source that say more than the Lean statements. The place of these results in the plan of the source is described in /chapter/theorem-and-plan/.

Status: drafted by a model. No person has checked this chapter against the Lean source.
