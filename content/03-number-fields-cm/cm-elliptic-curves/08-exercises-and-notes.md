---
title: Exercises and notes
lean:
  - Lib/CM/Sigma/Basic.lean
  - Lib/CM/ConjugateCurve.lean
  - Lib/CM/KroneckerLimit.lean
  - Lib/CM/ChowlaSelberg.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

In these exercises $d$ is a prime with $d \equiv 7 \pmod 8$, $K = \mathbb{Q}(\sqrt{-d})$ and $\omega = (1 + \sqrt{-d})/2$, as in the chapter.

**Exercise 1.** Let $E : y^2 + a_1xy = x^3 + x$. Compute the invariants $b_2$, $b_4$, $b_6$, $b_8$ of $E$ and show that $\Delta(E) = a_1^4 - 64$. Then show that $c_4 = a_1^4 - 48$ and $j(E) = (a_1^4 - 48)^3/(a_1^4 - 64)$. Compare with [the discriminant](/decl/New.CMLattice.disc_eq/) of Section 3.

*Hint.* Here $a_2 = a_3 = a_6 = 0$ and $a_4 = 1$. The standard formulas (Silverman, *The Arithmetic of Elliptic Curves*, Chapter III, §1) give $b_2 = a_1^2$, $b_4 = 2$, $b_6 = 0$ and $b_8 = -1$. Then $\Delta = -b_2^2b_8 - 8b_4^3 - 27b_6^2 + 9b_2b_4b_6$ and $c_4 = b_2^2 - 24b_4$.

**Exercise 2.** Let $L$ be the lattice of a CM lattice, with its point $t$ of order $2$. Show that $s_L(t) = a_1^4 - 64$, where $s_L(u) = 288\wp(u)^2/\wp''(u) - 64$ is [the scaled discriminant](/decl/PeriodPair.scaledDisc/) of Section 4. For $d = 7$, take $s_L(t) = -1$ as in Section 4. Use the sum $-48$ and the product $-2^{12}$ of the three values of $s_L$ to find the other two values. Deduce $a_1^4 = 63$ and $j = -3375$.

*Hint.* At $t$ one has $\wp''(t) = 2$ and $\wp(t) = a_1^2/12$. So $288\wp(t)^2/2 = a_1^4$. The other two values $s'$, $s''$ satisfy $s' + s'' = -47$ and $s's'' = 2^{12}$. The discriminant of $X^2 + 47X + 4096$ is $-14175 = -7 \cdot 45^2$. Use Exercise 1 for $j$.

**Exercise 3.** Let $\omega \in \mathbb{C}$ with $|\omega| > 1$, and suppose that $\omega^n = \omega\bar\omega$ for an integer $n \ge 1$. Show that $n = 2$ and that $\omega$ is real. Explain how this gives [the equality](/decl/New.CMLattice.thetaQuotient_eq_one/) $\hat\theta_D = \sigma\theta_C$ in Section 6. Check the case $d = 7$, where $\omega\bar\omega = 2$.

*Hint.* Take absolute values: $|\omega|^n = |\omega|^2$ and $|\omega| > 1$ give $n = 2$. Then $\omega^2 = \omega\bar\omega$ and $\omega \ne 0$ give $\omega = \bar\omega$. In Section 6, $q - 1 = z^nW$ with $W(0) \ne 0$, and the coefficient of $z^n$ in $q(\omega z) = q(z)^N$ gives $\omega^n = N$.

**Exercise 4.** For $d = 7$, write the Euler factors of $\zeta_K(s)$ at $p = 2$, $p = 3$ and $p = 7$. Check in each case that the factor is $(1 - p^{-s})^{-1}(1 - \chi(p)p^{-s})^{-1}$, as in [the factorisation](/decl/New.QuadField.eulerProd_one_eq_zeta_mul/) of Section 7. Explain why $p = 2$ splits for every prime $d \equiv 7 \pmod 8$.

*Hint.* The squares modulo $7$ are $1$, $2$, $4$. So $\chi(2) = 1$ and $\chi(3) = -1$. The minimal polynomial of $\omega$ is $X^2 - X + (d + 1)/4$, and $(d + 1)/4$ is even for $d \equiv 7 \pmod 8$. So the polynomial factors as $X(X - 1)$ modulo $2$.

**Exercise 5.** Let $L$ be a lattice and $k > 0$, and let $F$ be the function of [Kronecker's formula](/decl/New.kronecker_limit/). Show that the sum $\sum_l (|l|^2/(kA))^{-s}$ does not change if $L$ is replaced by $cL$, $c \in \mathbb{C}^\times$. Show that the right derivative $F(1)(2\gamma - \log(A/(k\pi^2)) - \frac16\log|\Delta|)$ does not change either. Then derive the case of general $k$ from the case $k = 1$.

*Hint.* Under $L \mapsto cL$, $|l|^2$ and $A$ scale by $|c|^2$, and $\Delta$ scales by $c^{-12}$. For the last part, the sum for $k$ is $k^s$ times the sum for $k = 1$, and $(s - 1)k^s \cdot \pi/(s - 1) = \pi k^s$ has the derivative $\pi k\log k$ at $s = 1$.

**Exercise 6.** Let $d = 23$, so $h = 3$ and the class group is $\{1, \mathcal{C}, \mathcal{C}^2\}$. Choose ideals $\mathfrak{b}_1 = (1)$, $\mathfrak{b}_{\mathcal{C}}$ and $\mathfrak{b}_{\mathcal{C}^2}$ in these classes. Write out the ideals $\mathfrak{c}_{\mathcal{C}'} = \mathfrak{b}_{\mathcal{C}'^2}/\mathfrak{b}_{\mathcal{C}'}$ of [the lemma](/decl/New.QuadField.exists_mk_eq_and_prod_eq_one/) of Section 7, and check that their product is $(1)$. Why does this construction fail for a class group of even order?

*Hint.* Squaring maps $\mathcal{C} \mapsto \mathcal{C}^2$ and $\mathcal{C}^2 \mapsto \mathcal{C}^4 = \mathcal{C}$. The product is $\prod \mathfrak{b}_{\mathcal{C}'^2}/\prod \mathfrak{b}_{\mathcal{C}'}$. For even order, squaring is not a bijection of the class group, so the numerator need not be a rearrangement of the denominator.

**Exercise 7.** Show that a number $x \in \mathbb{C}$ with $|\iota(x)| = 1$ for every ring homomorphism $\iota : \mathbb{C} \to \mathbb{C}_p$ is algebraic. Explain why this does not give the algebraicity of the unit $u$ of [the formula of Chowla and Selberg](/decl/New.CMLattice.chowla_selberg/) in the source, and what would be needed.

*Hint.* If $x$ is transcendental, extend $x \mapsto p$ to a field embedding $\mathbb{Q}(x) \to \mathbb{C}_p$, and then to $\mathbb{C}$, by a transcendence basis and the algebraic closedness of $\mathbb{C}_p$. The source states the unit property only for embeddings with the class `New.PadicPlace`, and it does not prove the step above in Lean.

## Notes and references

The classical theory of complex multiplication is in J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Graduate Texts in Mathematics 151, Springer, 1994, Chapter II. The main theorem is Theorem 8.2 there. The idelic form is in G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Princeton, 1971, Theorem 5.4, and in J. S. Milne, *Complex Multiplication* (notes, 2020), 9.17. The source cites both for its soft main theorem. The basic theory of elliptic curves is in J. H. Silverman, *The Arithmetic of Elliptic Curves*, Graduate Texts in Mathematics 106, Springer. Kronecker's first limit formula is in C. L. Siegel, *Lectures on Advanced Analytic Number Theory*, Tata Institute, 1961, Chapter I, Theorem 1. The proof of the source follows the shape of F. Chamizo, Ramanujan J. (2022), Proposition 3.1. The formula of Chowla and Selberg is in A. Selberg and S. Chowla, *On Epstein's zeta-function*, J. reine angew. Math. 227 (1967), 86 to 110. The source also cites B. Gross, *On the periods of abelian varieties*, arXiv 2005.04194. The factorisation of $\zeta_K$ and the partial zeta functions are in J. Neukirch, *Algebraic Number Theory*, Springer, 1999, Chapter VII. The odd class number is due to Gauss. The source cites D. Cox, *Primes of the Form x² + ny²*, Wiley, 1989, §3 and §6. For the good reduction the source cites D. Kubert and S. Lang, *Modular Units*, and B. Birch, *Weber's class invariants*, Mathematika 16 (1969).

The source differs from the classical theory in its order. It does not start from the algebraic curve. It starts from a lattice $\Lambda$ with a point of order $2$, normalised so that the model is $y^2 + a_1xy = x^3 + x$. All arithmetic comes from the theta function $\theta$ and its translates: good reduction from the cycle of $2$-isogenies (Section 4), integrality from the doubling forms (Section 5), and the Galois action from the transport of Taylor series (Section 6). The reciprocity law of [class field theory](/chapter/class-field-theory/) and the Hecke character of the curve are not used, and the source does not state them. The fields of [the previous chapter](/chapter/cm-fields/) supply $K$ and its places. The Galois side, with the CM splitting characters, is in [local duality](/chapter/local-duality/). The formal groups of Section 5 return in Volume 9, in [the CM formal group](/chapter/cm-formal-group/).

Junk values and choices in this chapter, in summary:

1. A CM lattice for $d = 0$ has no conditions of complex multiplication (Section 3). The source uses this as an intermediate step in Section 6.
2. The sigma function and the conjugate $C^\sigma$ are chosen by `choose` (Sections 3 and 6). The theta function and the lattice of $C^\sigma$ do not depend on the choice.
3. The adele $\beta$ of the soft main theorem is a cluster point. It is not shown to be a unit or to be the Artin map (Section 6).
4. In Kronecker's formula, only real $s \in (1, 2)$ occur, and the term $l = 0$ is $0^{-s} = 0$ (Section 7).
5. `Nat.card` of the units is $0$ for a field with infinitely many units. This does not occur for $K$ (Section 7).
6. The unit $u$ of Chowla and Selberg is a chosen $12h$-th root. It is a unit at every embedding into $\mathbb{C}_p$, and it is not shown to be algebraic (Section 7, finding F-064 of the spec). In Volume 9 it is fixed by `choose` as `New.Parameters.chowlaSelbergUnit`.

The constant $C_d = \gamma - \operatorname{Re} L'/L(1, \chi_K)$ of Chowla and Selberg enters Volume 1 in [the weighted prime remainder](/chapter/weighted-prime-remainder/), and the unit and the complex multiplication data enter Volume 9 in [the integral vacuum](/chapter/integral-vacuum/).
