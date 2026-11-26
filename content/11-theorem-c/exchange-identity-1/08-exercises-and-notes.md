---
title: Exercises and notes
lean:
  - New/Determinant/Exchange/LargeTriple.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of Sections 2 to 7.

**Exercise 1.** Let $n = 2$, $b = a = 1$, and $k \in GL_2(O)$. Write $k^{-1}$ with the adjugate of $k$. Check by hand that the last row $x_k$ of $k^{-1}$ and the first column $y_k$ of $k$ satisfy $x_k y_k = 0$ and $\det(s; x_k) \det k = s\, y_k$ for every row $s$.

*Hint.* $k^{-1} = (\det k)^{-1}\operatorname{adj}(k)$, and the last row of $\operatorname{adj}(k)$ is $(-k_{21}, k_{11})$.

**Exercise 2.** Let $s x = 1$ with $s$ of size $b \times n$ and $x$ of size $n \times b$. Show that $e = x s$ and $1 - e$ are idempotents with $e(1 - e) = 0$. Deduce that $d = \varpi^{-c}(1 - e) + e$ has inverse $\varpi^{c}(1 - e) + e$, and that $s d = s$ and $d x = x$.

*Hint.* Expand $e^2 = x(sx)s$.

**Exercise 3.** Let $R$ be a finite field, $\eta$ a nontrivial character of $R^\times$, extended by $\eta(0) = 0$, and $\varphi$ a nontrivial additive character. Show that $\sum_{r \in R} \eta(r)\varphi(Tr) = 0$ for $T = 0$, and that its absolute value is $\sqrt{|R|}$ for $T \neq 0$. Compare with the lemma on Gauss sums of matrices in Section 5 for $b = 1$.

*Hint.* For $T = 0$ the sum is $\sum_r \eta(r)$. For $T \neq 0$ expand the square of the absolute value and sum over $r$ first.

**Exercise 4.** Let $r$ be a unit vector in $\mathbb{C}^n$ and $P = r^* r$. Show that $\det(1 + \lambda P) = 1 + \lambda$, and that $(1 + \lambda P)^{-1} = 1 - \lambda(1 + \lambda)^{-1}P$ for $\lambda \neq -1$. For $\lambda = \bar\eta - 1$ with $|\eta| = 1$, compare with the formula $c^{-1} = 1 + (\eta - 1)P$ of Section 6.

*Hint.* $P^2 = P$, and $\det(1 + uv) = 1 + vu$ for a column $u$ and a row $v$.

**Exercise 5.** Let $g$ be a polynomial in one variable with $g(0) = 0$. Show that the mean of $g$ over the unit circle is $0$. Then let $P$ be a polynomial in one variable $X$, $N \geq 1$, and suppose that $P(X) = \eta^N P(\eta X)$ for all $|\eta| = 1$. Show that $P = 0$, as in the weight argument of Section 6.

*Hint.* Compare the coefficients of $X^j$: $c_j = \eta^{N+j}c_j$ for all $\eta$ on the circle.

**Exercise 6.** Let $\mu_w > 0$, $n$ even, and $2\operatorname{neg}(s) \leq n$. Show that $n/2 - \mu_w < n - \operatorname{neg}(s)$. Explain why this inequality is the weight hypothesis of the theorem of Section 6 for the large triple, with $t' = -1$.

*Hint.* $n - \operatorname{neg}(s) \geq n/2$. The space $W_1$ plays the part of $Z$, and $V' \oplus W_1$ has $b + \operatorname{neg}(s)$ negative signs.

**Exercise 7.** In part 3 of the theorem on the exchange from periods, let $m = 2b + n$ with $n$ even. Check that $\operatorname{card}(b \sqcup n) - \lfloor m/2 \rfloor = n/2$, and that the constant $K^{-2}$ makes condition (a) of the row-column exchange identity hold for every $\mathfrak{c}$.

*Hint.* Use $\|C_{\mathfrak{c}}\| = K\|I(\mathfrak{c})\|$.

## Notes and references

**Matched functions.** The matching of Section 2 is an identity of linear algebra over $O$: the rows of $k^{-1}$ and the columns of $k$ satisfy the relations of Jacobi between the minors of a matrix and of its inverse.

**Seesaw.** The exchange identity compares the theta integrals of $(X, V' \oplus W_1)$ and $(X, V')$. This is the shape of a seesaw identity: S. Kudla, *Seesaw dual reductive pairs*, in Automorphic forms of several variables, Progr. Math. 46, Birkhäuser (1984). The source does not use the seesaw principle. It proves the identity on standard data by the vanishing criterion of Section 5 and the period identity of Section 7.

**Singular forms.** The vanishing criterion of Section 5 rests on the theory of Fourier coefficients of singular forms along a frame, in the version of [singular forms](/chapter/rallis-inner-product/#singular-forms) in Volume 6. For the classical theory of singular modular forms see E. Freitag, *Singular modular forms and theta relations*, Lecture Notes in Math. 1487, Springer (1991).

**Hermitian forms.** The Hasse principle for hermitian forms over a quadratic extension of number fields, used in the lemma of Landherr in Section 5, is due to W. Landherr, *Äquivalenz Hermitescher Formen über einem beliebigen algebraischen Zahlkörper*.

**Fock model.** The weight argument of Section 6 uses the Fock model of the Weil representation at the real places, of [Volume 6](/chapter/weil-representation/). The circle of rotations in the stabiliser of a frame acts on polynomial vectors with positive weights only, and the mean value property kills every invariant functional.

**Constants.** The constant $K^{-2}$ of Section 7 is not computed. The chain of the plan needs only that one constant serves for all split tame characters. The identity continues in [the exchange identity, part 2](/chapter/exchange-identity-2/).
