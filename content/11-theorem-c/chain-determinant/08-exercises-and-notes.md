---
title: Exercises and notes
lean:
  - New/Determinant/Chain/TriangleNorms.lean
  - New/Determinant/Chain/NormOfChain.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

### Learning order

Read Section 2 first. It uses only linear algebra and gives the shape of every later proof. Then read the statements of Section 3 and skip the proofs on $L$-values at first. Sections 4 and 5 hold the analytic input: Rallis' formula for the first lift of each row, and the seesaw squares of [the previous chapter](/chapter/seesaw-squares/). Section 6 joins these parts, and Section 7 is linear algebra again. For the model case $m = 2$, read the example of Section 2 and the example of Section 5 together. Then do the exercises in order.

### Exercises

**Exercise 1.** Let $U = V = \mathbb{C}^2$ with the standard inner product, $u = \mathrm{diag}(2, 3)$ and $S = \mathrm{diag}(1, 9/4)$. Find $a$ with $\langle u x, u y\rangle = a\langle x, S y\rangle$, and check the lemma on Gram determinants.

*Hint.* $u^*u = \mathrm{diag}(4, 9) = 4S$. So $a = 4$ and $a^2\det S = 16 \cdot 9/4 = 36 = \det(u^*u)$.

**Exercise 2.** Show that for $m = 3$ the pairs $0 < i < j \leq 3$ are $(1,2)$, $(1,3)$ and $(2,3)$. Which squares of the triangle give each of them?

*Hint.* The square at $(i, n)$ has the modulus $\rho_{i+1, i+n+2}$ (Section 5). Row $0$ gives $(1,2)$ and $(1,3)$. Row $1$ gives $(2,3)$.

**Exercise 3.** Compute the exponent $k_j$ of the order of the block triangular group $P_j(R)$ for $\#N = r$ and $\#T = t$.

*Hint.* $\#\mathrm{BI}_j = r + jt$. So $k_j = \sum_{l<j}(r + lt)\,t = jrt + t^2 j(j-1)/2$. Check $j = 1$: the group has the blocks $\mathrm{GL}_r$, $\mathrm{GL}_t$ and an $r \times t$ block.

**Exercise 4.** In the proof of the theorem on the norm of the chain, the case $c(1) = 0$ forces $T = 0$. Explain why the proof cannot use $c(1) \neq 0$ directly.

*Hint.* The relation "absolute value up to a norm power" allows the constant $0$ (Section 3). The Gram theorem of Section 2 gives no lower bound for $\kappa$. Only injectivity at $\vartheta = 1$ links $c(1)$ to $T$.

**Exercise 5.** Let $\vartheta = 1$. Show that $Z(1)/Z(1) = 1$ agrees with the factorization theorem.

*Hint.* $Q$ is empty, so $\mathrm{Nm}\,Q = 1$, and every ramified ratio is $1$ at the trivial twist. Each factor $Z_j(1)/Z_j(1)$ is $1$.

**Exercise 6.** Why does the source compute the norm of the chain through the triangle and not through Rallis' formula for each lift of the chain?

*Hint.* The lift from $Y_{j-1}$ to $Y_j$ for $j \geq 2$ starts from a space whose rank is too large for the range of Rallis' formula. Compare the lemma on the range of Rallis' formula in Section 4, which compares only the first two columns of a row.

**Exercise 7.** Let $e_1, e_2$ be orthogonal central idempotents of an algebra $A$ with $e_0 = e_1 + e_2$, and let $f$ be a representation of $A$. Show that the range of $f(e_1)$ is in the range of $f(e_0)$, and that $f(e_0)$ is the identity on it.

*Hint.* $e_0 e_1 = e_1^2 + e_2 e_1 = e_1$. So $f(e_1) = f(e_0)f(e_1)$. Compare the lemma on pieces of the good idempotent in Section 7.

### Notes and references

The source claims the results of this chapter in the files New/Determinant/Chain/TriangleNorms.lean, Moduli.lean, TriangleLifts.lean, ChainNorms.lean and NormOfChain.lean, at the pin 72fead1. Lean accepts them, if the reported checks hold. The text does not claim that the argument is correct beyond this.

The docstring of ChainNorms.lean names three works as related. The source does not use them in the proofs. We list them as the source names them.

- W. T. Gan, Y. Qiu and S. Takeda, The regularized Siegel-Weil formula (second term identity) and the Rallis inner product formula, Invent. Math. 198 (2014), 739-831, Theorem 1.3. This is the Rallis inner product formula for one lift. The source proves the case it needs in [the inner product formula](/chapter/rallis-inner-product/).
- J. H. Bruinier and J. Funke, injectivity of the Kudla-Millson lift, 2010, as named in the source.
- H. He, compositions of theta correspondences, 2005, as named in the source.

Findings of the register that concern this chapter. F-071: the constant of "absolute value up to a norm power" may be $0$, and Section 6 handles the case $c(1) = 0$ apart. F-037 and F-121: the lemma `New.Exchange.IsTriangle.ne_zero_of_squareCommutes` is never applied. Only the chain form `New.Exchange.IsTriangle.ne_zero_of_chainCommutes` is used (Section 2). F-026: `Fintype.ofFinite` is a local instance of low priority in NormOfChain.lean.

The lemma on the order of $P_j(R)$ in Section 6 has no statement of its own in this chapter. Its Lean declaration carries an explicit universe, and the name index of the handbook does not list it.
