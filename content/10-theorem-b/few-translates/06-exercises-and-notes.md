---
title: Exercises
lean:
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/Spanning/SecondMoment/PositiveType.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $J : S \to T$ be an isometry, let $\lambda \geq 0$, and let $A = \lambda J$. Find the least $\varepsilon$ such that $A$ is a near isometry with the error $\varepsilon$ in the sense of [Definition](/decl/New.IsNearIsometry/). Compare it with the operator norm $\|A^*A - 1\|_{\mathrm{op}}$.

*Hint.* $\|A\,\mathrm{pr}_U\|^2 = \lambda^2\dim U$. The worst subspace is $U = S$ if $\lambda < 1$ and $U = 0$ if $\lambda \geq 1$. The answer is $\max(0, 1 - \lambda^2)$, and the operator norm is $|1 - \lambda^2|$.

**Exercise 2.** Let $\rho$ be a unitary representation of a finite group $\Gamma$ on $T$, and let $B : S \to T$ be an isometry. Prove that

$$\frac{1}{|\Gamma|}\sum_{s \in \Gamma}\|B^*\rho(s)B\|^2 \geq \frac{(\dim S)^2}{\dim T}.$$

Show that the model case of [the opening section](/chapter/few-translates/#what-the-chapter-proves) gives equality.

*Hint.* Let $\Sigma = \sum_s\rho(s)BB^*\rho(s)^*$. Then $\operatorname{tr}\Sigma = |\Gamma|\dim S$. By [Lemma](/decl/New.inner_hilbertSchmidtVector_translate/), $\|\Sigma\|^2 = |\Gamma|\sum_s\|B^*\rho(s)B\|^2$. The Cauchy-Schwarz inequality for $\Sigma$ and the identity gives $(\operatorname{tr}\Sigma)^2 \leq \dim T\,\|\Sigma\|^2$.

**Exercise 3.** The proof of [Lemma](/decl/New.IsSpread.exists_codim_le/) uses $\frac{3}{32} \leq \frac{1}{10}$. Show that the same proof gives the factor $1 - \frac{13\dim V}{32\dim W}$ in place of $1 - \frac{2\dim V}{5\dim W}$. What constant replaces $\frac{5}{2}$ in [Theorem](/decl/New.IsSpread.exists_few_le_finrank_iSup_range/)? Does Step 1 of its proof still hold?

*Hint.* The gain is $\frac{1}{2} - \frac{3}{32} = \frac{13}{32}$ of $(1 - \alpha)\dim V$. The constant becomes $\frac{32}{13} \approx 2.46$. Step 1 uses only the step lemma at $F = 0$.

**Exercise 4.** In the model case with $d \mid n$, the shifts spread with every error $\frac{3}{2}\varepsilon > 0$. Compute the number $l = \lceil\log(1/(16\varepsilon))/\mathrm{rate}\rceil$ of steps in the proof of [Theorem](/decl/New.IsSpread.exists_few_le_finrank_iSup_range/), and its ratio to $n/d$. Evaluate the ratio for $\varepsilon = (8b^2)^{-1}$ and $b = 1000$.

*Hint.* $\mathrm{rate} = 2d/(5n)$. The ratio is about $\frac{5}{2}\log(1/(16\varepsilon))$, which is about $32.8$ for $b = 1000$.

**Exercise 5.** Let $G = \mathrm{GL}_n(\mathbb{F}_q)$ act on $\mathbb{F}_q^n$. Prove that the stabilizer of each nonzero vector has $|G|/(q^n - 1)$ elements, under $g \mapsto g$ and under $g \mapsto (g^{\mathsf T})^{-1}$. Then let $m = 2$ and let $A_0 = A_1$ have the columns $e_1$ and $e_2$. Use [Theorem](/decl/New.card_mul_sum_det_eq_zero_le/) with $\Theta = 1$ to bound the share of the $g$ whose upper left $2 \times 2$ block is singular. For which pairs $(q, n)$ is the bound less than $1$?

*Hint.* The orbit of a nonzero vector is the set of all nonzero vectors. The bound on the share is $2/q + q(q^{n/2})/(q^n - 1)$. The true share is about $1/q$.

**Exercise 6.** Find the two places in the proof of [Theorem](/decl/New.card_mul_sum_det_eq_zero_le/) where $\Theta \geq 0$ is used. Give a function of positive type on $\mathbb{Z}/2\mathbb{Z}$ that takes a negative value, and explain why [Lemma](/decl/New.re_sum_addChar_dotProduct_mul_le/) still applies to it.

*Hint.* Step 1 multiplies $q \leq N(s)$ by $\Theta(s)$, and Step 5 needs $\Theta(G) \geq 0$. For $\mathbb{Z}/2\mathbb{Z}$, take $u_0 = 1$ and $u_1 = -1$ in $\mathbb{C}$, so $\Theta(0) = 1$ and $\Theta(1) = -1$.

## Notes and references

The Hilbert-Schmidt norm and the trace inner product are standard; see R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169 (1997). Ky Fan's maximum principle, used in the section on Hilbert-Schmidt norms, is in the same book. Functions of positive type on groups and the construction of the vectors $u_a$ from $\Theta$ are in G. B. Folland, *A Course in Abstract Harmonic Analysis*, Section 3.3. Additive characters of finite fields and their orthogonality are in R. Lidl and H. Niederreiter, *Finite Fields*, Chapter 5.

The bound of Exercise 2 is a form of the frame bound of L. R. Welch, *Lower bounds on the maximum cross correlation of signals*, IEEE Transactions on Information Theory 20 (1974). Equality holds for tight frames; see J. J. Benedetto and M. Fickus, *Finite normalized tight frames*, Advances in Computational Mathematics 18 (2003). The greedy cover with a logarithmic loss is the analysis of the greedy method for set cover of V. Chvátal, *A greedy heuristic for the set-covering problem*, Mathematics of Operations Research 4 (1979), and for submodular functions of L. A. Wolsey, *An analysis of the greedy algorithm for the submodular set covering problem*, Combinatorica 2 (1982). The dimension of a span is a submodular function of the set of chosen maps, so the case here is a case of Wolsey's setting. The source names Welch and Wolsey in FewTranslates.lean. REFERENCES.md marks these two citations as not compared with the source, with no place given, and this chapter has not compared them either.

The spread condition with the form $(1 + \alpha)/2$, the constants $\frac{3}{2}\varepsilon$, $16\varepsilon$ and $\frac{2}{5}$, and the lemma on singular minors follow the source. The statements in this chapter are those of Lean. Lean accepts them, if the reported checks hold. This chapter does not claim that the argument proves Theorem B in the sense of a refereed proof, and it does not claim that the Generalized Riemann Hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
