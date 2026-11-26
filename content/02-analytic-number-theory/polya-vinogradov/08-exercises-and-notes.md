---
title: Exercises
lean:
  - Lib/Analytic/PolyaVinogradov.lean
  - Lib/Analytic/QuadraticTwist.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\chi$ be the non-principal real character modulo $5$. Compute $S(X) = \sum_{v \leq X}\chi(v)$ for $X = 1, \ldots, 5$, and compare $\max_X|S(X)|$ with the bound $\sqrt5(1 + \log5)$ of the primitive case and with the bound $2\sqrt5(1 + \log5)$ of [Theorem](/decl/New.polya_vinogradov/).

*Hint.* The values are $1, -1, -1, 1, 0$, so $S(X)$ is $1, 0, -1, 0, 0$, and $|S(X)| \leq 1$. Both bounds are larger than $5$.

**Exercise 2.** Let $\chi$ be a non-principal character modulo $q$, and let $Y < Z$ be natural numbers. Deduce from the theorem of Section 2 that $|\sum_{Y < v \leq Z}\chi(v)| \leq 4\sqrt q(1 + \log q)$. Show that the factor $4$ can be replaced by $2$ when $\chi$ is primitive and $q \neq 1$.

*Hint.* The sum is $S(Z) - S(Y)$. For the primitive case use the bound $\sqrt q(1 + \log q)$ of the proposition on primitive characters for both terms.

**Exercise 3.** Let $r = p_1p_2\cdots p_k$ be the product of the first $k$ primes. Compare the number of divisors $2^k$ of $r$ with $2\sqrt r$ for $k = 1, \ldots, 6$. Then show that $\tau(r) \leq 2\sqrt r$ for every $r \geq 1$, by pairing each divisor $e \leq \sqrt r$ with $r/e$.

*Hint.* For $k = 1$ the two sides are $2$ and $2\sqrt2$. The divisors $e > \sqrt r$ are the numbers $r/e'$ with $e' < \sqrt r$.

**Exercise 4.** Let $m = 15$. Show that $(\cdot/15)$ is a non-principal character modulo $15$, that it is odd, and that it is primitive. Then compute $(-v/15)$ for $1 \leq v \leq 15$ and check the bound of the lemma on sums of Jacobi symbols for every $X \leq 15$.

*Hint.* $(-1/15) = (-1/3)(-1/5) = (-1)(1) = -1$. For primitivity, $(\cdot/3)$ and $(\cdot/5)$ are primitive, and the argument of the lemma on the twist of a primitive character applies with $M = 5$ and $d = 3$.

**Exercise 5.** Let $d \equiv 3 \bmod 8$ be a prime and $n = 2^km$ with $m$ odd. Show that $(n/d) = (-1)^k(-d/m)$. Deduce that the count of Section 6 also holds for a class of primes $d \equiv 3 \bmod 8$, if one replaces the coefficients $\psi(n)(-v/n^\circ)$ by $\psi(n)(-1)^{k(n)}(-v/n^\circ)$, where $2^{k(n)}$ is the largest power of $2$ that divides $n$.

*Hint.* $(2/d) = -1$ for $d \equiv 3 \bmod 8$. The sign $(-1)^{k(n)}$ depends only on $n$, so it can be put into $\alpha_n$, and the theorem of Section 5 allows every $\alpha$ with $|\alpha_n| \leq 1$. The parity of the twists is still fixed by $d \equiv 3 \bmod 4$.

**Exercise 6.** In the proof of the theorem on three lines at a zero, replace the box $\operatorname{Re} s \geq 1/2 + 9\delta$ by $\operatorname{Re} s \geq 1/2 + K\delta$. Find the least $K$ for which the same proof gives $|\Gamma_j(s)|^2 \leq CT^{-2\delta}$, with the hypothesis $J(\chi, T) \leq T^{2\delta}$ unchanged.

*Hint.* The exponent is $4\delta(1 - \lambda) - \lambda$ with $\lambda \geq 2K\delta/3$. It is at most $-2\delta$ for all small $\delta$ exactly when $2K/3 \geq 6$.

**Exercise 7.** Show that the number of pairs $(n, m)$ of positive integers with $n, m \leq Y$ and $nm$ a square is $\asymp Y\log Y$. Deduce that the trivial bound of the square pairs in Section 5 cannot give a mean square smaller than about $T^2\log T$ at $u = 1/T$.

*Hint.* Write $n = ab^2$ and $m = ac^2$ with $a$ squarefree. For fixed $a \leq Y$ there are about $Y/a$ pairs $(b, c)$.

**Exercise 8.** The theorem on bad primes gives $B(X) = O(X^{1 - \delta/2})$. Use only this bound and the divergence of $\sum_{p \equiv a}\log p/p$ to show that the set of good primes of the class is infinite, not only non-empty.

*Hint.* Remove a finite set of primes from the class. The sum over the rest still diverges. Apply the argument of the choice of the prime to the rest.

## Notes and references

The inequality is due to Pólya and to Vinogradov, both in 1918. The proof by Fourier expansion with Gauss sums is in Davenport, *Multiplicative Number Theory*, Chapter 23, in Montgomery and Vaughan, *Multiplicative Number Theory I*, Theorem 9.18, and in Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 12. Paley showed in 1932 that the logarithm cannot be replaced by a bounded function: there are real characters with $\max_X|S(X)| \gg \sqrt q\log\log q$. Montgomery and Vaughan (Invent. Math. 43 (1977)) proved the upper bound $\sqrt q\log\log q$ under GRH. The source cites Pólya 1918 and Vinogradov 1918 with no place, and Davenport and Montgomery and Vaughan with the place confirmed, in its list of references.

Gauss sums and the functional equation of $L(s, \chi)$ for primitive $\chi$ are in Davenport, Chapter 9. This book treats them in [Dirichlet L-functions](/chapter/dirichlet-l-functions/), which also contains the theta series of the source. The Jacobi symbol and its reciprocity law are in Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 5. Zero detection by mollifiers and zero density estimates are in Iwaniec and Kowalski, Chapter 10.

Mean values over real characters were studied by Jutila (*On mean values of Dirichlet polynomials with real characters*, Acta Arith. 27 (1975)) and by Heath-Brown (*A mean value estimate for real character sums*, Acta Arith. 72 (1995)). The source cites both, with no place. Its estimate is weaker than either and has a different form: a smoothed mean square over all $v \leq T^2$ of theta series of length $1/u \leq T$, proved by Pólya-Vinogradov alone. The source also attributes the mean value estimate to "an estimate of Elliott", with no reference; the list of references of the source has no entry for Elliott. The plan of this handbook calls the result of Section 6 a zero density estimate; Section 6 explains that it counts bad primes, not zeros. The findings F-067 and F-103 of the research notes record that the faithfulness of this file to the cited works has not been checked.

The Lean files are Lib/Analytic/PolyaVinogradov.lean and Lib/Analytic/QuadraticTwist.lean, with the theta series of Lib/Analytic/DirichletTheta.lean. The only use in the argument is in New/Reduction/Zeros/Criterion.lean, in the proof of the [one-sided criterion](/chapter/landau-criterion/).

The results of this chapter are classical in kind, and their proofs in the source use only Mathlib and thirteen local files, none under New/. This book does not claim that the argument of the source is correct. Volume 0, [the claim and its status](/chapter/claim-and-status/), describes what has and has not been checked.

Status: drafted by a model. No person has checked this chapter against the Lean source.
