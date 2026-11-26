---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $q \geq 1$, $q_0 = 18480\, q$ and $d_0 = 9240\, q - 1$. Show that $18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$, that $d_0 = q_0/2 - 1$, that $d_0 \equiv 7 \bmod 8$, and that $(d_0, q_0) = 1$. These are the hypotheses that the proof of the half-plane theorem checks before it applies Landau's criterion.

*Hint.* $9240 = 8 \cdot 1155$. A common divisor of $d_0$ and $q_0 = 2(d_0 + 1)$ divides $2$, and $d_0$ is odd.

**Exercise 2.** In the proof of the star inequality, put $\mathrm{loss} = f a \log^4 b$, $\mathrm{err}_0 = f a \log^3 b$ and $\mathrm{err} = 4\,\mathrm{loss} + 20 \log(1 + 2b^2)\, \mathrm{err}_0$. Show that $\log(1 + 2b^2) \leq 2\log b + 2$ for $b \geq 1$, and deduce that $2\,\mathrm{err} \leq f a \log^5 b$ when $\log b \geq 100$. Which term of $2\,\mathrm{err}$ is the largest?

*Hint.* $1 + 2b^2 \leq 3b^2$ and $\log 3 < 2$. Then $2\,\mathrm{err} \leq 88\, f a \log^4 b + 80\, f a \log^3 b$. The index term is the largest: it is about ten times the other two together.

**Exercise 3.** Suppose that the data could be chosen with $x^{\theta} \leq m$ for some $0 < \theta \leq 1/2$, with all other conditions of the end of the proof unchanged. Show that $R_{q_0}(x) \leq (64\,\varphi(q_0) + 3)\, x^{-\theta + 6\varepsilon_1}$ for large integers $x$. Which half-plane free of zeros would Landau's criterion give? Why does a value $\theta > 1/2$ give nothing more?

*Hint.* Follow the proof of the one-sided bound in Section 2. The criterion needs a bound $R_{q_0}(x) \leq x^{\beta - 1}$ with $\beta > 1/2$, and it gives no zeros in $\operatorname{Re} s > \beta$. Take $\beta = 1 - \theta + 7\varepsilon_1$. For the last question, $\beta > 1/2$ is a hypothesis of the criterion, and the half-plane theorem already covers $\operatorname{Re} s > 1/2$.

**Exercise 4.** This is a model of size against divisibility. Let $n \geq 1$ and $N = \binom{2n}{n}$. Show that every prime $p$ with $n < p \leq 2n$ divides $N$, and that $N \leq 4^n$. Deduce that
$$\sum_{n < p \leq 2n} \log p \leq n \log 4.$$
The prime number theorem says that the left side is $n + o(n)$. Explain why this argument can never give the bound $n + o(n)$, and what this says about the main amount in the method of Section 3.

*Hint.* $N = (2n)!/(n!)^2$, and $p$ divides the numerator but not the denominator. $N$ is one term of $(1 + 1)^{2n}$. The size bound $N \leq 4^n$ does not know the main term of the prime sum: it is too large by the factor $\log 4 > 1$.

## Notes and references

The Riemann hypothesis is in Riemann's paper of 1859 on the number of primes below a given size. Edwards, *Riemann's Zeta Function* (1974), has an English translation of the paper as an appendix and a commentary on it. Hadamard and de la Vallée Poussin proved the prime number theorem in 1896 by showing that $\zeta(s) \neq 0$ on $\operatorname{Re} s = 1$. Hilbert put the Riemann hypothesis in the eighth of his problems of 1900. Hardy proved in 1914 that $\zeta$ has infinitely many zeros on the critical line; Titchmarsh, *The Theory of the Riemann Zeta-Function*, Chapter 10, gives the proof. Bombieri's description of the problem for the Clay Mathematics Institute (2000) states the hypothesis and surveys what is known.

Dirichlet introduced his L-functions in 1837 to prove that every reduced class modulo $q$ contains infinitely many primes. Davenport, *Multiplicative Number Theory*, treats this theorem in Chapters 1 to 4, primitive characters in Chapter 5, Riemann's memoir and the functional equation of $\zeta$ in Chapter 8, and the functional equation of $L(s, \chi)$ in Chapter 9. Iwaniec and Kowalski, *Analytic Number Theory*, Chapter 5, treat L-functions in general. The analogue for curves over finite fields is a theorem of Weil (1948). Bombieri, *Counting points on curves over finite fields*, Séminaire Bourbaki 430 (1973), gives a proof by Stepanov's method, in which an auxiliary polynomial vanishes to high order at the points to be counted, and its degree bounds the number of these zeros.

For its criterion the source cites Landau's paper of 1905, Montgomery and Vaughan, *Multiplicative Number Theory I*, Sections 15.1 and 15.2, on Landau's theorem for Dirichlet series with coefficients of one sign, and Suzuki, arXiv 2411.07436. For the prime number theorem that the end of the proof uses, it cites Corollary 11.19 of the same book.

The source says that the proof is Levent Alpöge's, with Claude, and that the readable edition "is a shorter rewriting of Levent Alpöge's Lean proof (see https://alpo.ge/remark.pdf). It follows that proof's method; many steps are proved by other arguments, and parts of it, mostly background material, were ported from there and then rewritten". It also says that the file of statements, and the names and types of the five theorems, are taken from that proof unchanged. This book has not compared the source with Alpöge's proof. The method of Section 3 is the method of the source, read from its Lean files and their heads.

The head of the file of the main inequality names, as earlier bounds for sums over primes by size against divisibility, four works: Pritsker, *The Gelfond-Schnirelman method in prime number theory* (2005); Granville and Stark, *ABC implies no Siegel zeros for L-functions of characters with negative discriminant* (2000); Bombieri's Bourbaki talk above; and van Frankenhuijsen, *The Riemann hypothesis for function fields over a finite field* (2008). The list of citations of the source marks the citation of Bombieri as confirmed at second hand, and the other three as found with no place given. This book has not compared them. In its file on twisted lattices the source cites, as related work, Bost, *Algebraic leaves of algebraic foliations over number fields* (2001), and Laurent, *Linear forms in two logarithms and interpolation determinants* (1994).

Status: drafted by a model. No person has checked this chapter against the Lean source.
