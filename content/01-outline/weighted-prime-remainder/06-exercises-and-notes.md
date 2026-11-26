---
title: Exercises and notes
lean:
  - New/Reduction/Zeros/PrimeError.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

1. Take $d = 23$ and $q = 1$. List the $n \leq 30$ with $\lambda(n) \neq 0$, and compute $R_1(10)$ and $R_1(30)$ with $c_1 = -1 - \mathrm{cs}_{23} = -1.999337$. *Hint.* The squares modulo $23$ are $1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18$. So $2$ and $3$ split, and $5$ and $7$ are inert.
2. Check the numbers of the explicit formula for the weighted sum in Section 2. Show that $\sum_{k \geq 1} 1/(2k(2k + 1)) = 1 - \log 2$, and that $-(2 + \gamma - \log 4\pi) - \log 2\pi + 1 - \log 2 = -1 - \gamma$. *Hint.* $1/(2k(2k + 1)) = 1/(2k) - 1/(2k + 1)$, and $\sum_{j \geq 2}(-1)^j/j = 1 - \log 2$.
3. Let $d \equiv 3 \bmod 4$ be a prime and $q = 1$. From $\sum \lambda(n)n^{-s} = -2\zeta'/\zeta + \zeta_K'/\zeta_K$, compute the residues of $\sum \lambda(n)n^{-s}/(s(s - 1))$ at $s = 1$ (a double pole: give the two coefficients of the Laurent expansion), at a zero of $\zeta$, and at a zero of $L(s, \chi_K)$ that is not a zero of $\zeta$. Deduce the main term $\log x$ and the constant $c_1$ of $R_1$.
4. Let $a : \mathbb{N} \to [0, \infty)$ with $\sum a(n)n^{-\sigma} < \infty$ for $\sigma > 1$. Show by partial summation that for every $r \in \mathbb{N}$ and $\operatorname{Re} s > 1$, $\sum a(n)n^{-s} = (s + r - 1)\int_1^\infty y^{-r}\bigl(\sum_{n \leq y} a(n)n^{r - 1}\bigr) y^{-s}\, dy$. Why does the source ask $\operatorname{Re} s > 2$?
5. Take $d = 2$. Show that $(n/2)$, as defined by the source, is the principal character modulo $2$, so that $\psi\chi_K$ is principal when $\psi$ is principal. Compute the Dirichlet series of $\lambda$ in this case for $q = 1$, and show that the term $\log x/\varphi(q)$ of $R_q$ is then the wrong main term. Which results of this chapter fail, and which ones stay true?
6. Show that $\overline{G_q(\bar s)} = G_q(s)$ at every $s$ where $G_q$ is analytic. Deduce the proposition that $G_q(1)$ is real without the transform. *Hint.* $\psi \mapsto \bar\psi$ is a bijection of the characters modulo $q$, and $\overline{\psi\chi_K} = \bar\psi\chi_K$.
7. Suppose that $L(s, \chi_K)$ has a real zero $\beta \in (1/2, 1)$ of order $1$, and that $\zeta(\beta) \neq 0$. Take $q = 1$. Show that the residue of the transform of $R_1$ at $\beta$ is $-1/(\beta(1 - \beta))$. Show that Landau's theorem in the form of Section 5 cannot apply to $R_1$ with any $\beta' < \beta$, whatever upper bound $R_1$ satisfies.

## Notes and references

The explicit formula for $\psi(x)$ is in Davenport, *Multiplicative Number Theory* (3rd edition, revised by H. L. Montgomery), Chapter 17, and its form for $\psi(x, \chi)$ in Chapter 19. The sum $\sum_\rho 1/\rho$ and the constant $B$ of the product formula for $\xi$ are in Chapter 12. The orthogonality of characters and the non-vanishing of $L(1, \chi)$ are in Chapter 4, the class number formula in Chapter 6, and the functional equation in Chapter 9. Montgomery and Vaughan, *Multiplicative Number Theory I*, Chapter 12, treats explicit formulae. The weight $1/n - 1/x$ of this chapter is the simplest of them: it is the first integral of the count.

The formula of Chowla and Selberg is in A. Selberg and S. Chowla, *On Epstein's zeta-function*, J. reine angew. Math. 227 (1967), 86 to 110. The source proves a form without Gamma values, through Kronecker's limit formula (Lib/CM/ChowlaSelberg.lean).

The file New/Reduction/Zeros/PrimeError.lean names Davenport as its source, without a chapter. The file of the references of the source records this as a work found with no place given. The places above are those of the classical statements, not of the forms of the source.

The source differs from the textbook treatment in three points. It works with the entire functions $\tilde L$, so that the pole at $s = 1$ is explicit. It proves that $G_q(1)$ is real through the transform. It gives the residue at $s = 1$ as the junk value of a division by zero. The main theorem asks $d \equiv 7 \bmod 8$, but its proof uses only $d \neq 2$. The research note on the remainder says that the terms $c_q$ and $\log x/\varphi(q)$ kill the double pole at $s = 1$. More exactly, $\log x/\varphi(q)$ removes the double pole, and $c_q$ removes the simple pole that is left.

The relevant findings of the notes are F-039 (the residue at $s = 1$ as a division by zero), F-064 (the unit of the formula of Chowla and Selberg is not shown to be algebraic), F-077 (the sign of the residues, to be checked by a person) and F-092 (the thresholds depend on $|\mathrm{cs}_d|$, and so on $d$).

Status: this chapter was drafted by a model. No person has checked it against the source.
