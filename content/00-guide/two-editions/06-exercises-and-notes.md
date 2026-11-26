---
title: Exercises
lean:
  - Main.lean
  - Statements.lean
  - New/Reduction/OneSidedBound.lean
  - New/Reduction/MainInequality.lean
  - New/Reduction/Zeros/PrimeError.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Compare the files `src/Main.lean` of the two editions with `diff`. List each line that differs. Show that no line that differs is part of a declaration, and conclude that the two files declare the same five theorems with the same proof terms.

*Hint.* The differences are five docstrings and the place of one comment line relative to `import New.Main`. A docstring is attached to a declaration, but it is not part of its type or its value.

**Exercise 2.** The readable main inequality is $m \cdot \mathrm{rem} \leq f a \log^5 b$. The compact one is $m \cdot \mathrm{rem} \leq \log^2 b \cdot \mathcal B$. Show that the two right sides are equal. Then add the four compact errors per dimension of Section 3 (length, missing dimensions, index, covolume) and show that their sum is at most $f a \log^5 b$ under the scale conditions. Which term needs $b^{-2} x^{99}$ to be small?

*Hint.* $\mathcal B = f a \log^3 b$. The missing dimensions give $4 x^{99}$, and $x^{99} \leq b$ is far smaller than $f a \log^4 b$, since $a \geq x b$. The index term is $10 \log(1 + b^2) \cdot f a \log^3 b \leq 30 f a \log^4 b$ for large $b$.

**Exercise 3.** In the model of the window lemma (Section 4), replace $k = \lceil t^2/9 \rceil$ by $k = \lceil t \rceil$. Which of the three estimates fails? Then replace it by $k = \lceil t^3 \rceil$. Which estimate fails now? Explain why the window must be $[t, t^2]$ and not $[t, 2t]$ for this method.

*Hint.* The gamma density with shape $k + 1$ and rate $3$ has its mass near $k/3$. For the window estimate the mass must be in $[t, t^2]$. For the term $(3/R)^k$ to beat $e^{3t}$ one needs $k \gg t$.

**Exercise 4.** Let $E(v) = \sin(v)$ for $v \geq 0$. Compute its transform $\Phi(s) = \int_0^\infty \sin(v) e^{(1-s)v}\,dv$ for $\operatorname{Re} s > 1$. Show that $(s - 1)\Phi(s)$ is analytic on $\operatorname{Re} s \geq 1$, so that $E$ satisfies the analytic clause of the compact `IsPolar`. Check the conclusion of the window lemma for $E$ and $E' = 0$ directly.

*Hint.* $\Phi(s) = 1/((s-1)^2 + 1)$, with poles at $1 \pm i$. For the conclusion, $\sin u \leq 0$ on a subinterval of length $\pi$ of every interval of length $2\pi$.

**Exercise 5.** In the readable data, $b$ is a multiple of $q_1 x_1$ (the field `dvd_natB`). Find in the readable construction of the data the place where $b$ is chosen from $x_1$. Explain why a proof that changes $x_1$ after the data are made would have to change $b$, and so all the objects that depend on $b$.

*Hint.* Search `New/Reduction/Data/Existence.lean` for the definition of the scale $b$: it is the least multiple of $q x_1$ above $\exp(W^6)$, with $x_1 = \lfloor e^W \rfloor$.

**Exercise 6.** The readable criterion has the hypothesis $\rho \neq 1$, and the readable proof of the half-plane theorem treats $\rho = 1$ apart. The compact criterion has no such hypothesis. Show that the compact conclusion $\tilde L(\rho, \chi) \neq 0$ at $\rho = 1$ for the principal character is the statement that $L(s, \chi_0)$ has a pole at $s = 1$ with non-zero residue. Then explain why the compact proof of `New.grh` needs no separate case.

*Hint.* $\tilde L(s, \chi_0) = (s - 1) L(s, \chi_0)$. For $\chi \neq \chi_0$, $\tilde L = L$, and the case $\rho = 1$ is Dirichlet's theorem, which the criterion then contains.

## Notes and references

The two editions are described in the READMEs of the source, `grh/README.md` and `grh-compact/README.md`, and in the specification of this book, 01.3 and the findings F-115 to F-118. The comparison of files in Section 2 was done by this book with `cmp` and `diff` at the pinned commit 72fead1.

The prime number theorem in arithmetic progressions for a fixed modulus, with an error term that saves every power of the logarithm, is in Montgomery and Vaughan, *Multiplicative Number Theory I*, Corollary 11.19, which the readable file cites. A Tauberian route to the prime number theorem is in Chapter 8 of the same book. The criterion of Landau type, a one-sided bound for a sum with weights of one sign that gives a half-plane of analytic continuation, goes back to Landau (1905); Montgomery and Vaughan, Sections 15.1 and 15.2, treat oscillation theorems of this kind. Both editions cite these as related work.

The window lemma of the compact edition is a local form of an oscillation argument: a function whose transform has no pole in a half-plane cannot keep one sign on a long interval. The compact file cites the work of Pintz on sign changes of $\pi(x) - \operatorname{li}(x)$ (1976 to 1978) and of Kaczorowski on sign changes of the remainder in the prime number formula (1984) as related work. This book has not compared the lemma with these papers. The model proof in Section 4 is this book's. It uses only the gamma integral, Chebyshev's inequality and Stirling's lower bound $k! \geq (k/e)^k$.

The finding F-118 says that `Main.lean` "differs only in docstrings and the order of imports". The file has one import. The difference is the order of one comment line and the import, with the docstrings. The specification 01.3 says that the spine comment of the compact `New/Main.lean` is at lines 26 to 112. At the pin it is at lines 27 to 115.

Status: drafted by a model. No person has checked this chapter against the Lean source.
