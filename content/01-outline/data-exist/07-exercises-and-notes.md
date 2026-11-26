---
title: Exercises
lean:
  - New/Reduction/Data/Existence.lean
  - New/Reduction/OneSidedBound.lean
  - Lib/Analytic/Primes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Take $n = 4$, $H = 3$ and $L = 2$ in [Behrend's sets with weights](/decl/New.exists_three_term_free/), so that $o = 6^4 = 1296$. Find the sizes of all the spheres $\Sigma(4, 3, k)$. Compare the largest size with the lower bound $H^n/(nH^2)$ of [the lemma on a large sphere](/decl/Behrend.exists_large_sphere/). Write down the set $S$ for one largest sphere, and check by hand one case of property 3.

*Hint.* A point of $\{0, 1, 2\}^4$ with $j$ entries $1$ and $l$ entries $2$ has $\sum v_i^2 = j + 4l$. The largest spheres are $k = 5$, $6$ and $9$, with $12$ points each. The lower bound is $81/36 = 2.25$.

**Exercise 2.** In the theorem on Behrend's sets, the base is $B = LH$, and not $H$. Take $n = 3$, $H = 3$ and the sphere $\Sigma(3, 3, 5)$ of the Example in Section 2. Read its points in base $3$ in place of base $6$. Show that the images include $7$, $11$ and $15$, which form a three-term progression. Explain where the proof of property 3 uses that every entry of $\alpha u + \alpha' w$ is less than $B$.

*Hint.* The points $(1, 2, 0)$, $(2, 0, 1)$ and $(0, 2, 1)$ lie on the sphere, and in base $3$ they give $1 + 2 \cdot 3$, $2 + 9$ and $2 \cdot 3 + 9$. Their digit vectors $u$, $w$ have $u + w = (1, 4, 1) \neq 2v = (4, 0, 2)$, and the entry $4$ is not a digit in base $3$. The proof compares digits of the two sides, and this needs entries less than $B$.

**Exercise 3.** Let $Q$, $A$ be fixed, and assume the Siegel-Walfisz theorem in the form of Section 4. Let $U \geq W$ and $q = Q^k \leq W^A$. Show that the number of primes $p \equiv 1 \pmod q$ with $\log p \in [U, U + W]$ is at least $e^{U + W}/(2\varphi(q)(U + W))$ for large $W$. Deduce that the window $[U, U + 1]$ is already enough for the source form when $W$ is large, provided $U \geq W$.

*Hint.* Write the count with $\psi(e^{U + W}; q, 1) - \psi(e^U; q, 1)$. The main term is $(e^{U + W} - e^U)/\varphi(q)$, and the error is at most $e^{U+W}(U + W)^{-A - 2}$. For the second part, replace $W$ by $1$ in the length only, and keep $q \leq W^A \leq U^A$.

**Exercise 4.** In [the corollary on the scales](/decl/New.eventually_exists_data_scales/), show that $x^{\varepsilon/7} \leq \log x_1$ also holds for every large $x$. Then show that $x^{\varepsilon/6} \leq \log x_1$ holds only when $\exp(x^{\varepsilon/6})$ is an integer. So the exponent $\varepsilon/6$ itself cannot be used, and some loss is necessary.

*Hint.* For the first part, $u^{7/6} - 1 \geq u$ for large $u$, with $u = x^{\varepsilon/7}$. For the second part, $x_1 = \lfloor e^W \rfloor \leq e^W$, with equality only if $e^W$ is an integer, and $\log$ is strictly increasing.

**Exercise 5.** Let $n \geq 1$ and $\varepsilon > 0$ be fixed. Condition 8 of [a large scale](/decl/New.Parameters.IsLargeScale/) at $W = x^{\varepsilon/6}$ asks for $(5184 y)^n \leq e^{\varepsilon y/6}$, where $y = \log x$. Show that it holds for every large $y$. Show that $y \geq (12 n/\varepsilon) \log(12 n/\varepsilon) \cdot C$ is enough for a suitable absolute constant $C$, if $n/\varepsilon \geq 5184$.

*Hint.* Take logarithms: the condition is $n \log(5184 y) \leq \varepsilon y/6$. The function $y/\log(5184 y)$ increases for $y \geq 1$. Put $y = a \log a$ with $a = 12 n/\varepsilon$ and compare.

**Exercise 6.** Let $x, x_1, b$ be positive integers with $x_1 \mid b$ and $x \leq x_1$. Show that $\lfloor xb/x_1 \rfloor = x \cdot (b/x_1)$ and that $1 \leq \lfloor xb/x_1 \rfloor \leq b$. So the weights of [the admissible data](/decl/New.Parameters.IsAdmissibleData/) off $\Phi_b$ are exactly $xb/x_1$, as in the source's notes. Which of the three hypotheses does the proof of [the existence of admissible data](/decl/New.Parameters.IsLargeScale.exists_isAdmissibleData/) check, and how?

*Hint.* Write $b = c x_1$. Then $xb/x_1 = xc$, with $1 \leq xc \leq x_1 c = b$. In the proof, $x \leq x_1$ follows from $\log x \leq W$, and $x_1 \mid b$ from $q_1 x_1 \mid b$.

## Notes and references

The construction of Section 2 goes back to Behrend, "On sets of integers which contain no three terms in arithmetical progression", Proc. Nat. Acad. Sci. USA 32 (1946), 331 to 332. Behrend's bound $r_3(N) \geq N \exp(-c\sqrt{\log N})$ is still close to the best lower bound known for sets without three-term progressions. The form with weights, which avoids many equations $(\alpha + \alpha') e_2 = \alpha e_1 + \alpha' e_3$ at once, is due to Shapira, "Behrend-type constructions for sets of linear equations", Acta Arith. 122 (2006). A lemma close to the source's form is Lemma 4.1 of Alon and Shapira, "A characterization of easily testable induced subgraphs" (2006), in the preprint numbering. The source's list of references marks the Alon and Shapira citation as compared, with the place confirmed. It marks the Behrend and Shapira citations as "work found, no place given". This book has not compared any of the three. Mathlib has Behrend's construction for three-term progressions in its file on the Behrend bound, and the source uses its lemma on a large sphere.

The Siegel-Walfisz theorem in the form of Section 4 is Corollary 11.19 of Montgomery and Vaughan, *Multiplicative Number Theory I* (2007). Chapter 11 of that book gives the zero-free regions and Siegel's theorem behind it, and Chapter 5 of Iwaniec and Kowalski, *Analytic Number Theory*, gives the explicit formula and the zero-free region for a general L-function. The source's list of references marks the citation of Montgomery and Vaughan for the file on primes as compared, with the place confirmed. The source proves a weaker statement directly. Its observation that the real characters to the moduli $M^k$ come from $M^2$ removes Siegel's theorem from the proof. The analytic step follows Newman's short proof of the prime number theorem, "Simple analytic proof of the prime number theorem", Amer. Math. Monthly 87 (1980), with the contour integral over a circle. The source's file uses a finite form of the argument with explicit bounds. Volume 2 gives the full proof.

The recipe for the data, $x_1 = \lfloor \exp(x^{\varepsilon/6}) \rfloor$ and $\log b \approx x^\varepsilon$, is the source's own. The source's notes describe the sizes as $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$, and the recipe makes both hold with a wide margin. The source's notes call the theorem on primes in windows a short-interval result. The windows $[e^U, e^{U + W}]$ are long in the multiplicative sense, since their ratio $e^W$ tends to infinity, so the term can mislead. The notes also compare $\sqrt{\log b}$ with $\log q_2^2$, while the Lean proof uses the condition $q_2^2 \leq W^n$. The open question of where the sparse set is used at the end of the proof stays open in this chapter. Volume 11 uses the field.

The chapter [data and sizes](/chapter/data-and-sizes/) defines the data and lists the sizes that this chapter fills. The chapter [the main inequality](/chapter/main-inequality/) uses the corollary on the scales.

Status: drafted by a model. No person has checked this chapter against the Lean source.
