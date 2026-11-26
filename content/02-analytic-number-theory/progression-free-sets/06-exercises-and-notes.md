---
title: Exercises
lean:
  - New/Reduction/Data/Existence.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Build a sequence greedily: $a_0 = 0$, and $a_{j+1}$ is the least integer $a > a_j$ such that $\{a_0, \dots, a_j, a\}$ has no nontrivial three-term progression. Prove that $a_j$ is the integer whose ternary digits are the binary digits of $j$. So the greedy sequence is the set of Erdős and Turán of Section 2, and the greedy method gives only the density $N^{-0.369\ldots}$.

*Hint.* Show by induction on $j$ that the first $j + 1$ terms are the $j + 1$ least elements of $S = \bigcup_n S_n$. The set $S$ is 3AP-free, so the next element of $S$ is allowed. For an integer $a \notin S$, some ternary digit of $a$ is $2$. Let $c'$ have the digits of $a$ with each $2$ replaced by $1$, and let $c$ have the digits of $a$ with each $2$ replaced by $0$. Then $c, c' \in S$, $c < c' < a$ and $c + a = 2 c'$ digit by digit, with no carries. So $a$ is excluded.

**Exercise 2.** Show that the bound $\alpha + \alpha' \leq L$ in the theorem of Section 3 cannot be dropped. That is, let $o \geq 1$ and let $S \subseteq \mathbb{N}$ have at least two elements. Find $e_1, e_2, e_3 \in S$ and $\alpha, \alpha' > 0$ with $(\alpha + \alpha') e_2 \equiv \alpha e_1 + \alpha' e_3 \pmod{o}$ but not $e_1 = e_2 = e_3$. Then show more: for $S$ with three elements $e_1 < e_2 < e_3$ there are $\alpha, \alpha' > 0$ with $(\alpha + \alpha') e_2 = \alpha e_1 + \alpha' e_3$ in $\mathbb{Z}$, and give a bound for $\alpha + \alpha'$ in terms of $e_3 - e_1$.

*Hint.* For the first part take $e_1 = e_2 \neq e_3$ and $\alpha' = o$. For the second part take $\alpha = e_3 - e_2$ and $\alpha' = e_2 - e_1$. So a set of exponents below $o$ can avoid all the weights only up to a bound $L$, and the bound $L = 2l_0$ of Section 4 is a real restriction.

**Exercise 3.** Let $c \geq 1$ and $l_0 = 3^{c-1}$. Prove that $4$ has order exactly $l_0$ in $(\mathbb{Z}/3^c\mathbb{Z})^\times$. Deduce the statement of Section 4 for $\ell = 2$: if $4^a \equiv 4^b \pmod{3 l_0}$ with $0 \leq a, b < l_0$, then $a = b$. Compare your proof with `ZMod.orderOf_one_add_prime` (Mathlib).

*Hint.* Prove $(1 + 3)^{3^j} \equiv 1 + 3^{j+1} \pmod{3^{j+2}}$ by induction on $j$, with the binomial theorem. The terms of degree $2$ and $3$ need the factor $3$ in $\binom{3}{2}$ and the bound $3(j+1) \geq j + 3$. So $4^{3^{c-2}} \not\equiv 1 \pmod{3^c}$, while $4^{3^{c-1}} \equiv 1$.

**Exercise 4.** In the theorem of Section 3, the hypothesis $0 < L$ is used in the proof of property 1. Show that the statement becomes false for $L = 0$. Take $n = 1$, $H = 2$ and $o = 0$, and check each hypothesis and each property. Then explain why the case $n = 0$ needs no hypothesis, with the convention $x / 0 = 0$ of Lean.

*Hint.* For $L = 0$ and $n = 1$ the room condition is $0 \leq o$. Property 1 asks $e < 0$ for every $e \in S$, so $S$ is empty. Property 2 asks $2/(1 \cdot 4) = 1/2 \leq 0$. For $n = 0$ the count is $H^0/(0 \cdot H^2) = 1/0 = 0$ in Lean.

**Exercise 5.** Let $\delta(N) = 1/(n L^n H^2)$ be the density bound of Section 3, with $(L H)^n = N$. Fix $n$ and $L$ and let $H \to \infty$. Show that $\delta(N) = N^{-2/n + o(1)}$. Compare this with the bound of Kelley and Meka in Section 2: a 3AP-free set of density $\delta$ in $[0, N)$ has $\delta \leq \exp(-c(\log N)^{1/12})$. Explain why the two bounds do not contradict each other, and why the argument cannot hope for a set of positive density.

*Hint.* $H^2 = N^{2/n}/L^2$. The density $N^{-2/n}$ is $\exp(-(2/n)\log N)$, and $(2/n)\log N$ is much larger than $c(\log N)^{1/12}$ for large $N$. Behrend's choice of $n$ near $\sqrt{2 \log N/\log 2}$ gives a density $\exp(-c'\sqrt{\log N})$, still below the upper bound. For the last question use Roth's theorem.

**Exercise 6.** In the example of Section 3, with $n = 3$, $H = 4$ and the sphere $k = 10$, list the solutions of $3 e_2 = e_1 + 2 e_3$ in the set $\{11, 25, 67, 88, 193, 200\}$ with $e_1, e_2, e_3$ not all equal. Then check by hand that the set $\{15, 37, 147, 180, 433, 444\}$ in base $12$ has no such solution, and that the set in base $8$ has no nontrivial solution of $2 e_2 = e_1 + e_3$.

*Hint.* For each $e_2$ the number $3 e_2 - 2 e_3$ must be in the set. There are only $36$ pairs $(e_2, e_3)$. In base $8$ the weights $\alpha = \alpha' = 1$ give digits below $2H = 8$, so no carries arise and strict convexity applies.

**Exercise 7.** In the proof of the theorem on a large sparse set of places in Section 4, find each use of the bounds $i < l_0$ and $j < l_0$. Show that the same proof works if the definition of sparseness allows $0 < i < j \leq l_0$. Then explain why the case $\ell = 2$ cannot allow $i = l_0$.

*Hint.* In the case $\ell = 2$ only $i < l_0$ is used, against the order $l_0$ of $4$ modulo $3 l_0$. In the case of odd $\ell$ the weights $2a$ and $2i$ have sum $2j$, and the theorem of Section 3 was applied with the weights up to $2 l_0$, so $2j \leq 2 l_0$ is enough. The final order bound uses $2i \leq 2 l_0$. For $i = l_0$ the class $4^{l_0}$ is $1$ modulo $3 l_0$, and the argument modulo $3 l_0$ gives no contradiction.

## Notes and references

The problem of the size of $r_3(N)$ is due to Erdős and Turán, "On some sequences of integers", J. London Math. Soc. 11 (1936) 261-264, where the ternary example of Section 2 appears. Salem and Spencer, "On sets of integers which contain no three terms in arithmetical progression", Proc. Nat. Acad. Sci. USA 28 (1942) 561-563, gave the first density $N^{-o(1)}$. Behrend, "On sets of integers which contain no three terms in arithmetical progression", Proc. Nat. Acad. Sci. USA 32 (1946) 331-332, gave the construction on a sphere that the source uses. Elkin, "An improved construction of progression-free sets", Israel J. Math. 184 (2011), gained the factor $(\log N)^{1/4}$, and Green and Wolf gave a short proof of the same bound in "A note on Elkin's improvement of Behrend's construction". Tao and Vu, *Additive Combinatorics* (2006), Chapter 10, give Behrend's construction and Roth's theorem with proofs.

Roth's theorem is in Roth, "On certain sets of integers", J. London Math. Soc. 28 (1953) 104-109. The bounds of Section 2 are in Heath-Brown, "Integer sets containing no arithmetic progressions", J. London Math. Soc. (2) 35 (1987) 385-394; Szemerédi, "Integer sets containing no arithmetic progressions", Acta Math. Hungar. 56 (1990) 155-158; Bourgain, "On triples in arithmetic progression", Geom. Funct. Anal. 9 (1999) 968-984; Sanders, "On Roth's theorem on progressions", Ann. of Math. 174 (2011) 619-636; Kelley and Meka, "Strong bounds for 3-progressions", FOCS 2023; and Bloom and Sisask, "The Kelley-Meka bounds for sets free of three-term arithmetic progressions" (2023). For invariant equations and for several equations at once see Ruzsa, "Solving a linear equation in a set of integers I", Acta Arith. 65 (1993), and Shapira, "Behrend-type constructions for sets of linear equations", Acta Arith. 122 (2006).

The docstring of `New/Reduction/Data/Existence.lean` names Shapira's paper as the source of the form with several equations, after Behrend, and compares Alon and Shapira, "A characterization of easily testable induced subgraphs" (2006), Lemma 4.1 in the preprint numbering. The list of references of the source gives these statuses: Alon and Shapira, Lemma 4.1, "compared, place confirmed"; Behrend, PNAS 32, 1946, "work found, no place given"; Shapira, Acta Arith. 2006, "work found, no place given". This book has not compared the statement of `New.exists_three_term_free` with Lemma 4.1 of Alon and Shapira. Mathlib's file on Behrend's construction gives `Behrend.roth_lower_bound` and the lemmas of Section 2, and Mathlib proves Roth's theorem in the form `rothNumberNat_isLittleO_id`.

Volume 1 states the existence of the data, with the sparse set, in [the data exist](/chapter/data-exist/). The uses of sparseness are proved in Volume 11 (the sharpness of the derivatives) and in Volume 12 (the local loss). The notes of the Volume 1 chapter name only Volume 11. The research notes point the uses to the determinant part (`New/Determinant`), but the two uses of Section 5 are in `New/Derivatives/Sharpness` and `New/Congruences/LocalLoss`. The determinant part does not use the sparse set.

### What Volume 2 gave to the argument

Volume 2 collected the analytic and arithmetic results that the reduction of Volume 1 takes from outside the new argument. Each chapter supplies one input.

1. [Dirichlet L-functions and zero symmetry](/chapter/dirichlet-l-functions/) proved the symmetry of the zeros, `New.gammaFactor_eq_zero_or_LFunction_one_sub_eq_zero`, for every Dirichlet character. `New.zeros_on_line` in `New/Main.lean` uses it to pass from nonvanishing in $\operatorname{Re} s > 1/2$ to the zeros on the line. The chapter also built the entire function `New.entireL` and the theta series.
2. [Polar functions and the explicit formula](/chapter/polar-functions/) defined `New.IsPolar` and proved `New.isPolar_primeRemainder`: the transform of the weighted prime remainder continues with simple poles at the zeros. The criterion of `New/Reduction/Zeros/Criterion.lean` uses it.
3. [Landau's theorem](/chapter/landau-theorem/) proved `New.IsPolar.landau`. A one-sided bound for the remainder then forces the residues at the zeros in $\operatorname{Re} s > \beta$ to vanish, in the same criterion.
4. [The prime number theorem in progressions](/chapter/prime-number-theorem/) gave the zero-free region, the Tauberian theorem and the bound $|R_q(y)| \leq (\log y)^{-B}$ for large $y$, which `New/Reduction/OneSidedBound.lean` uses.
5. [Primes in windows](/chapter/primes-in-windows/) proved `New.exists_prime_modEq_one_log_mem`. The data take the primes $p_0$, $p_1$ and $N$ from these windows.
6. [Pólya-Vinogradov and quadratic twists](/chapter/polya-vinogradov/) gives `exists_entireL_quadTwist_ne_zero`, which chooses the prime $d$ of the criterion so that no twist $L(s, \chi \cdot (\cdot/d))$ vanishes in the region of the zero.
7. This chapter gave the set of exponents with no weighted three-term progressions, and with it the sparse set $\Phi_b$ of places of weight $b$.

The first four inputs reduce the theorem to a one-sided bound for the remainders. The last three supply the data at which Volumes 3 to 12 prove that bound. No result of Volume 2 is new mathematics, and nothing here shows that the argument of the later volumes is correct.

Status: drafted by a model. No person has checked this chapter against the Lean source.
