---
title: Exercises and notes
lean:
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/Data/Existence.lean
  - New/Reduction/OneSidedBound.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises ask the reader to redo some size comparisons of the chapter by hand. Each one uses only the table of Section 3 and the five inequalities (S1) to (S5) of Section 2. Each one has a hint. None of them needs the source, but a reader who wants to compare the answer with the source can find the lemma that the exercise names.

**Exercise 1.** Show that $(\log b)^{100} \leq x$ follows from (S2). Then show that $x^{1/2} \geq (\log b)^{50}$, and conclude that the first term $\varphi(q_0) (\log b)^6/m$ of the error budget is at most $\varphi(q_0)(\log b)^{-44}$.

*Hint.* Apply $\exp$ to $100 \log\log b \leq \log x$. For the last part, use $m \geq \sqrt{x}$ from the table. Compare with `New.Data.logB_pow_le_x` (Sizes.lean:63).

**Exercise 2.** Show that $x_1^{10^6} \leq b$ and $x^{10^{12}} \leq b$ follow from (S3) and (S4). Then show that $x^{999} \leq a/x_1$, where $a = x b$.

*Hint.* For the last part, write $a/x_1 = \exp(\log x + \log b - \log x_1)$ and use $\log x_1 \leq 10^{-6} \log b$. Compare with `New.Data.x₁_pow_le_b` (Sizes.lean:52) and `New.Data.a_div_x₁_mem_Icc` (Sizes.lean:182).

**Exercise 3.** Show that (S4) does not imply (S5). That is, find real numbers $X_1 > e$ and $B > e$ with $10^6 \log X_1 \leq \log B$ and $6 \log\log X_1 > \log\log B$.

*Hint.* Take $\log B = 10^6 \log X_1$. Then (S5) reads $(\log X_1)^6 \leq 10^6 \log X_1$, that is $(\log X_1)^5 \leq 10^6$. Take $\log X_1 = 100$.

**Exercise 4.** The level satisfies $\log N \in [m \log b, 30 m \log b]$, and $m = 2n$ for the shape of the data. Show that $N \leq b^{60 n}$. Then show that the bound $\log N \leq 31 m \log b$ would not be enough for this conclusion.

*Hint.* For the second part, note that $31 m \log b = 62 n \log b$, and that $b^{62 n} > b^{60 n}$ since $b > 1$. Compare with `New.Data.N_le_pow` (Spanning/Unfolding/FillingAdmissible.lean:725).

**Exercise 5.** The number of lifts satisfies $\sqrt{x} \leq m \leq 2\sqrt{x}$, and $k \geq e^{-2} x^5$. Show that $1000\, m^9 \leq k$ and $m^7 \leq 2^7 k$ once $\log x$ is large. Find the exponent $\alpha$ such that $1000\, m^9 \leq k$ would fail for $m \approx x^{\alpha}$ with $\alpha$ above it.

*Hint.* $m^9 \leq 2^9 x^{9/2}$. The condition $1000 m^9 \leq k$ with $k \approx x^5$ asks $9 \alpha < 5$, so $\alpha = 5/9$.

**Exercise 6.** In the sparseness bound `New.mul_rank_lt_two_pow` (Existence.lean:405), the exponent $22$ appears in $2^s = m^{22}$. Suppose the source had $2^s = m^{20}$ instead. With $m \approx \sqrt{x}$, $k t \geq 5 x^{10}$ and $l_0 \geq 1$, show that $2 l_0 (k t + 1) < 2^s$ can fail.

*Hint.* With $m = \sqrt{x}$, $m^{20} = x^{10}$, while $2 l_0 (k t + 1) > 10 x^{10}$.

**Exercise 7.** The remainders at $x_1$ are at most $x^{-2}$ when $\log x_1 \geq x^{\varepsilon/12}$ (`New.eventually_abs_primeRemainder_exp_le`, OneSidedBound.lean:95). Suppose instead that one knew only $\log x_1 = 10^6 \log x$, as (S3) allows, and the bound $\lvert R(y) \rvert \leq (\log y)^{-B}$. Show that $\lvert R(x_1) \rvert \leq (10^6 \log x)^{-B}$, and explain why this does not give $\lvert R(x_1) \rvert \leq x^{-1/2}$ for large $x$.

*Hint.* For each fixed $B$, $(\log x)^{-B}$ decays more slowly than every power $x^{-c}$ with $c > 0$.

**Exercise 8.** The tower degree is $\operatorname{towerDeg}(s) = 3^{\lfloor \log_3 s \rfloor + 5}\, 2^s$, with $2^s = m^{22}$ and $s \leq 32 \log x$. Show that $\operatorname{towerDeg}(s) \leq 3^5 \cdot 2^{22} (s + 1)\, x^{11}$, and use (S1), (S3) and (S5) to show that this is at most $x^{11} (\log b)^{1/5}$ once $\log\log b$ is large.

*Hint.* Use $3^{\lfloor \log_3 s\rfloor} \leq s$ and $s + 1 \leq 33 \log x$. By (S3), $\log x \leq \log x_1$, and by (S5), $\log x_1 \leq (\log b)^{1/6}$. The remaining factor $(\log b)^{1/30}$ absorbs the constant.

## Notes and references

The table of this chapter is a guide to the sizes. It is not a part of the formal proof, and it does not replace the source. Each row names a declaration, a file and a line, so that the reader can check the row against the Lean statement. The line numbers refer to the source at the time of writing and can move when the source changes. The names of the declarations are more stable than the line numbers.

The order of the scales and the five inequalities are those of [the data and their sizes](/chapter/data-and-sizes/) in Volume 1. That chapter has its own [table of sizes](/chapter/data-and-sizes/#the-table-of-sizes), arranged by file. This chapter arranges the sizes by role, and it adds the uses in the later parts and the reasons for the gaps. The existence of the data is the subject of [the existence of the data](/chapter/data-exist/), and the error budget is the subject of [the main inequality and the end of the proof](/chapter/main-inequality/).

The reasons for the gaps in Section 7 are the reading of this chapter. The source states each size condition where it is used, but it does not collect the reasons. A reader who finds a use with less margin than the uses listed here can add it to the table.

The research notes of the project contain three statements on sizes that the Lean source does not support as written. First, research note b, §1.4, says that $N \approx b^m$. The source gives only $\log N \in [m \log b, 30 m \log b]$ (`New.Data.log_N_mem_Icc`, LevelAndTwists.lean:234). Second, the same section gives the range of the level primes as $(b^2, N)$. The field `levelPrime_mem` of the data gives $[b^{10}, b^{11}]$. The range $(b^2, N)$ is the weaker consequence `levelPrime_mem_Ioo`. Third, research note d, §3, lists $r + 10^8 n^4 \leq k$ with the conditions on the ranks of the data. In the source, this condition has a local $r$ of the section in Spanning/Frames/FiniteShells.lean, and it is used with $r = k - n^7$. For the rank $r$ of the data, the condition is false, since $r = k + m - 1 > k$. The exponent $s$ of the sizes at a real place is also not the exponent of the tower (Section 6).

Three results of the literature enter the construction of the sizes. The prime windows of Section 4 are, as the source says, a consequence of the Siegel-Walfisz theorem. The source cites H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I: Classical Theory*, Cambridge University Press, 2007, Corollary 11.19, and proves the form that it needs in Lib/Analytic/Primes.lean. The sets of weights without three-term relations come from a construction of Behrend type. The source cites A. Shapira, "Behrend-type constructions for sets of linear equations", *Acta Arithmetica* (2006), after F. A. Behrend, *Proc. Nat. Acad. Sci. USA* 32 (1946), and compares N. Alon and A. Shapira, "A characterization of easily testable induced subgraphs" (2006), Lemma 4.1 in the preprint numbering (Reduction/Data/Existence.lean, lines 33 to 35). The prime number theorem with a saving of a power of the logarithm, used at $x_1$, is the classical prime number theorem for arithmetic progressions. In the source it is `New.eventually_abs_primeRemainder_le` (Reduction/Zeros/PrimeNumberTheorem.lean:217).

The register of findings records the dependence of the thresholds on $d$ through $C_P$ as F-092, and the difference between `levelPrime_mem` and `levelPrime_mem_Ioo` as F-119.
