---
title: Exercises and notes
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Show that the field `New.Data.towerExp_le` of the data, $s \leq 32\log x$, follows from the other fields. Find the least value of $\log x$ for which your argument works, and compare it with the lower bound for $\log x$ that the scale inequalities give.

*Hint.* Use $m = 2^{e+1} \leq 2\sqrt x$ and $s = 22(e + 1)$, as in the remark of Section 3. One gets $s \leq 22 + (11/\log 2)\log x$.

**Exercise 2.** Compute, with the rules of Section 6, an upper and a lower exponent of $n_m = k + m(t + 1)$ from the exponents of $k$, $m$ and $t$ in the table. Check that you get $5.5L + 12$ and $5.5L$, with $L = \log x$. Then use the rules to prove $n_m \leq \tfrac12\Delta$, and say how large the margin is.

*Hint.* The rule for sums adds $1$ to the upper exponent at each sum. The lower exponent of $\tfrac12\Delta$ is $40L$.

**Exercise 3.** Prove that the off weight $x b / x_1$ is an integer divisible by $q_1$, and that $\kappa(\tau) = a / x_1$ holds as an equation of real numbers. Which field of the data does the proof use? Give data, with all fields except this one, for which the natural number $x b / x_1$ of the source differs from the real number $a / x_1$.

*Hint.* The field is `New.Data.dvd_natB`. Without it, take $x_1$ prime to $x b$.

**Exercise 4.** Prove that exactly $\operatorname{towerDeg}(s)$ places of $E$ have class $-1$ modulo $q_0$. Deduce that $\#\Phi_b \leq \#\Phi_a$, and so that $\#\Phi_a/\log b \leq \#\Phi_b \leq \#\Phi_a$.

*Hint.* The places with a given class modulo $q_0$ form a coset of the kernel $\Phi_a$ of the reduction map. Use $\Phi \cong (\mathbb{Z}/q_1)^\times$ and the lemma on $\#\Phi_a$ in Section 4.

**Exercise 5.** In the theorem on the size of $N_-$ (Section 5), the hypothesis is $2 \leq m$. Show that the lower bound $m L \leq \log N_-$ follows from the proof for every real $m \geq 53/36$, and that it can fail for $m = 1$. Why does the source not need the case $m = 1$?

*Hint.* The proof gives $\log N_- \geq 19(m - 1)L - \tfrac{15}{2}L$. For $m = 1$, take all weights equal to $1$.

**Exercise 6.** Prove $q_1 \leq x^{12}$ without the automation, using only the table and the scale inequalities. Then prove the stronger bound $q_1 \leq x^{11 + 1/100}$.

*Hint.* Write $q_1 = q_0 \cdot 3 l_0 \cdot 2^s$ and bound each factor, as in Section 3. For the stronger bound use $(\log b)^{100} \leq x$ and $C_P \leq \log\log b$.

**Exercise 7.** Check the five scale inequalities for the model data of Section 2 with $\varepsilon = 1/200$. For which $x$, roughly, do (S2) and (S3) hold? Which of the five inequalities needs the largest $x$?

*Hint.* (S1) asks at least $\varepsilon\log x \geq 6.4 \cdot 10^{13}$, which is far beyond the others. For (S3) compare $10^6 \log x$ with $x^{1/1200}$.

## Notes and references

The data of this chapter are the objects that the method of the source lets grow with $x$. The textbook analogue is the choice of auxiliary parameters in a transcendence proof: a few integers, chosen at the start, whose relative sizes make every error term small. The source records the sizes as fields and lemmas, and the five scale inequalities replace the usual phrase "for $x$ large enough in terms of $q_0$ and $d$". So every threshold of the argument is explicit, but the thresholds are huge: $\log\log b \geq 6.4 \cdot 10^{13}$.

The constant $C_P$ depends on $q_0$ and $d$. So the thresholds for $x$ depend on $d$, and the argument uses one $d$ at a time (finding F-092 of the [register of findings](/chapter/register-of-findings/)). The relation $2^s = m^{22}$ fixes the field $E$, and $q_1 = 3 l_0 m^{22} q_0$ (F-093). The bound $\log h_E \leq x^{30}$ and the two windows $[m\log b, 24 m\log b]$ for $\log N_-$ and $[m\log b, 30 m\log b]$ for $\log N$ are recorded as F-098. The second window adds the width $\sqrt{\log b}$; the two are not in conflict.

The class number bound in Section 5 is a crude form of Minkowski's theorem that each ideal class contains an integral ideal of norm at most the Minkowski bound. See Neukirch, *Algebraic Number Theory*, Chapter I, §5 (Minkowski theory) and §6 (the finiteness of the class number). The bound $\mathrm{rd}_E \leq q_1 d$ comes from the different of $E$; for the different and the discriminant see Neukirch, Chapter III, §2. The constant $c_{\mathrm{CS}}(d)$ takes its name from S. Chowla and A. Selberg, "On Epstein's zeta-function", J. Reine Angew. Math. 227 (1967), 86 to 110.

The sparse condition on $\Phi_b$ is a condition of the type of F. A. Behrend, "On sets of integers which contain no three terms in arithmetical progression", Proc. Nat. Acad. Sci. USA 32 (1946), 331 to 332. The construction of a set that is both dense, in the sense $\operatorname{towerDeg}(s) \leq \#\Phi_b\log b$, and sparse is in [the data exist](/chapter/data-exist/). The source cites Shapira (Acta Arithmetica, 2006) for it; that chapter gives the details.

Status: drafted by a model. No person has checked this chapter against the Lean source.
