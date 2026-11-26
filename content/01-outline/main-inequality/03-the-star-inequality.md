---
title: The main inequality
lean:
  - New/Reduction/MainInequality.lean
  - New/Reduction/Data/Magnitudes.lean
decls:
  - New.star_inequality
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The main inequality

This section proves the main inequality $m \cdot \mathrm{rem} \leq f a \log^5 b$. It is the only place where Theorems A, B and C meet. The proof is the model of Section 1 with the exact objects: one family of target forms, a covolume bounded from above by Theorems A and B, and from below by Theorem C. The section ends with the budget of the errors, dimension by dimension.

### The statement

**Theorem (The main inequality).** Let $P$ be parameters: a multiple $q_0$ of $18480$ and a prime $d \equiv q_0/2 - 1 \pmod{q_0}$. Let $D$ be admissible data for $P$. Then

$$m \cdot \mathrm{rem} \;\leq\; f \, a \log^5 b.$$

Lean: `New.star_inequality` (New/Reduction/MainInequality.lean).

The theorem has no other hypothesis. All the conditions on the scales are fields of $D$ (Section 2 lists the ones that this chapter uses). The inequality is one-sided. It bounds $\mathrm{rem}$ from above and says nothing about a lower bound. Landau's criterion needs only an upper bound (Section 6), so this is enough.

### The idea of the proof

Fix the number

$$h \;=\; \mathrm{main} - m \cdot \mathrm{rem} + L, \qquad L = f a \log^4 b.$$

Theorems A (a) and B give about $d_T$ independent lattice vectors of squared length at most $e^h$, so a covolume at most $d_T h$ and a small index. Theorem C bounds the covolume plus twice the index from below by $d_T(\mathrm{main} - 3L)$. The term $d_T \cdot \mathrm{main}$ cancels, and $d_T \cdot m \cdot \mathrm{rem}$ is left against errors of order $d_T f a \log^4 b$.

### The proof

*Proof.* The proof has eight steps. Write $I = 10 \log(1 + 2b^2) \cdot f a \log^3 b$ for the index per dimension.

*Step 1: the translates.* By [Theorem B](/decl/New.Data.enough_forms/), $d_T > 0$, and there is a finite set $t \subseteq G$ with $\#t \cdot \dim \mathrm{src} \leq 5 d_T \log(1 + 2b^2)$ and $(1 - 4/b^2) d_T \leq \dim \sum_{g \in t} g \mathfrak{p}(\mathrm{src})$.

*Step 2: the short forms.* Let $S$ be the set of integral source forms $\varphi$ with $\|\Theta_1 \, g \mathfrak{p} \, \varphi\|_\sigma^2 \leq e^h$ for all $g \in G$ and all $\sigma$. By [Theorem A (a)](/decl/New.Data.span_short_integralRamified_eq_top/), $S$ spans $\mathrm{src}$.

*Step 3: the family.* Let $Y = \bigcup_{g \in t} g \mathfrak{p}(S)$. Since $S$ spans $\mathrm{src}$ and each $g \mathfrak{p}$ is linear, $Y$ spans $\sum_{g \in t} g \mathfrak{p}(\mathrm{src})$. A spanning set of a finite-dimensional space contains a basis. So there are $y_1, \dots, y_n$ in $Y$, linearly independent, with $n = \dim \sum_{g \in t} g \mathfrak{p}(\mathrm{src})$. By Step 1, $n \geq (1 - 4/b^2) d_T$. Since the $y_i$ are independent in $T$, $n \leq d_T$.

*Step 4: the covolume.* Each $y_i$ is $g \mathfrak{p} \varphi$ with $g \in t$ and $\varphi \in S$. So $\|\Theta_1 y_i\|_\sigma^2 \leq e^h$ for every $\sigma$. By [Hadamard's inequality](/decl/New.TwistedLattice.covolumeLe_of_normSqAt_le/), $y$ has covolume at most $n h$.

*Step 5: the index.* Each $\varphi \in S$ is integral. So [Theorem A (b)](/decl/New.Data.indexLe_normalizedPoincare/) applies to $y$ and $t$, and $y$ has index at most

$$\#t \cdot \dim \mathrm{src} \cdot 2 f a \log^3 b \;\leq\; 5 d_T \log(1 + 2b^2) \cdot 2 f a \log^3 b \;=\; d_T \, I.$$

The inequality is Step 1. An index bound remains true for a larger number, so $y$ has index at most $d_T I$.

*Step 6: the lower bound.* The family $y$ is independent, $n \geq (1 - 4/b^2) d_T$, its index is at most $d_T I$ and its covolume is at most $n h$. By [Theorem C](/decl/New.Data.integral_forms_long/),

$$d_T (\mathrm{main} - 3L) \;\leq\; n h + 2 d_T I. \tag{3.1}$$

*Step 7: the cancellation.* By [the bound for the main amount](/decl/New.Data.mainAmount_nonneg/), $\mathrm{main} \geq 0$, and $L > 0$. Since $n \leq d_T$,

$$n (\mathrm{main} + L) \;\leq\; d_T (\mathrm{main} + L). \tag{3.2}$$

Now $n h = n(\mathrm{main} + L) - n \, m \cdot \mathrm{rem}$. Insert this into (3.1), and use (3.2):

$$d_T (\mathrm{main} - 3L) \;\leq\; d_T (\mathrm{main} + L) - n \, m \cdot \mathrm{rem} + 2 d_T I.$$

The terms $d_T \cdot \mathrm{main}$ cancel, and

$$n \, m \cdot \mathrm{rem} \;\leq\; d_T \cdot \mathrm{err}, \qquad \mathrm{err} = 4L + 2I. \tag{3.3}$$

*Step 8: division by $n$.* The scales give $4/b^2 \leq 1/2$. So $d_T = 2(1 - 1/2) d_T \leq 2(1 - 4/b^2) d_T \leq 2n$. Since $d_T > 0$, $n > 0$. From (3.3), $n \, m \cdot \mathrm{rem} \leq d_T |\mathrm{err}| \leq 2n |\mathrm{err}| = n |2 \mathrm{err}|$. Divide by $n$:

$$m \cdot \mathrm{rem} \;\leq\; |2 \, \mathrm{err}| \;=\; 8 f a \log^4 b + 40 \log(1 + 2b^2) \cdot f a \log^3 b.$$

The last step is a comparison of sizes. Since $b \geq 3$, $\log(1 + 2b^2) \leq \log(3 b^2) \leq 3 \log b$. So $|2 \mathrm{err}| \leq 128 f a \log^4 b$. The data have $\log \log b \geq 10^{12} c_P \geq 64 \cdot 10^{12}$, so $\log b \geq 128$, and $128 f a \log^4 b \leq f a \log^5 b$. $\square$

**Remark.** The comparison in Step 7 is the heart of the method. Theorem A bounds the length of a form by $\mathrm{main} - m \cdot \mathrm{rem}$ plus an error. Theorem C bounds the covolume from below by $d_T \cdot \mathrm{main}$ minus an error. The main amount is at least $x^4 f a$. It is larger than every error by a factor of at least $x^4/\log^4 b$. So the method needs the main amount to be the same number in both theorems, and the data are designed for this.

**Remark.** Step 7 needs $\mathrm{main} + L \geq 0$, because the family has $n \leq d_T$ members and not exactly $d_T$. If $h$ were negative, the inequality $n h \leq d_T h$ would fail. The missing $d_T - n$ dimensions are at most $4 d_T / b^2$, but Step 7 does not use this: it uses only the sign of $\mathrm{main} + L$, and the number of missing dimensions enters only through $n \geq d_T/2$ in Step 8.

**Remark (Formalization).** The family in Step 3 is chosen by a lemma of Mathlib that extracts a linearly independent family, indexed by $\mathrm{Fin}\, n$ with $n$ the dimension of the span, from a spanning set (`exists_fun_fin_finrank_span_eq` (Mathlib)). The source writes the error with an absolute value $|2 \mathrm{err}|$, because the final comparison of sizes is made for $|2 \mathrm{err}|$. Since $\mathrm{err} > 0$, the absolute value changes nothing. The final comparison $|2 \mathrm{err}| \leq f a \log^5 b$ is proved by the size automation of the source, `New.Data.le_of_hasLogBound`. This tactic compares the exponents of two monomials in the scales, with the five scale inequalities. It proves the same inequality as the computation above, with other intermediate constants. [The data and its sizes](/chapter/data-and-sizes/) describes it.

### The errors per dimension

The proof has three sources of error. The source lists them in a table, per dimension of the target.

| source | where | amount per dimension |
|---|---|---|
| size | Theorem A (a) | $f a \log^4 b$ |
| index | Theorems A (b) and B | $20 \log(1 + 2b^2) \cdot f a \log^3 b$ |
| covolume | Theorem C | $3 f a \log^4 b$ |

The index enters twice in Theorem C, and the table shows the doubled amount $2I$. The sum of the three rows is $\mathrm{err} = 4L + 2I$. The family has at least $d_T/2$ members, so $m \cdot \mathrm{rem}$ is at most twice the sum, and twice the sum is at most $f a \log^5 b$.

Every error is $f a$ times a power of $\log b$, and so smaller than the main amount $x^4 f a$ by a factor $x^4/\log^5 b$. Section 4 divides by $m$, and this saving $1/m$ is the saving of the whole method.

### What cancels, and where

The main inequality is the last of several cancellations, which the head of the source file lists. The others are inside earlier proofs: the gains $\sum_\ell \mathrm{gain}_\ell \log \ell$ against $\log c_B$ in Theorem A (a); the constant $c_1 = \operatorname{Re} G_1(1)$ between the period and the expected value of the prime sums; the excesses of the $m$ lifts against $a \log N$, up to $O(a \log b)$; the main terms $\log x$, $\log x_1$ and $c_1$ in the identity for the total remainder; and a constant that depends on $q_0$, between the two cut-offs. [Why a lattice can bound a prime sum](/chapter/lattice-and-prime-sum/) explains the first of these.

### The budget in the compact edition

The source has a second edition, `grh-compact`, which proves the same theorem in fewer lines. Its main file opens with the clearest single statement of the budget. The rest of this subsection is taken from the head of that file, in the notation of this book. It is not the edition that this book follows, and some amounts differ.

The compact edition writes the spine as one chain of inequalities, for one family of target forms:

$$\mathrm{main} \;\leq\; \frac{V + 2\delta}{d_T} \;\leq\; \mathrm{main} - m \cdot \mathrm{rem},$$

up to errors, where $e^V$ bounds the squared covolume of the lifts at all conjugates and $\delta$ bounds the logarithm of the index.

Among the scales it lists, one comment matters here: $m$, the number of lifts, lies in $[\sqrt{x}, 2\sqrt{x}]$, and "the saving $x^{-1/2}$ is $1/m$".

It lists the errors per dimension, with $L = f a \log^4 b$:

| source | compact edition |
|---|---|
| length, Theorem A (a) | $L$ |
| missing dimensions, Theorem B | $4 b^{-2} \cdot b^2 x^{99}$ |
| index, Theorems A (b) and B | $2 \cdot 5 \log(1 + b^2) \cdot f a \log^3 b$ |
| covolume, Theorem C | $3L$ |

and says that their sum is at most $f a \log^5 b$, and that exponents such as $99$ are slack: every power of $x$ that occurs is below $b$.

**Remark (Formalization).** The two editions treat the missing dimensions in different ways. The compact edition bounds $-h$ by a crude bound $b^2 x^{99}$ for $|\mathrm{main} + \mathrm{rem}|$, and pays $(d_T - n)(-h) \leq (4/b^2) d_T \cdot b^2 x^{99}$. The readable edition uses only $\mathrm{main} + L \geq 0$ (Step 7), and has no row for the missing dimensions. The two editions also state the index of Theorem A (b) with $\log(1 + b^2)$ and $\log(1 + 2b^2)$. In both editions the main inequality reads $m \cdot \mathrm{rem} \leq f a \log^5 b$: the compact edition writes it as `star_inequality` (grh-compact), with the bound $\log^2 b$ times its `budget` $f a \log^3 b$. Findings F-113 and F-114 of Volume 0 record the differences of the two editions.
