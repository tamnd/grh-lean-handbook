---
title: The five scale inequalities
lean:
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
decls:
  - New.Parameters.constantBound
  - New.Data.le_constantBound
  - New.Data.scale_inequalities
  - New.Data.x_pow_le_x₁
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The five scale inequalities

This section states the axioms of the sizes: the conditions on the parameters, the constant $C_P$, and the five inequalities between the scales. Every other row of the table of Section 3 is a consequence of these and of the explicit choices of the ranks, the field and the primes. The proofs of the consequences are in [the scales](/chapter/data-and-sizes/#the-scales) of Volume 1.

### The parameters

The parameters $P$ are two natural numbers $q_0$ and $d$ with three conditions:

1. $18480 \mid q_0$, where $18480 = 2^4 \cdot 3 \cdot 5 \cdot 7 \cdot 11$ (the field `New.Parameters.dvd_q₀`, FieldsAndPlaces.lean:70);
2. $d$ is prime (`New.Parameters.d_prime`, FieldsAndPlaces.lean:72);
3. $q_0 \mid 2(d + 1)$ and $q_0 \nmid d + 1$ (`New.Parameters.q₀_dvd_and_not_dvd`, FieldsAndPlaces.lean:74).

The third condition says $d \equiv q_0/2 - 1 \pmod{q_0}$. Since $18480 \mid q_0$, it gives $d \geq q_0/2 - 1 \geq 9239$. The source proves the weaker bound $64 < d$ (`New.Parameters.sixty_four_lt_d`, FieldsAndPlaces.lean:136), which is all that it uses. The parameters are fixed for the whole argument. The end of the proof chooses them from the character $\chi$ of the theorem: $q_0 = 18480\,q$ for a character modulo $q$, and $d$ a prime in a fixed class modulo $q_0$ ([the main inequality and the end of the proof](/chapter/main-inequality/)).

### The constant of the parameters

**Definition (The constant of the parameters).** For parameters $P = (q_0, d)$, the constant $C_P$ is
$$C_P = C_{\mathrm{vac}} + (2d + 6) + \Bigl(q_0 + \lvert c_d \rvert + \sum_{w} \bigl\lvert \log \lvert \Phi_{q_0}'(w) \rvert \bigr\rvert \Bigr),$$
where $C_{\mathrm{vac}} \geq 0$ is the constant of the bound for the integral vacuum, $c_d$ is the constant of Chowla and Selberg of $K = \mathbb{Q}(\sqrt{-d})$, $\Phi_{q_0}$ is the cyclotomic polynomial of order $q_0$, and $w$ runs over the primitive $q_0$-th roots of unity in $\mathbb{C}$.

Lean: `New.Parameters.constantBound` (New/Reduction/Data/AdmissibleData.lean).

**Lemma (Lower bounds for the constant).** For all parameters $P$, one has $64 \leq C_P$, $q_0 \leq C_P$, $d \leq C_P$ and $\varphi(q_0) \leq C_P$.

Lean: `New.Data.le_constantBound` (New/Reduction/Data/Magnitudes.lean).

*Proof.* The three terms in the large parentheses other than $q_0$ are at least $0$, and $C_{\mathrm{vac}} \geq 0$. So $C_P \geq q_0 + 2d + 6$. Then $d > 64$ gives the first and the third bound, and $\varphi(q_0) \leq q_0$ gives the fourth. $\square$

**Remark (Formalization).** The constant $C_{\mathrm{vac}}$ is `New.Parameters.vacuumBoundConst`, a natural number that the source defines by `choose` from an existence statement. So it has no formula, and it can be $0$. The definition of $C_P$ adds it with a plus sign, so the lemma above does not depend on its value. What matters is that $C_{\mathrm{vac}}$, and so $C_P$, depends on $P$ only. If it depended on the data, the inequality (S1) below would be circular. The register of findings records, as F-092, that the thresholds of the argument depend on $d$ through $C_P$.

The definition of $C_P$ is in AdmissibleData.lean at line 50, and the lemma is at Magnitudes.lean:56. The source also has an instance that bounds $C_P \leq \log b$ (Magnitudes.lean:430), which the size automation uses.

### The scales and the five inequalities

The data $D$ contain three natural numbers $x$, $x_1$, $b$ and three real numbers $\log x$, $\log x_1$, $\log b$, with the fields `exp_logX`, `exp_logX₁` and `exp_logB` that say $\exp(\log x) = x$, and so on. In the source, $x$, $x_1$ and $b$ as real numbers are the abbreviations `New.Data.x`, `New.Data.x₁`, `New.Data.b` for $\exp$ of the stored logarithms (AdmissibleData.lean:172, 175, 178).

**Lemma (The scale inequalities).** The data $D$ satisfy

$$\begin{aligned}
&\text{(S1)} \quad 10^{12}\, C_P \leq \log\log b, \\
&\text{(S2)} \quad 100 \log\log b \leq \log x, \\
&\text{(S3)} \quad 10^{6} \log x \leq \log x_1, \\
&\text{(S4)} \quad 10^{6} \log x_1 \leq \log b, \\
&\text{(S5)} \quad 6 \log\log x_1 \leq \log\log b .
\end{aligned}$$

Lean: `New.Data.scale_inequalities` (New/Reduction/Data/Magnitudes.lean).

*Proof.* These are five fields of the structure of the data: `New.Data.constantBound_le` (AdmissibleData.lean:98), `New.Data.mul_log_logB_le_logX` (line 100), `New.Data.logX_le_logX₁` (line 102), `New.Data.logX₁_le_logB` (line 104), and `New.Data.log_logX₁_le_log_logB` (line 106). The lemma at Magnitudes.lean:77 packs them into one statement. $\square$

**Remark (Formalization).** In Lean the constants are written `1e12` and `1e6`, which are the real numbers $10^{12}$ and $10^6$. The lemma `New.Data.scale_inequalities` is the list of facts that the size automation passes to `grind`. So every comparison that the source proves by `D.le_of_hasLogBound` reduces to linear arithmetic in the six numbers $\log x$, $\log x_1$, $\log b$, $\log\log x_1$, $\log\log b$ and $C_P$, under these five inequalities. The automation is explained in [the table of sizes of Volume 1](/chapter/data-and-sizes/#the-table-of-sizes).

**Remark (Formalization).** In Mathlib, $\log y = \log \lvert y \rvert$ for $y < 0$ and $\log 0 = 0$. These junk values do not occur in (S1) to (S5). By (S1) and $C_P \geq 64$, $\log\log b > 0$, so $\log b > 1$. Then (S2) gives $\log x > 0$, and (S3) gives $\log x_1 > 0$. So each logarithm in the five inequalities is the logarithm of a number greater than $1$.

### The exponential forms

**Lemma (The scales in exponential form).** The data satisfy $x^{10^6} \leq x_1$, $x_1^{10^6} \leq b$, $(\log x_1)^6 \leq \log b$, and $(\log b)^{100} \leq x$.

Lean: `New.Data.x_pow_le_x₁`, `New.Data.x₁_pow_le_b`, `New.Data.logX₁_pow_le_logB`, `New.Data.logB_pow_le_x` (New/Reduction/Data/Sizes.lean).

*Proof.* Apply $\exp$ to (S3), (S4), (S5) and (S2). The last two steps use $\log x_1 > 0$ and $\log b > 0$ from the remark above. $\square$

The four lemmas are at Sizes.lean:46, 52, 58 and 63. They are the forms in which the docstrings of the source state the scales. For example, the docstring of the main inequality says: "The scales are integers with $(\log b)^{100} \leq x$, $x^{10^6} \leq x_1$, $x_1^{10^6} \leq b$ and $\log\log b \geq 10^{12} C_P$."

### What each inequality says

The inequality (S1) says that $b$ is large in terms of the parameters. It is the only one of the five that involves $P$. Its role is to make every constant that depends on $q_0$ and $d$ negligible against $\log\log b$, and so against $\log x$, $\log x_1$ and $\log b$.

The inequalities (S2), (S3) and (S4) separate the scales. They say $\log b \leq x^{1/100}$, $x_1 \geq x^{10^6}$ and $b \geq x_1^{10^6}$. In the language of degrees, $\log b$ has degree at most $\tfrac{1}{100}$ in $x$, while $x_1$ and $b$ have degree at least $10^6$ and $10^{12}$.

The inequality (S5) is of another kind. It says $\log x_1 \leq (\log b)^{1/6}$. The inequality (S4) says only $\log x_1 \leq 10^{-6}\log b$. Since $\log b$ is huge, (S5) is much stronger than (S4). It does not follow from (S2), (S3) and (S4). It is used where a power of $\log x_1$, or a power of $\log x$ times $\log x_1$, must be small against $\log b$. Section 7 gives the uses.

### The scales in numbers

The five inequalities give a chain of lower bounds. By (S1) and $C_P \geq 64$, $\log\log b \geq 6.4 \cdot 10^{13}$. By (S2), $\log x \geq 6.4 \cdot 10^{15}$. By (S3), $\log x_1 \geq 6.4 \cdot 10^{21}$. By (S4), $\log b \geq 6.4 \cdot 10^{27}$. These bounds are far from the truth, since (S1) alone gives $\log b \geq \exp(6.4 \cdot 10^{13})$. But they show the scale of the numbers. Every explicit constant of a later proof, such as $e^{32}$ in the bound for $\log N$, $3^8$ in the gap, or $10^{10}$ in a filling condition, is smaller than $\log x$ by a huge factor.

This is why the automation of the source can be crude. It adds $1$ to an exponent at each sum, and it bounds $2$ by $e$. It still proves every comparison that the source asks of it, because the margins in the five inequalities are much larger than the constants that the rules add.

**Example (A comparison with a margin).** Consider $q_2 \leq x^{33 q_0 d}$, where $q_2 = (q_0 d)^{s+6}$ and $s$ is the exponent of the tower (`New.Data.q₂_le`, Sizes.lean:146). The proof needs $s + 6 \leq 33 \log x$. The data give $s \leq 32 \log x$ (`New.Data.towerExp_le`, AdmissibleData.lean:122). So it is enough that $6 \leq \log x$. This follows from (S1), (S2) and $C_P \geq 64$. Then $q_0 d \leq e^{q_0 d}$ gives $q_2 \leq \exp((s + 6) q_0 d) \leq x^{33 q_0 d}$. The margin $\log x - 6$ is huge, and the proof uses only a small part of it.
