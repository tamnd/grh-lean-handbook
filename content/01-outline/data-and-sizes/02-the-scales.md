---
title: The scales and the five inequalities
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Reduction/Data/Magnitudes.lean
  - New/Reduction/Data/Sizes.lean
  - New/Reduction/Data/Existence.lean
decls:
  - New.Parameters.constantBound
  - New.Data.le_constantBound
  - New.Data.natX
  - New.Data.constantBound_le
  - New.Data.x_pow_le_x₁
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The scales and the five inequalities

This section defines the constant $C_P$ of the parameters and the three scales $x$, $x_1$, $b$ of the data. It states the five scale inequalities, which are fields of the data, and their exponential forms. At the end it checks the inequalities on the explicit data of the next chapter.

### The constant of the parameters

The argument has many constants that depend on $q_0$ and $d$ but not on $x$. The source puts all of them into one number and asks that $\log\log b$ be much larger than it.

**Definition (The constant of the parameters).** Let $P = (q_0, d)$ be parameters. The constant $C_P$ is
$$C_P = C_{\mathrm{vac}} + (2d + 6) + q_0 + \lvert c_{\mathrm{CS}}(d)\rvert + \sum_{w} \bigl\lvert \log \lvert \Phi_{q_0}'(w)\rvert \bigr\rvert .$$
Here $C_{\mathrm{vac}}$ is the natural number in the bound $\exp(C_{\mathrm{vac}} q_1^2)$ for the conjugates of the values of the integral vacuum, $c_{\mathrm{CS}}(d) = \gamma - \operatorname{Re} (L'/L)(1, \chi_K)$ is the constant of Chowla and Selberg, $\Phi_{q_0}$ is the cyclotomic polynomial of order $q_0$, and $w$ runs over the primitive $q_0$-th roots of unity in $\mathbb{C}$.

Lean: `New.Parameters.constantBound` (New/Reduction/Data/AdmissibleData.lean).

The five terms come from five places of the argument. The integral vacuum is the theta function of rank one whose values Theorem A uses (Volume 9). The constant $c_{\mathrm{CS}}(d)$ is the value of the constant $c_q$ of the prime remainder that [the weighted prime remainder](/chapter/weighted-prime-remainder/) computes. The derivative $\Phi_{q_0}'(w)$ at a root $w$ is the factor at $w$ in the discriminant of $\mathbb{Q}(\zeta_{q_0})$, since $\prod_w \Phi_{q_0}'(w)$ is that discriminant up to sign. The term $2d + 6$ enters, next to $C_{\mathrm{vac}}$, the bound in Theorem A for the action of the Weil representation on the vacuum.

**Remark (Formalization).** The number $C_{\mathrm{vac}}$ is `New.Parameters.vacuumBoundConst`, and the source defines it by `choose` from an existence statement (`New.Parameters.exists_mul_vacElem_integral_bounded`), which gives one constant for every exponent $s$ of the tower. So it has no formula: the argument uses only the bound that it satisfies. Its definition takes only $P$ as input, so $C_P$ depends on $q_0$ and $d$ and on nothing else. This matters, since the data contain the inequality $10^{12} C_P \leq \log\log b$: if $C_P$ depended on the data, the inequality would be circular. The definition of $C_P$ is the reason that the file of the data imports a file of Theorem A. So the data are not at the bottom of the imports of the source.

**Lemma (Lower bounds for the constant).** For all parameters $P$,
$$64 \leq C_P, \qquad q_0 \leq C_P, \qquad d \leq C_P, \qquad \varphi(q_0) \leq C_P .$$

Lean: `New.Data.le_constantBound` (New/Reduction/Data/Magnitudes.lean).

*Proof.* The terms $C_{\mathrm{vac}}$, $\lvert c_{\mathrm{CS}}(d)\rvert$ and the sum are at least $0$. So $C_P \geq q_0 + 2d + 6$. The prime $d$ satisfies $d > 64$ (`New.Parameters.sixty_four_lt_d`), because $q_0 \mid 2(d+1)$ and $q_0 \geq 18480$. So each of $64$, $q_0$, $d$ is at most $C_P$. Last, $\varphi(q_0) \leq q_0$. $\square$

The lemma is weak on purpose: it is all that the sizes need. The true value is larger. Since $q_0 \mid 2(d + 1)$, one has $d \geq q_0/2 - 1 \geq 9239$, and so $C_P \geq 18480 + 2 \cdot 9239 + 6 = 36964$.

### The scales

**Definition (The scales).** The data $D$ for the parameters $P$ contain three natural numbers $x$, $x_1$, $b$ and three real numbers $\log x$, $\log x_1$, $\log b$ with
$$\exp(\log x) = x, \qquad \exp(\log x_1) = x_1, \qquad \exp(\log b) = b .$$
The number $x$ is the length of the prime sum. The number $x_1$ is the second cut-off. The number $b$ is the weight at the $b$-places (Section 4).

Lean: `New.Data.natX`, `New.Data.natX₁`, `New.Data.natB`, `New.Data.logX`, `New.Data.logX₁`, `New.Data.logB`, `New.Data.exp_logX`, `New.Data.exp_logX₁`, `New.Data.exp_logB` (New/Reduction/Data/AdmissibleData.lean).

So the three scales are integers, and the data store their logarithms. The real numbers $\exp(\log x)$, $\exp(\log x_1)$, $\exp(\log b)$ are `New.Data.x`, `New.Data.x₁`, `New.Data.b`. The data do not ask $x \leq x_1 \leq b$ directly. The order follows from the scale inequalities.

**Definition (The scale inequalities).** The data satisfy the five inequalities
$$\begin{aligned}
&\text{(S1)} \quad 10^{12}\, C_P \leq \log\log b, \\
&\text{(S2)} \quad 100 \log\log b \leq \log x, \\
&\text{(S3)} \quad 10^{6} \log x \leq \log x_1, \\
&\text{(S4)} \quad 10^{6} \log x_1 \leq \log b, \\
&\text{(S5)} \quad 6 \log\log x_1 \leq \log\log b .
\end{aligned}$$

Lean: `New.Data.constantBound_le`, `New.Data.mul_log_logB_le_logX`, `New.Data.logX_le_logX₁`, `New.Data.logX₁_le_logB`, `New.Data.log_logX₁_le_log_logB` (New/Reduction/Data/AdmissibleData.lean); the conjunction of the five is `New.Data.scale_inequalities` (New/Reduction/Data/Magnitudes.lean).

The inequality (S1) says that $b$ is large in terms of $P$. The inequalities (S2) to (S4) separate the four scales. The inequality (S5) is of another kind. It says $\log x_1 \leq (\log b)^{1/6}$, while (S4) says only $\log x_1 \leq 10^{-6} \log b$. So (S5) is much stronger than (S4), and it does not follow from (S2) to (S4). It is used where a power of $\log x_1$ must be small against $\log b$, for example in the bound $x_1^{3 l_0^2} \leq \sqrt b$ of Section 3.

**Remark (Formalization).** In Mathlib, $\log y = \log\lvert y\rvert$ for $y < 0$, and $\log 0 = 0$. So $\log\log b$ in (S1) is defined for every real $\log b$. The junk values do not occur: $b = \exp(\log b)$ is a natural number, so $\log b \geq 0$, and (S1) with $C_P \geq 64$ gives $\log\log b > 0$, so $\log b > 1$. Then (S2) gives $\log x > 0$, and (S3) gives $\log x_1 > 0$. So all the logarithms in the five inequalities are logarithms of numbers greater than $1$.

### The exponential forms

**Lemma (The scales in exponential form).** The data satisfy
$$x^{10^6} \leq x_1, \qquad x_1^{10^6} \leq b, \qquad (\log x_1)^6 \leq \log b, \qquad (\log b)^{100} \leq x .$$

Lean: `New.Data.x_pow_le_x₁`, `New.Data.x₁_pow_le_b`, `New.Data.logX₁_pow_le_logB`, `New.Data.logB_pow_le_x` (New/Reduction/Data/Sizes.lean).

*Proof.* Apply $\exp$ to (S3) and (S4): $x^{10^6} = \exp(10^6 \log x) \leq \exp(\log x_1) = x_1$, and in the same way $x_1^{10^6} \leq b$. Apply $\exp$ to (S5) and (S2): $(\log x_1)^6 = \exp(6 \log\log x_1) \leq \log b$, and $(\log b)^{100} = \exp(100 \log\log b) \leq x$. These steps use $\log x_1 > 0$ and $\log b > 0$ from the remark above. $\square$

**Example (The scales in numbers).** The four exponential forms and (S1) give a chain of lower bounds. First $\log\log b \geq 6.4 \cdot 10^{13}$. Then $\log x \geq 100 \log\log b \geq 6.4 \cdot 10^{15}$. Then $\log x_1 \geq 10^6 \log x \geq 6.4 \cdot 10^{21}$, and $\log b \geq 10^{6}\log x_1 \geq 6.4 \cdot 10^{27}$. They are far from the truth, since (S1) alone gives $\log b \geq \exp(6.4 \cdot 10^{13})$. So every constant that appears in a later proof, such as $2^{22}$, $3^8$ or $e^{32}$, is smaller than $\log x$ by a very large factor. So a proof can absorb such a constant without comment.

### Admissible scales: the model case

The scale inequalities have a model, which the next chapter constructs. Fix $\varepsilon$ with $0 < \varepsilon < 1/100$. The existence theorem ([the data exist](/chapter/data-exist/)) states: for every large integer $x$ there are data $D$ whose first scale is $x$, with
$$x_1 = \bigl\lfloor \exp(x^{\varepsilon/6}) \bigr\rfloor,$$
with $b$ the least multiple of $q_1 x_1$ that is greater than $\exp(x^{\varepsilon})$, with $m$ the least power of $2$ that is at least $\sqrt x$, and with $r$ the least power of $3$ that is at least $x^5$. These data have $x^{\varepsilon/6} - 1 \leq \log x_1$ and $x^{\varepsilon} \leq \log b \leq x^{\varepsilon} + 1$ ([Theorem](/decl/New.eventually_exists_data/)).

In the model, $\log x_1 \approx x^{\varepsilon/6}$ and $\log b \approx x^{\varepsilon}$. Here is why the five inequalities hold for large $x$.

1. (S2): $100 \log\log b \leq 100 \log(x^\varepsilon + 1)$, which is about $100\varepsilon \log x$. This is less than $\log x$ for large $x$, because $100 \varepsilon < 1$. This is the reason for $\varepsilon < 1/100$.
2. (S3): $10^6 \log x \leq x^{\varepsilon/6} - 1$ for large $x$, since a power of $x$ grows faster than $\log x$.
3. (S4): $10^6 \log x_1 \leq 10^6 x^{\varepsilon/6} \leq x^\varepsilon \leq \log b$ for large $x$.
4. (S5): $\log x_1 \leq x^{\varepsilon/6}$, since $x_1 \leq \exp(x^{\varepsilon/6})$. So $(\log x_1)^6 \leq x^{\varepsilon} \leq \log b$. This is the reason for the exponent $\varepsilon/6$.
5. (S1): $\log\log b \geq \varepsilon \log x$, which tends to infinity, while $C_P$ is fixed.

So in the model all scales are fixed functions of $x$, and the inequalities hold from some point on. The data of the source ask only for the five inequalities and the ranges of the next sections. Only the end of the proof ([the main inequality and the end of the proof](/chapter/main-inequality/)) uses the existence theorem, to pass from data to the one-sided bound for the prime remainder.
