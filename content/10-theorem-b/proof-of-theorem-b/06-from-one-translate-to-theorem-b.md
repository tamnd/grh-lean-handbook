---
title: From one translate to Theorem B
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/UpperBound/Size/ShortColumns.lean
decls:
  - New.Data.invGainFactor
  - New.Data.invGainFactor_pos
  - New.Data.seesawConst
  - New.Data.scaledInclusion
  - New.Data.projectedPoincare
  - New.Data.normalizedPoincare
  - New.Data.range_normalizedPoincare
  - New.Data.five_halves_mul_one_add_log_le
  - New.Data.targetDim_pos
  - New.Data.exists_le_finrank_iSup_range_normalizedPoincare
  - New.Data.enough_forms
status: drafted
drafted_by: writer@claude-opus-5-5
---
## From one translate to Theorem B

This section proves Theorem B from [the theorem on one translate](/chapter/proof-of-theorem-b/#one-translate). It defines the maps $s\mathfrak{p}$ of the statement, shows that their ranges are images of the ramified forms under $\mathfrak{g}_s$, applies the greedy cover, and restricts to the ramified forms.

### The normalized maps

The maps of the statement carry two scalars from Theorem A.

**Definition (The inverse gain factor).** $c_B = \prod_l l^{-g_l}$, the product over the non-split primes $l$ below $x_1$ and the prime $N$, where $g_l = D.\mathtt{gainExponent}\ l$ is an integer. It is a rational number.

Lean: `New.Data.invGainFactor` (New/Reduction/ShortAndEnough.lean).

**Lemma (The inverse gain factor is positive).** $c_B > 0$.

Lean: `New.Data.invGainFactor_pos` (New/Reduction/ShortAndEnough.lean).

*Proof.* Each $l$ in the product is prime, so $l > 0$, and an integer power of a positive rational is positive. $\square$

**Definition (The seesaw constant).** $c_{ss}$ is a unit of $\mathbb{C}$ for which the seesaw identity of Theorem A holds with the linear form $D.\mathtt{besselForm}$ and the point $D.\mathtt{besselPoint}$.

Lean: `New.Data.seesawConst` (New/Reduction/ShortAndEnough.lean).

**Remark (Formalization).** The seesaw constant is chosen: it is `(D.seesaw_identity D.besselForm D.besselPoint).choose`. Its type is `ℂˣ`, so it is a nonzero complex number. It need not be positive or real. The gain exponents $g_l$ use `D.divisibilityError`, which is also built from chosen objects, so $c_B$ depends on choices too. Theorem B uses only $c_B \neq 0$ and $c_{ss} \neq 0$.

**Definition (The scaled inclusion).** $\iota = c_{ss}^{-1}\cdot(\mathrm{src} \hookrightarrow X)$.

Lean: `New.Data.scaledInclusion` (New/Reduction/ShortAndEnough.lean).

**Definition (The projected Poincaré map).** For $s \in \bar G$, the map $\mathrm{src} \to \mathrm{target}$ is $\mathfrak{g}_s \circ \iota$.

Lean: `New.Data.projectedPoincare` (New/Reduction/ShortAndEnough.lean).

**Definition (The normalized Poincaré map).** For $s \in \bar G$, $s\mathfrak{p} = c_B\,\mathfrak{g}_s\circ\iota$.

Lean: `New.Data.normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

The name $s\mathfrak{p}$ is justified by `coe_normalizedPoincare`: as a form on $Y_0$, $s\mathfrak{p}(\varphi)$ is $\rho(s)$ applied to $1\mathfrak{p}(\varphi)$, because $e_0$ is central.

**Lemma (The range of a normalized map).** For each $s \in \bar G$,

$$\operatorname{range}(s\mathfrak{p}) = \mathfrak{g}_s(\mathrm{src}).$$

Lean: `New.Data.range_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* The range of $c\,A$ is the range of $A$ for $c \neq 0$ (`LinearMap.range_smul`). Here $c_B \neq 0$ by the positivity lemma, and $c_{ss}^{-1} \neq 0$ since it is a unit. The range of a composite $\mathfrak{g}_s \circ j$ with $j$ the inclusion is the image of $\mathrm{src}$ under $\mathfrak{g}_s$ (`LinearMap.range_comp`). $\square$

### A logarithm

**Lemma (The factor of the cover).** With $\varepsilon = (8b^2)^{-1}$,

$$\frac52\Bigl(1 + \log\frac{1}{16\varepsilon}\Bigr) \leq 5\log(1 + 2b^2).$$

Lean: `New.Data.five_halves_mul_one_add_log_le` (New/Reduction/ShortAndEnough.lean).

*Proof.* The size bound $2 \leq b^2$ holds (`le_of_hasLogBound`). Then $1 + 2b^2 \geq 5 > e$, since $e < 3$ (`exp_one_lt_three`), so $\log(1 + 2b^2) \geq 1$. Next $(16\varepsilon)^{-1} = b^2/2 \leq 1 + 2b^2$, so $\log(16\varepsilon)^{-1} \leq \log(1 + 2b^2)$ (`log_le_log`). Hence

$$\frac52\bigl(1 + \log(16\varepsilon)^{-1}\bigr) \leq \frac52\log(1 + 2b^2) + \frac52\log(1 + 2b^2) = 5\log(1 + 2b^2).$$

This is the claim. $\square$

In Lean the term is `log (16 * (8 * D.b ^ 2)⁻¹)⁻¹`, the logarithm of the inverse. The real logarithm of Mathlib is defined on all reals with $\log 0 = 0$ and $\log x = \log|x|$. Here the argument is $b^2/2 > 0$, so the junk values do not occur.

### The positivity of the target

**Lemma (The target has positive dimension).** $0 < d_T$.

Lean: `New.Data.targetDim_pos` (New/Reduction/ShortAndEnough.lean).

*Proof.* [The lemma that the target is not zero](/decl/New.Data.finrank_targetForms_ne_zero/), read as positivity of a natural number. $\square$

### The count and the span

**Theorem (Few normalized translates span the target).** There is a finite set $t \subseteq \bar G$ with

$$\#t\cdot\dim\mathrm{src} \leq 5\,d_T\log(1 + 2b^2)\quad\text{and}\quad\Bigl(1 - \frac{4}{b^2}\Bigr)d_T \leq \dim\sum_{s \in t}s\mathfrak{p}(\mathrm{src}).$$

Lean: `New.Data.exists_le_finrank_iSup_range_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* Let $\varepsilon = (8b^2)^{-1}$ and $D_X = \dim X$.

Step 1: the greedy cover. The source forms are nontrivial, because $\kappa$ is a linear equivalence onto a nontrivial space (`D.sourceFormCoords.nontrivial`). Apply [Theorem](/decl/New.IsSpread.exists_few_le_finrank_iSup_range/) to the family $\mathfrak{g}_s : X \to \mathrm{target}$. Its hypotheses are:

1. the family spreads with error $\tfrac32\varepsilon$, which is [the theorem on one translate](/decl/New.Data.isSpread_goodPoincare/);
2. $0 < d_T$, which is the positivity lemma;
3. $0 < \varepsilon$, since $b > 0$ (`HasLogBound.pos`);
4. $\varepsilon < 1/16$, a size bound of $D$ (`lt_of_hasLogBound`), equivalent to $b^2 > 2$.

The theorem gives a finite set $t$ with

$$\#t\cdot D_X \leq \frac52\bigl(1 + \log(16\varepsilon)^{-1}\bigr)d_T\quad\text{and}\quad(1 - 16\varepsilon)\,d_T \leq \dim\sum_{s \in t}\mathfrak{g}_s(X).$$

Step 2: the count. By the lemma on the factor of the cover,

$$\#t\cdot D_X \leq 5\,d_T\log(1 + 2b^2).$$

Call this bound (F).

Since $\dim\mathrm{src} \leq D_X$ (`Submodule.finrank_le`), the first claim follows.

Step 3: the loss for one map. By the bound for the ramified forms ([Theorem](/decl/New.Data.le_finrank_ramifiedSourceForms/)),

$$D_X - \dim\mathrm{src} \leq \frac{f}{N - 1}D_X \leq b^{-8}D_X,$$

where the second step is [Theorem](/decl/New.Data.f_div_N_sub_one_le/).

Step 4: the loss for all maps. Multiply Step 3 by $\#t$ and use (F):

$$\#t\,(D_X - \dim\mathrm{src}) \leq b^{-8}\,\#t\,D_X \leq b^{-8}\cdot 5\,d_T\log(1 + 2b^2) \leq \frac{2}{b^2}\,d_T.$$

The last step is the size bound $b^{-8}\cdot 5\log(1 + 2b^2) \leq 2/b^2$ (`le_of_hasLogBound`).

Step 5: the span. By the range lemma, $\sum_{s \in t}s\mathfrak{p}(\mathrm{src}) = \sum_{s \in t}\mathfrak{g}_s(\mathrm{src})$. By [Lemma](/decl/New.finrank_biSup_range_le/) with $U = \mathrm{src}$,

$$\dim\sum_{s \in t}\mathfrak{g}_s(X) \leq \dim\sum_{s \in t}\mathfrak{g}_s(\mathrm{src}) + \#t\,(D_X - \dim\mathrm{src}).$$

So

$$\Bigl(1 - \frac{4}{b^2}\Bigr)d_T = (1 - 16\varepsilon)\,d_T - \frac{2}{b^2}d_T \leq \dim\sum_{s \in t}\mathfrak{g}_s(X) - \#t\,(D_X - \dim\mathrm{src}) \leq \dim\sum_{s \in t}s\mathfrak{p}(\mathrm{src}).$$

The equality is $16\varepsilon = 2/b^2$. The first inequality is Step 1 and Step 4. The second is the lemma. $\square$

**Theorem (Theorem B, enough forms).** $0 < d_T$, and there is a finite set $t \subseteq \bar G$ with $\#t\cdot\dim\mathrm{src} \leq 5\,d_T\log(1 + 2b^2)$ and $(1 - 4/b^2)\,d_T \leq \dim\sum_{s \in t}s\mathfrak{p}(\mathrm{src})$.

Lean: `New.Data.enough_forms` (New/Reduction/ShortAndEnough.lean).

*Proof.* The positivity lemma and the theorem on the count and the span. $\square$

**Remark (Formalization).** The set $t$ comes from an existence statement, and the greedy cover builds it by a choice at each step. Theorem B says only that some $t$ exists. Lean accepts this proof, if the reported checks of the source hold. This book does not claim more.

### The constants

The table lists every constant of the proof of Theorem B, from the input to the statement.

| Step | Constant | Value | Reason |
|---|---|---|---|
| bad types at one prime | share | $\leq f\varepsilon_p + b^{-9} \leq b^{-8}/2$ | size bound |
| $L$ is a near isometry | error | $b^{-4}$ | $\|L^*L - 1\|^2 \leq b^{-12}D_X$ |
| $(1 - e_0)L$ | $\|\cdot\|^2$ | $\leq 4b^{-4}D_X$ | two primes |
| $e_0L$ is a near isometry | error | $5b^{-4}$, then $\varepsilon$ | $5b^{-4} \leq \varepsilon$ |
| second moment | factor | $1 + 9b^{-4}$, then $1 + \varepsilon$ | $9b^{-4} \leq \varepsilon$ |
| dimension of the target | bound | $\#\bar G\,\deg\,\mathrm{mass}_r$ | equal multiplicities |
| one translate | spread error | $\tfrac32\varepsilon = 3/(16b^2)$ | spread theorem |
| greedy cover | count factor | $\tfrac52(1 + \log(16\varepsilon)^{-1}) \leq 5\log(1 + 2b^2)$ | $2 \leq b^2$ |
| greedy cover | loss | $16\varepsilon = 2/b^2$ | $\varepsilon < 1/16$ |
| ramified forms | loss for one map | $f/(N - 1) \leq b^{-8}$ | $f \leq b$, $b^9 + 1 \leq N$ |
| ramified forms | loss for all maps | $\leq 2/b^2$ | $5b^{-8}\log(1 + 2b^2) \leq 2b^{-2}$ |
| Theorem B | share | $1 - 4/b^2$ | $2/b^2 + 2/b^2$ |

Here $\varepsilon = (8b^2)^{-1}$ and $\varepsilon_p = (1 + q_2 + 2r)/p_i$. All size bounds are consequences of the class `HasLogBound` of the data.

### Comparison with the plan

[The plan](/chapter/theorem-b-plan/#theorem-b-and-its-input) gives the same deduction in a shorter form. Three of its sentences differ from the source.

1. The plan says that $\iota$ is scaled by a positive number and that the two scalars of $s\mathfrak{p}$ are positive. In the source $c_{ss}$ is a unit of $\mathbb{C}$, so only $c_B$ is known to be positive. The plan's conclusion still holds, because the range lemma needs only that both scalars are nonzero.
2. The plan says that the cover theorem is applied with $V = X$ in the coordinates of the source forms. In the source it is applied to $\mathfrak{g}_s$ on $X$ itself. The coordinates enter only inside the proof of the theorem on one translate, through the lemma on preimages.
3. The plan says that $b^2 \geq 2$ gives $0 < \varepsilon < 1/16$. From $b^2 \geq 2$ one gets only $\varepsilon \leq 1/16$. The source proves the strict inequality $\varepsilon < 1/16$ by a separate size bound (`lt_of_hasLogBound`).
