---
title: Theorem B and its input
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/SecondMoment/FewTranslates.lean
  - New/UpperBound/Size/ShortColumns.lean
decls:
  - New.Data.enough_forms
  - New.Data.goodPoincare
  - New.Data.normalizedPoincare
  - New.Data.isSpread_goodPoincare
  - New.Data.le_finrank_ramifiedSourceForms
  - New.Data.f_div_N_sub_one_le
  - New.finrank_biSup_range_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theorem B and its input

This volume explains Theorem B of the source, the statement that few translates of one space of Poincaré series span almost all of the target space. This chapter gives the statement, its analytic input, the four layers of the proof, the conventions that change the meaning of a statement, and a map of the volume. It proves only one thing in full: the deduction of Theorem B from its input. That deduction is short, and it fixes all the constants that the rest of the volume must reach.

Theorem B is one of the three theorems of the main inequality. [The plan](/chapter/theorem-and-plan/) shows where it sits, and [the chapter on Theorems A, B and C](/chapter/theorems-a-b-c/) shows how the three combine. Theorem C needs a family that spans almost all of the target, and the index bound of Theorem A (b) grows with the number of translates. Theorem B gives a family with both properties.

### The objects

The statement uses five objects of the admissible data $D$. Their sizes are fixed in [the data and its sizes](/chapter/data-and-sizes/).

1. The number $b = D.b = e^{\log b}$ is the weight at the $b$-places. All sizes in this volume are powers of $b$. The data give $b \geq 1000$ and much more.
2. The target is the space of good forms on the hermitian space $Y_0$, and $d_T$ is its dimension.
3. The source $\mathrm{src}$ is the space of ramified source forms. It is a subspace of the space $X$ of all source forms. A source form is ramified if, at each place $w$ above the split prime $N$, the sum of its translates by the powers $z_w^i$, $0 \leq i < N - 1$, of a chosen scaling $z_w$ is $0$.
4. The group $\bar G$ is the finite group $\prod_w \mathrm{GL}_r(\mathbb{F}_w)$, the product over the chosen places $w$ above the two level primes $p_0$ and $p_1$. It acts on the forms of principal level on $Y_0$.
5. The map $s\mathfrak{p}$, for $s \in \bar G$, is the normalized Poincaré map translated by $s$. It sends a ramified source form to a target form.

The map $\mathfrak{p}$ is built in steps. Let $\mathcal{P}$ be the Poincaré map from all source forms to the forms of principal level on $Y_0$. Its construction is the subject of [the chapter on Poincaré series](/chapter/poincare-series/). Let $e_0$ be the central projection onto the good forms.

**Definition (Good Poincare maps).** For $s \in \bar G$, the map $\mathfrak{g}_s : X \to \mathrm{target}$ is $\mathfrak{g}_s = \#\bar G \cdot e_0\, s\, \mathcal{P}$, the Poincaré map, then the translation by $s$, then the projection onto the good forms, times the order of $\bar G$.

Lean: `New.Data.goodPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

**Definition (Normalized Poincare maps).** For $s \in \bar G$, the map $s\mathfrak{p} : \mathrm{src} \to \mathrm{target}$ is $c\,\mathfrak{g}_s \circ \iota$. Here $\iota$ is the inclusion of the ramified source forms into all source forms, scaled by a positive number, and $c$ is a positive number, the inverse of a gain factor.

Lean: `New.Data.normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

The two scalars come from Theorem A. There the factor $c_B c_{ss}^{-1}$ makes the forms integral with a controlled index. For Theorem B they do not matter, because a nonzero scalar does not change a range.

### The statement

**Theorem (Theorem B, enough forms).** The target has positive dimension, $0 < d_T$. There is a finite set $t \subseteq \bar G$ with

$$\#t \cdot \dim \mathrm{src} \leq 5\, d_T \log(1 + 2b^2)$$

and

$$\Bigl(1 - \frac{4}{b^2}\Bigr) d_T \leq \dim \sum_{s \in t} s\mathfrak{p}(\mathrm{src}).$$

Lean: `New.Data.enough_forms`, `New.Data.exists_le_finrank_iSup_range_normalizedPoincare`, `New.Data.targetDim_pos` (New/Reduction/ShortAndEnough.lean).

The two inequalities have two uses. The first bounds the number of translates against the ratio $d_T/\dim\mathrm{src}$, up to the factor $5\log(1 + 2b^2)$. The second inequality is the hypothesis $n \geq (1 - 4/b^2) d_T$ of Theorem C. The positivity $d_T > 0$ lets the main inequality divide by $d_T$.

### The input: one translate spreads

The proof of Theorem B rests on one statement about the maps $\mathfrak{g}_s$ on all source forms. It is a statement of average position. The images $\mathfrak{g}_s(X)$ are not in general position, but for every subspace $F$ of the target some translate meets $F$ in about the dimension that a random subspace would.

Recall from [the chapter on Theorems A, B and C](/chapter/theorems-a-b-c/) the notion of spread. Maps $B_s : V \to W$ of finite-dimensional complex spaces *spread with the error* $\eta$ if for every subspace $F$ of $W$, with $\alpha = \dim F/\dim W$, there is an index $s$ with $\dim B_s^{-1}(F) \leq ((1 + \alpha)/2 + \eta)\dim V$. A subspace in general position meets $F$ in at most the share $\alpha$ of its dimension. So spread is a weak form of general position.

**Theorem (One translate).** The maps $\mathfrak{g}_s$, $s \in \bar G$, spread with the error $\frac{3}{2}(8b^2)^{-1}$. That is, for every subspace $F$ of the target with $\alpha = \dim F/d_T$, there is $s \in \bar G$ with

$$\dim \mathfrak{g}_s^{-1}(F) \leq \Bigl(\frac{1 + \alpha}{2} + \frac{3}{16 b^2}\Bigr)\dim X.$$

Lean: `New.Data.isSpread_goodPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

This theorem is the subject of the whole volume. [The proof of Theorem B](/chapter/proof-of-theorem-b/) assembles it. Its proof has the four layers of [the section on the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof), and each of the other chapters proves one part.

**Remark (Formalization).** The error in Lean is written $\frac{3}{2} \cdot (8b^2)^{-1}$, and this is the form that the cover lemma below reads: it asks for the error $\frac{3}{2}\varepsilon$ with $\varepsilon = (8b^2)^{-1}$. So $16\varepsilon = 2/b^2$. The number $3/(16b^2)$ is the error itself, not $\varepsilon$. A reader who sets $\varepsilon = 3/(16b^2)$ finds the wrong loss $3/b^2$. The theorem is stated for the maps on all source forms $X$, not on $\mathrm{src}$. The passage to $\mathrm{src}$ is part of the proof of Theorem B below.

### From one translate to Theorem B

The deduction uses the greedy cover of [the chapter on Theorems A, B and C](/chapter/theorems-a-b-c/), and three facts about sizes.

**Theorem (Few maps span almost everything).** Let $V$ and $W$ be finite-dimensional, with $V \neq 0$ and $\dim W > 0$. Let $0 < \varepsilon < 1/16$, and let maps $B_s : V \to W$ spread with the error $\frac{3}{2}\varepsilon$. Then there is a finite set $t$ of indices with $\#t \cdot \dim V \leq \frac{5}{2}(1 + \log(1/(16\varepsilon)))\dim W$ and $(1 - 16\varepsilon)\dim W \leq \dim\sum_{s \in t} B_s(V)$.

Lean: `New.IsSpread.exists_few_le_finrank_iSup_range` (New/Spanning/SecondMoment/FewTranslates.lean).

**Lemma (Restriction to a subspace).** Let $B_s : V \to W$ be linear maps, $t$ a finite set of indices and $U$ a subspace of $V$. Then

$$\dim \sum_{s \in t} B_s(V) \leq \dim \sum_{s \in t} B_s(U) + \#t\,(\dim V - \dim U).$$

Lean: `New.finrank_biSup_range_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Choose a complement $C$ of $U$ in $V$. Then $\sum_s B_s(V) = \sum_s B_s(U) + \sum_s B_s(C)$, and the second sum has dimension at most $\#t \dim C = \#t(\dim V - \dim U)$. $\square$

**Lemma (Ramified forms are most forms).** The ramified source forms satisfy $(1 - f/(N - 1))\dim X \leq \dim \mathrm{src}$, where $f$ is the number of infinite places of the CM field $E$.

Lean: `New.Data.le_finrank_ramifiedSourceForms` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The space $\mathrm{src}$ is the range of the product of the operators $1 - z_w$ over the $f$ places $w$ above $N$. The kernel of each factor is the space fixed by $z_w$, and it has dimension at most $\dim X/(N - 1)$. The kernel of a product of $f$ operators has dimension at most the sum of the dimensions of their kernels. So the codimension of $\mathrm{src}$ is at most $f\dim X/(N - 1)$. $\square$

**Lemma (The share is small).** $f/(N - 1) \leq b^{-8}$.

Lean: `New.Data.f_div_N_sub_one_le` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The data give $f \leq b$ and $b^9 + 1 \leq N$. So $f/(N - 1) \leq b/b^9$. $\square$

*Proof of Theorem B.* First, $d_T > 0$ by [Theorem](/decl/New.Data.finrank_targetForms_ne_zero/): the composite $e_0\mathcal{P}$ is almost an isometry, so its range is not zero. Put $\varepsilon = (8b^2)^{-1}$. Since $b^2 \geq 2$, we have $0 < \varepsilon < 1/16$. The space $X$ is not zero, because it has coordinates indexed by a nonempty set.

Apply the cover theorem to the maps $\mathfrak{g}_s$ on $X$, with the spread of [Theorem](/decl/New.Data.isSpread_goodPoincare/). It gives a finite set $t \subseteq \bar G$ with

$$\#t \dim X \leq \tfrac{5}{2}(1 + \log(b^2/2))\, d_T \quad\text{and}\quad (1 - 2/b^2)\, d_T \leq \dim \sum_{s \in t}\mathfrak{g}_s(X).$$

Here $1/(16\varepsilon) = b^2/2 \leq 1 + 2b^2$, and $1 + 2b^2 \geq e$, so $\frac{5}{2}(1 + \log(b^2/2)) \leq \frac{5}{2}(2\log(1 + 2b^2)) = 5\log(1 + 2b^2)$. Since $\dim\mathrm{src} \leq \dim X$, this gives the first inequality of Theorem B.

For the second inequality, restrict to $\mathrm{src}$. By the two lemmas on ramified forms, $\dim X - \dim\mathrm{src} \leq b^{-8}\dim X$. By the restriction lemma, the span loses at most

$$\#t\,(\dim X - \dim\mathrm{src}) \leq b^{-8}\,\#t\dim X \leq b^{-8} \cdot 5\log(1 + 2b^2)\, d_T \leq \frac{2}{b^2}\, d_T.$$

The last step is a size inequality of the data: $5 b^{-8}\log(1 + 2b^2) \leq 2b^{-2}$, which holds with room since $b \geq 1000$. So $\dim\sum_{s \in t}\mathfrak{g}_s(\mathrm{src}) \geq (1 - 2/b^2 - 2/b^2)\, d_T = (1 - 4/b^2)\, d_T$. Finally, the range of $s\mathfrak{p}$ is $\mathfrak{g}_s(\mathrm{src})$, since the two scalars in $s\mathfrak{p}$ are positive. $\square$

The share $4/b^2$ has two halves. One is the share $16\varepsilon = 2/b^2$ that the greedy cover leaves. The other pays for the passage to the ramified forms, where the true loss is only $5b^{-8}\log(1 + 2b^2)\, d_T$.

**Remark (Formalization).** The cover theorem is applied with $V = X$ in the coordinates of the source forms, which are indexed by pairs of a class and a Bessel coordinate. The spread statement is proved in those coordinates and then moved to the forms; a linear equivalence does not change the dimension of a preimage. The ramified forms enter only in this last proof, through the codimension. The spread theorem itself never sees them. The positivity $d_T > 0$ is a consequence of the near isometry, not a separate hypothesis.
