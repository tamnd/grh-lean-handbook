---
title: The greedy cover
lean:
  - New/Spanning/SecondMoment/FewTranslates.lean
decls:
  - New.finrank_sup_range_add_finrank_comap
  - New.IsSpread.exists_codim_le
  - New.IsSpread.exists_codim_le_max
  - New.IsSpread.exists_few_le_finrank_iSup_range
  - New.finrank_biSup_map_le
  - New.finrank_biSup_range_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The greedy cover

This section proves that a spread family has few maps whose images span almost all of the target. The result is [Theorem](/decl/New.IsSpread.exists_few_le_finrank_iSup_range/), which [Theorem B and its input](/chapter/theorem-b-plan/#theorem-b-and-its-input) applies to the good Poincaré maps with $\varepsilon = (8b^2)^{-1}$. The proof is the greedy method of set cover, with spread in place of a count of elements. In this section $V$ and $W$ are finite-dimensional complex vector spaces, $\Theta$ is an index set, and $B_s : V \to W$ are linear maps. No inner product is needed.

### The idea

Let $F$ be the span of the images chosen so far, and let $c = \dim W - \dim F$ be the codimension, the number of dimensions that are still missing. Adding the image of $B_s$ to $F$ adds $\dim V - \dim B_s^{-1}(F)$ dimensions. Spread gives an $s$ for which $\dim B_s^{-1}(F)$ is at most $\frac{1 + \alpha}{2}\dim V$ plus a small error, so the step adds at least about $\frac{1 - \alpha}{2}\dim V$ dimensions. Here $1 - \alpha = c/\dim W$ is the missing share. So the step removes a share of about $\dim V/(2\dim W)$ of what is missing, whatever $F$ is. A fixed share removed at each step gives exponential decay, and the number of steps to reach a share $\delta$ is about $\log(1/\delta)$ divided by that share.

This is the reason for the form $(1 + \alpha)/2$ in the definition of spread. The gain of a step must be proportional to the missing share $1 - \alpha$, with a constant that does not depend on $F$. The error $\eta$ spoils this when $1 - \alpha$ is of the size of $\eta$. So the greedy method stops at a missing share of a constant times $\eta$.

### The dimension of one step

**Lemma (One step adds a codimension).** Let $A : V \to W$ be linear and let $F$ be a subspace of $W$. Then

$$\dim(F + A(V)) + \dim A^{-1}(F) = \dim F + \dim V.$$

Lean: `New.finrank_sup_range_add_finrank_comap` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $R = A(V)$. The restriction of $A$ to $A^{-1}(F)$ has the image $F \cap R$ and the kernel $\ker A$, so $\dim A^{-1}(F) = \dim(F \cap R) + \dim\ker A$. The dimension formula gives $\dim(F + R) + \dim(F \cap R) = \dim F + \dim R$, and $\dim R + \dim\ker A = \dim V$. Add the three equations. $\square$

**Lemma (One greedy step).** Let $\dim W > 0$, let the maps $B_s$ spread with the error $\frac{3}{2}\varepsilon$, and let $F$ be a subspace of $W$ with

$$16\varepsilon\dim W < \dim W - \dim F.$$

Then there is $s \in \Theta$ with

$$\dim W - \dim(F + B_s(V)) \leq \Bigl(1 - \frac{2\dim V}{5\dim W}\Bigr)(\dim W - \dim F).$$

Lean: `New.IsSpread.exists_codim_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Let $\alpha = \dim F/\dim W \leq 1$. The hypothesis says $16\varepsilon < 1 - \alpha$. Spread gives $s$ with $\dim B_s^{-1}(F) \leq (\frac{1 + \alpha}{2} + \frac{3}{2}\varepsilon)\dim V$. Since $\frac{3}{2}\varepsilon < \frac{3}{32}(1 - \alpha) \leq \frac{1}{10}(1 - \alpha)$,

$$\frac{1 + \alpha}{2} + \frac{3}{2}\varepsilon \leq 1 - \frac{1 - \alpha}{2} + \frac{1 - \alpha}{10} = 1 - \frac{2}{5}(1 - \alpha).$$

By the lemma on one step, $\dim(F + B_s(V)) = \dim F + \dim V - \dim B_s^{-1}(F) \geq \dim F + \frac{2}{5}(1 - \alpha)\dim V$. Now $(1 - \alpha)\dim W = \dim W - \dim F$, so $\frac{2}{5}(1 - \alpha)\dim V = \frac{2\dim V}{5\dim W}(\dim W - \dim F)$. Subtract from $\dim W$. $\square$

The constant $\frac{2}{5}$ has a little room. The exact gain in the proof is $\frac{1}{2} - \frac{3}{32} = \frac{13}{32}$, and $\frac{2}{5} = \frac{12.8}{32}$. The lemma has no sign condition on $\varepsilon$. For $\varepsilon < 0$ the step is only better.

Write $\mathrm{rate} = \frac{2\dim V}{5\dim W}$. The lemma says that one step multiplies the codimension by at most $1 - \mathrm{rate}$, as long as the codimension exceeds $16\varepsilon\dim W$.

### Many steps

**Lemma (The greedy choice after $l$ steps).** Let $\dim W > 0$, let the maps $B_s$ spread with the error $\frac{3}{2}\varepsilon$, and let $l \geq 0$ be an integer. Then there is a finite set $t \subseteq \Theta$ with $\#t \leq l$ and

$$\dim W - \dim\sum_{s \in t}B_s(V) \leq \max\bigl(16\varepsilon,\ e^{-l\cdot\mathrm{rate}}\bigr)\dim W.$$

Lean: `New.IsSpread.exists_codim_le_max` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Induction on $l$. For $l = 0$ take $t = \emptyset$. The codimension is $\dim W$, and $e^0 = 1$.

Let $t$ be a set for $l$, and let $c$ be the codimension of $F = \sum_{s \in t}B_s(V)$. If $c \leq 16\varepsilon\dim W$, then $t$ also serves for $l + 1$. Otherwise the bound for $l$ gives $c \leq e^{-l\cdot\mathrm{rate}}\dim W$. The lemma on one greedy step gives $s$, and $t \cup \{s\}$ has at most $l + 1$ elements and the codimension at most

$$(1 - \mathrm{rate})\,c \leq e^{-\mathrm{rate}}\cdot e^{-l\cdot\mathrm{rate}}\dim W = e^{-(l + 1)\mathrm{rate}}\dim W,$$

by $1 - x \leq e^{-x}$. The factor $1 - \mathrm{rate}$ is applied to $c \geq 0$, so the inequality needs no sign of $1 - \mathrm{rate}$. $\square$

### The cover theorem

**Theorem (Few maps span almost everything).** Let $V$ and $W$ be finite-dimensional, with $V \neq 0$ and $\dim W > 0$. Let $0 < \varepsilon < \frac{1}{16}$, and let the maps $B_s : V \to W$, $s \in \Theta$, spread with the error $\frac{3}{2}\varepsilon$. Then there is a finite set $t \subseteq \Theta$ with

$$\#t\cdot\dim V \leq \frac{5}{2}\Bigl(1 + \log\frac{1}{16\varepsilon}\Bigr)\dim W \qquad\text{and}\qquad (1 - 16\varepsilon)\dim W \leq \dim\sum_{s \in t}B_s(V).$$

Lean: `New.IsSpread.exists_few_le_finrank_iSup_range` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* *Step 1: $\mathrm{rate} \leq 1$.* Apply the lemma on one greedy step to $F = 0$. Its hypothesis $16\varepsilon\dim W < \dim W$ holds since $16\varepsilon < 1$. It gives $s$ with $0 \leq \dim W - \dim B_s(V) \leq (1 - \mathrm{rate})\dim W$. As $\dim W > 0$, $\mathrm{rate} \leq 1$. Also $\mathrm{rate} > 0$, since $V \neq 0$.

*Step 2: the number of steps.* Put $L = \log(1/(16\varepsilon)) \geq 0$ and $l = \lceil L/\mathrm{rate}\rceil$. Then $l\cdot\mathrm{rate} \geq L$, and

$$l\cdot\mathrm{rate} < \Bigl(\frac{L}{\mathrm{rate}} + 1\Bigr)\mathrm{rate} = L + \mathrm{rate} \leq 1 + L.$$

*Step 3: the cover.* The lemma on $l$ steps gives $t$ with $\#t \leq l$ and the codimension at most $\max(16\varepsilon, e^{-l\cdot\mathrm{rate}})\dim W$. Since $l\cdot\mathrm{rate} \geq L$, $e^{-l\cdot\mathrm{rate}} \leq 16\varepsilon$. So the codimension is at most $16\varepsilon\dim W$, which is the second claim. For the first,

$$\#t\cdot\dim V \leq l\dim V = \frac{5}{2}\,l\cdot\mathrm{rate}\cdot\dim W \leq \frac{5}{2}(1 + L)\dim W. \qquad\square$$

Step 1 is a small point with a reason. A spread family cannot have $\dim V$ much larger than $\dim W$, because spread at $F = 0$ bounds the kernel of some $B_s$ by about half of $V$. Without $\mathrm{rate} \leq 1$ the rounding up of $L/\mathrm{rate}$ could cost a full step of size $\dim V$, which is not bounded by $\dim W$.

**Remark (Formalization).** The set $t$ is given by an existence statement. The proof chooses each step by the existence of $s$ in the definition of spread, so the set is not computed. Lean states $\#t\cdot\dim V \leq \ldots$ with $\#t$ the number of elements of a finite set, so the same index is never counted twice. The logarithm is the real logarithm of $(16\varepsilon)^{-1}$, a number $> 1$ under the hypotheses, so no convention for $\log 0$ enters.

### The size of the cover in the source

With $\varepsilon = (8b^2)^{-1}$, $16\varepsilon = 2/b^2$ and $1/(16\varepsilon) = b^2/2$. So the cover has

$$\#t \leq \frac{5}{2}\Bigl(1 + \log\frac{b^2}{2}\Bigr)\frac{d_T}{\dim X}$$

translates, where $X$ is the space of all source forms, and its images span at least $(1 - 2/b^2)d_T$ dimensions. For $b = 1000$, $\log(b^2/2) \approx 13.1$ and the factor is about $35.3$. The trivial lower bound is $d_T/\dim X$. So the greedy cover is within a factor $O(\log b)$ of the best possible count. [Theorem B and its input](/chapter/theorem-b-plan/#theorem-b-and-its-input) bounds $\frac{5}{2}(1 + \log(b^2/2))$ by $5\log(1 + 2b^2)$.

### Restriction to a subspace

Theorem B needs the span of the images of the ramified source forms $\mathrm{src} \subseteq X$, not of all of $X$. Two lemmas pass from one to the other.

**Lemma (Images of a subspace).** Let $t$ be a finite set of indices and $C$ a subspace of $V$. Then $\dim\sum_{s \in t}B_s(C) \leq \#t\dim C$.

Lean: `New.finrank_biSup_map_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Induction on $t$: $\dim(G + H) \leq \dim G + \dim H$, and $\dim B_s(C) \leq \dim C$. $\square$

**Lemma (Restriction to a subspace).** Let $t$ be a finite set of indices and $U$ a subspace of $V$. Then

$$\dim\sum_{s \in t}B_s(V) \leq \dim\sum_{s \in t}B_s(U) + \#t\,(\dim V - \dim U).$$

Lean: `New.finrank_biSup_range_le` (New/Spanning/SecondMoment/FewTranslates.lean).

*Proof.* Choose a complement $C$ of $U$ in $V$, so $\dim C = \dim V - \dim U$. Since $V = U + C$, $\sum_s B_s(V) = \sum_s B_s(U) + \sum_s B_s(C)$. Bound the dimension of the second sum by the lemma on images. $\square$

In the source $\dim X - \dim\mathrm{src} \leq b^{-8}\dim X$, so the loss is at most $b^{-8}\#t\dim X$, a share far smaller than $2/b^2$ of $d_T$. The proof of Theorem B in [the opening chapter](/chapter/theorem-b-plan/#theorem-b-and-its-input) makes this exact.

### A model case of the cover

In the model case of [the opening section](/chapter/few-translates/#what-the-chapter-proves), with $d \mid n$, the shifts spread with the error $0$, hence with every error $\frac{3}{2}\varepsilon > 0$. The theorem gives at most $\frac{5}{2}(1 + \log(1/(16\varepsilon)))\,n/d$ shifts that span $(1 - 16\varepsilon)n$ dimensions. The true answer is $n/d$ shifts for all of $\mathbb{C}^n$. The loss is the logarithm, and it comes from the worst case of spread: the method does not know that the shifts are in a special position, only that no subspace captures too much of every shift.

The logarithm cannot be removed by the method. Spread controls each step only through the share $1 - \alpha$ that is missing, and the gain $\frac{2}{5}(1 - \alpha)\dim V$ shrinks with it. In the last steps, when the missing share is near $16\varepsilon$, each translate adds only about $6\varepsilon\dim V$ new dimensions. Exercise 4 asks for the number of steps that the proof gives in the model case, and compares it with $n/d$.
