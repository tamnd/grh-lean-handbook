---
title: Sizes, lengths and balanced frames
lean:
  - New/Spanning/Frames/Lengths.lean
  - New/Spanning/Frames/TwoGauges.lean
decls:
  - New.Floors.Size
  - New.Floors.Size.form_mem_ofSize
  - New.Floors.Size.det_mem_ofSize
  - New.Floors.Size.HasMatrixSize.inv
  - New.Floors.coe_weylRatio
  - New.Floors.Size.LengthLeAt
  - New.Floors.Size.IsBalanced
  - New.Floors.Size.GaugesDifferLe
  - New.Floors.Size.HasShortDual
  - New.Floors.Size.IsHead
  - New.Floors.Size.GaugesDifferLe.of_succ
  - New.Floors.Size.GaugesDifferLe.on_whole_space_of_hasShortDual
  - New.Floors.Size.head_prod_mul_dual_mem_ofSize
  - New.Floors.Size.hasMatrixSize_of_isHead
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Sizes, lengths and balanced frames

Every bound of the chapter has the form "this quantity has size $c$" or "this integral is at most $\Lambda^{c}$". This section sets up the first kind. A *size* is a filtration of the ring by sets $A_{(0)} \subseteq A_{(1)} \subseteq \cdots$, and a vector or a matrix has size $i$ if all its entries have size $i$. The rules are few, and the source applies them by hand. The constants of the later sections, such as $9n$, $60n^2$ and $99n^2$, come from the counts of this section.

### The rules of sizes

**Definition (Size).** A *size* for the form $T$ is a family of sets $A_{(i)} \subseteq A$, $i \in \mathbb{N}$, with these rules.

1. $A_{(i)}A_{(j)} \subseteq A_{(i + j)}$.
2. A sum of at most $r + 1$ terms of size $i$ has size $i + 1$, where $r$ is the rank of the space.
3. $-x$ has size $i$ exactly when $x$ has, and so does $\bar x$.
4. $0$ and $1$ have every size.
5. The entries of the Gram matrix $J$ and of $J^{-1}$ have size $1$.

Lean: `New.Floors.Size` (New/Spanning/Frames/Lengths.lean).

The source has two cases in view. At a real place, $x$ has size $i$ if $|x| \leq L^i$ for a fixed number $L$. At the finite places, $x$ has size $i$ if $\alpha^i x$ is integral for a fixed integral unit $\alpha$. The structure does not ask that the sets increase. The lemma `New.Floors.Size.mem_ofSize_mono` derives this from rules 1 and 4, since $x = x\cdot 1$ with $1$ of size $j - i$.

**Example.** Take $A = \mathbb{R}$ and $A_{(i)} = \{x : |x| \leq L^i\}$. Rule 1 holds for every $L > 0$, and rule 4 asks that $L \geq 1$. Rule 2 asks that $(r + 1)L^i \leq L^{i + 1}$, that is, $L \geq r + 1$. Rule 5 holds once $L$ bounds the moduli of the entries of $J$ and of $J^{-1}$. So a scale $L \geq r + 1$ that also bounds these entries gives a size. The rank $r$ enters only through rule 2, and this is why the constants below grow with $n$: each sum over the basis costs one step.

**Lemma (Products and the form).** If $v$ has size $i$ and $w$ has size $j$, then $h(v, w) = \bar v^{\mathsf T}Jw$ has size $i + j + 3$.

Lean: `New.Floors.Size.form_mem_ofSize` (New/Spanning/Frames/Lengths.lean).

*Proof.* An entry of $Jw$ is a sum over the basis of products of an entry of size $1$ and an entry of size $j$, so it has size $j + 2$. Then $\bar v^{\mathsf T}(Jw)$ is a sum over the basis of products of size $i + j + 2$, so it has size $i + j + 3$. $\square$

**Lemma (Determinants).** Let $Z$ be a square matrix of order $j \leq \varrho$ whose entries have size $7$. Then $\det Z$ has size $8j$.

Lean: `New.Floors.Size.det_mem_ofSize` (New/Spanning/Frames/Lengths.lean).

*Proof.* By induction on $j$. For $j = 0$ the determinant is $1$. For $j + 1$, expand along a row: $\det Z$ is a sum of $j + 1 \leq r + 1$ terms, each a sign times an entry of size $7$ times a minor of size $8j$. Each term has size $8j + 7$, and the sum has size $8j + 8$. $\square$

**Lemma (Inverses).** If the matrix of an isometry $x$ has size $i$, then the matrix of $x^{-1}$ has size $i + 4$.

Lean: `New.Floors.Size.HasMatrixSize.inv` (New/Spanning/Frames/Lengths.lean).

*Proof.* Since $x$ preserves $h$, $x^{-1} = J^{-1}x^{\mathsf H}J$. The entries of $x^{\mathsf H}J$ have size $i + 2$, and those of $J^{-1}(x^{\mathsf H}J)$ have size $1 + (i + 2) + 1 = i + 4$. $\square$

### Weyl elements

For a sequence of units $p = (p_0, p_1, \dots)$ and $j \leq \varrho$, the Weyl element $w_p$ (`weylElem j p`) sends $e_a$ to $p_ae^*_a$ and $e^*_a$ to $\bar p_a^{-1}e_a$ for $a < j$, and fixes the other basis vectors. The quotient of two of them is diagonal.

**Lemma (Weyl ratio).** Let $j \in \mathbb{N}$ and let $p, q$ be sequences of units. The matrix of $w_q^{-1}w_p$ (`weylRatio j p q`) is diagonal. For $a < \min(j, \varrho)$, its entry at $e_a$ is $p_a/q_a$ and its entry at $e^*_a$ is $\overline{q_a/p_a}$. Every other diagonal entry is $1$.

Lean: `New.Floors.coe_weylRatio` (New/Spanning/Frames/Lengths.lean).

*Proof.* Both elements act on the plane of $e_a, e^*_a$ for $a < j$ and fix the rest. On that plane, $w_q^{-1}w_p e_a = w_q^{-1}(p_ae^*_a) = p_aq_a^{-1}e_a$, and the entry at $e^*_a$ follows in the same way. $\square$

### Lengths at a point

A point $g \in \mathsf{G}$ gives a notion of length: $y$ has length at most $L^i$ at $g$ if $g^{-1}y$ has size $i$ (`LengthLeAt g i y`). At a real place this is a bound on the sup norm of $g^{-1}y$. On the quotient $Y^{(l)}$, the induced length of a class is the least length of a lift (`InducedLengthLe`). Lean writes $y \perp e_b$ for $b < l$ as `IsOrthogonalBelow l y`, which says that the coordinates of $y$ at $e^*_b$ are $0$, and two lifts of one class as `CongrBelow l y y'`.

Lean: `New.Floors.Size.LengthLeAt` (New/Spanning/Frames/Lengths.lean).

**Definition (Balanced).** Let $g \in \mathsf{G}$, $a < \varrho$ and $i \in \mathbb{N}$. The vector $e_a$ is *balanced* in $Y^{(a)}$ at $g$ with bound $L^i$ if

1. some lift of the class of $e_a$ in $Y^{(a)}$ has length at most $L^i$ at $g$, and
2. some $\zeta$ with $\zeta \perp e_b$ for $b < a$ and $\zeta(e^*_a) = 1$, a *dual* of $e_a$, has length at most $L^i$ at $g$.

Lean: `New.Floors.Size.IsBalanced` (New/Spanning/Frames/Lengths.lean).

The dual stands for a lower bound on the length at a real place, and for primitivity at the finite places. The source compares two points $g, g'$ by three relations, all modulo a unit $r$. Let $r$ be a unit.

**Definition (Gauges that differ little).** Let $g, g' \in \mathsf{G}$, $l, t \in \mathbb{N}$. The lengths at $g$ and $g'$ on $Y^{(l)}$ *differ by at most $L^t$ modulo $r$* if, for each $i$ and each $\omega \perp e_b$ ($b < l$) of length at most $L^i$ at $g$, some $\omega'$ congruent to $\omega$ modulo the $e_b$ ($b < l$) has $r^{-1}(g^{-1}\omega - g'^{-1}\omega')$ of size $i + t$.

Lean: `New.Floors.Size.GaugesDifferLe` (New/Spanning/Frames/Lengths.lean).

**Definition (Short dual).** The vector $e_a$ has a *short dual* of size $i$ for $g, g'$ modulo $r$ if some dual $\zeta$ of $e_a$ has length at most $L^i$ at $g$ and some lift $\zeta'$ of its class has $r^{-1}(g^{-1}\zeta - g'^{-1}\zeta')$ of size $i$.

Lean: `New.Floors.Size.HasShortDual` (New/Spanning/Frames/Lengths.lean).

**Definition (Head).** A sequence of units $p$ is a *head of length $j$* if $(p_0\cdots p_{l-1})^{-1}$ has size $1$ for every $l \leq j$.

Lean: `New.Floors.Size.IsHead` (New/Spanning/Frames/Lengths.lean).

### From one quotient to the next

**Lemma (One step down).** Let $g, g' \in \mathsf{G}$, let $r$ be a unit with $\bar r = r$ of size $1$, let $a < \varrho$ and $c, t \in \mathbb{N}$. Suppose that the class of $e_a$ in $Y^{(a)}$ has induced length at most $L^c$ at $g$ and at $g'$, that $e_a$ has a short dual of size $c$ for $g, g'$ modulo $r$, and that the lengths at $g$ and $g'$ on $Y^{(a+1)}$ differ by at most $L^t$ modulo $r$. Then they differ by at most $L^{t + 4c + 12}$ modulo $r$ on $Y^{(a)}$.

Lean: `New.Floors.Size.GaugesDifferLe.of_succ` (New/Spanning/Frames/TwoGauges.lean).

*Proof.* Let $\omega \perp e_b$ ($b < a$) have length at most $L^i$ at $g$, and let $\zeta$ be the short dual. The number $\gamma = h(e_a, \omega)$ equals $h(f, \omega)$ for the short lift $f$ of $e_a$, since $\omega \perp e_b$ for $b < a$. As $g$ is an isometry, $\gamma = h(g^{-1}f, g^{-1}\omega)$ has size $c + i + 3$ by the lemma on the form. The vector $\omega - \gamma\zeta$ is orthogonal to $e_b$ for $b \leq a$, so the hypothesis on $Y^{(a+1)}$ applies to it, and $\gamma\zeta$ is handled by the short dual. The lemma on the form modulo $r$ (`New.Floors.Size.form_sub_form_mem_ofSize`, with the loss $6$) compares $\gamma$ with the same product at $g'$. The source adds the losses of these steps and gets $4c + 12$. $\square$

**Lemma (All quotients).** Let $j \leq \varrho$ and let $r$ be as before. Suppose that for each $a < j$ the class of $e_a$ in $Y^{(a)}$ has induced length at most $L^c$ at $g$ and at $g'$ and has a short dual of size $c$ for $g, g'$ modulo $r$. If the lengths differ by at most $L^t$ modulo $r$ on $Y^{(j)}$, then they differ by at most $L^{t + (4c + 12)j}$ modulo $r$ on $Y^{(0)} = V$.

Lean: `New.Floors.Size.GaugesDifferLe.on_whole_space_of_hasShortDual` (New/Spanning/Frames/TwoGauges.lean).

*Proof.* Apply the lemma on one step $j$ times, for $a = j - 1, \dots, 0$. $\square$

### Heads keep the first vectors short

**Lemma (Cramer's rule for a head).** Let $K \subseteq \mathsf{G}$ be a set whose elements have matrices of size $1$. Let $j \leq \varrho$, $a < j$, $p$ a sequence of units and $g \in \mathsf{G}$. Suppose that $\eta w_p^{-1}g \in K$ for some $\eta \in R^{(j)}$, and let $s \in R^{(j)}$ with $sg \in K$. Then for every index $i$ the number $p_0\cdots p_a\cdot(s)_{i, e^*_a}$ has size $8\varrho$.

Lean: `New.Floors.Size.head_prod_mul_dual_mem_ofSize` (New/Spanning/Frames/TwoGauges.lean).

*Proof.* The two conditions say that $g$ and $w_p^{-1}g$ are both moved into $K$ by unitriangular elements. The column $se^*_a$ solves a linear system whose matrix has entries of the elements of $K$ and of $w_p$, and the system has order at most $\varrho$. The product $p_0\cdots p_a$ is the factor that the Weyl element puts in front of the determinant. Cramer's rule writes each entry as a quotient of two determinants. The lemma on determinants gives the size $8\varrho$. $\square$

**Lemma (Heads give sizes).** Let $K$ be as before, $j \leq \varrho$, $p$ a head of length $j$, and $g \in \mathsf{G}$ with $\eta w_p^{-1}g \in K$ for some $\eta \in R^{(j)}$. Let $s \in R^{(j)} \cap U_{<j}$ with $sg \in K$. Then $g$ has size $60n^2$ and $w_p^{-1}g$ has size $99n^2$.

Lean: `New.Floors.Size.hasMatrixSize_of_isHead` (New/Spanning/Frames/TwoGauges.lean).

*Proof.* The head condition turns the products of the lemma on Cramer's rule into entries of $s$ of size about $9n$ (`New.Floors.Size.head_entries_mem_ofSize` gives $10n$). The lemma on inverses bounds $s^{-1}$ (with `New.Floors.Size.hasMatrixSize_inv_of_mem_unipotentBelow`), so $g = s^{-1}(sg)$ has a size of order $n^2$. The matrix of $w_p^{-1}$ has size of order $n$ on the head (`New.Floors.Size.hasMatrixSize_weylElem_inv`). The source collects the constants into $60n^2$ and $99n^2$. $\square$

**Remark (Formalization).** A size is a structure of rules, not a norm. The source never uses an inequality between real numbers in this section, so the same proofs serve at a real place and at the finite places. The price is that each sum over the basis costs one step, and the constants grow with $n$ and $n^2$. The constants are not optimal, and the source does not claim that they are.
