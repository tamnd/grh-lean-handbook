---
title: Weights of regular parameters
lean:
  - New/Determinant/AuxiliaryForms/RegularParameters.lean
decls:
  - New.Exchange.abs_hcParameter_le_of_isHCParam
  - New.Exchange.hcParameter_sub_one
  - New.Exchange.boxes_le_card_mul_of_isHCParam
  - New.Exchange.natAbs_le_of_isHCParam
  - New.Exchange.exists_eq_add_card_add_sum_Ioc
  - New.Exchange.exists_isHCParam_of_le
  - New.Exchange.exists_isHCParam_of_hasGap
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Weights of regular parameters

On the last path the forms are algebraic forms of a weight $(\kappa, e)$. Section 7 must find this weight from the parameter of the node, and it must bound the weight. This section gives the two tools: every regular parameter comes from a weight, and a bound on the parameter bounds the weight. All results are in [RegularParameters.lean](lean:New/Determinant/AuxiliaryForms/RegularParameters.lean), in the namespace `New.Exchange`.

### Results used

1. A *weight* is a pair $(\kappa, e)$ with $\kappa_w(h) \in \mathbb{N}$, the number of columns of height $h$ at the place $w \in \Phi$, and $e_w \in \mathbb{Z}$, the power of the determinant. In rank $N$, the diagram weight is $\mu_w(p) = \sum_{p < h < N} \kappa_w(h)$, and `hcParameter` at $(w, p)$ is $2(e_w + \mu_w(p)) + N - 1 - 2p$. The predicate $\mathrm{IsHCParam}(\kappa, e, l)$ says that each $l_w \colon n \to \mathbb{Z}$ is injective and each value $l_w(i)$ is `hcParameter` at $(w, p)$ for some $p < |n|$ ([norms, invariance and orthogonality](/chapter/weyl-modules/#norms-invariance-and-orthogonality)).
2. If $\mathrm{IsHCParam}(\kappa, e, l)$, every position $p < |n|$ is taken: some $i$ has $l_w(i) = $ `hcParameter` at $(w, p)$ (`New.IsHCParam.exists_decreasingPosition_eq`, [SmoothAlgebraicForms.lean](lean:Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean#L454)).
3. The number of boxes `New.boxes` $\kappa$ $N$ is $\sum_w \sum_{h < N} h\,\kappa_w(h)$. It is also the sum of the row lengths $\mu_w(p)$ over $w$ and $p < N$ (`New.FitsRanks.sum_diagramWeight_eq_boxes`, [JetConjugatesAndBounds.lean](lean:New/UpperBound/Kernels/JetConjugatesAndBounds.lean#L511)).
4. A vector $l$ is a *parameter of gap $c$* for the signs $s$ if its entries are distinct, each $l_i + |n| - 1$ is even, and $2c \leq |l_i - l_j|$ for entries of opposite sign ([parameters and their gap](/chapter/discrete-series/#parameters-and-the-coefficient)).

### Bounds from the parameter

Fix $l$ with $\mathrm{IsHCParam}(\kappa, e, l)$ and write $N = |n|$.

**Lemma.** If $|l_w(i)| \leq \beta$ for all $i$, then the entry of `hcParameter` at $(w, p)$ has absolute value at most $\beta$ for every $p < N$. For $N > 0$ the last entry, at $p = N - 1$, is $2 e_w + 1 - N$.

Lean: `New.Exchange.abs_hcParameter_le_of_isHCParam`, `New.Exchange.hcParameter_sub_one` (New/Determinant/AuxiliaryForms/RegularParameters.lean).

*Proof.* By item 2 the entry at $p$ is a value $l_w(i)$, so its absolute value is at most $\beta$. For $p = N - 1$ the sum $\mu_w(N - 1)$ runs over $N - 1 < h < N$, which is empty. So the entry is $2 e_w + N - 1 - 2(N - 1) = 2 e_w + 1 - N$. $\square$

**Proposition.** If $|l_w(i)| \leq \beta$ for all $w$ and $i$, then $\kappa$ has at most $|\Phi|\, N \beta$ boxes in the columns of height below $N$:
$$\mathrm{boxes}(\kappa, N) \leq |\Phi|\, N\, \beta.$$

Lean: `New.Exchange.boxes_le_card_mul_of_isHCParam` (New/Determinant/AuxiliaryForms/RegularParameters.lean).

*Proof.* Count the boxes by rows. Fix $w$ and $p < N$. By the lemma,
$$2(e_w + \mu_w(p)) + N - 1 - 2p \leq \beta, \qquad 2 e_w + 1 - N \geq -\beta.$$
Subtract the second inequality from the first. This gives $2\mu_w(p) + 2(N - 1 - p) \leq 2\beta$. Since $p \leq N - 1$, we get $\mu_w(p) \leq \beta$. By item 3 the boxes are the sum of the $N |\Phi|$ row lengths $\mu_w(p)$. $\square$

**Proposition.** Let $n$ be nonempty. If $|l_w(i)| \leq \beta$ for all $i$, then $|e_w| \leq \beta$.

Lean: `New.Exchange.natAbs_le_of_isHCParam` (New/Determinant/AuxiliaryForms/RegularParameters.lean).

*Proof.* The first entry is $2(e_w + \mu_w(0)) + N - 1 \leq \beta$. Since $\mu_w(0) \geq 0$ and $N \geq 1$, this gives $2 e_w \leq \beta$. The last entry is $2 e_w + 1 - N \geq -\beta$, so $2 e_w \geq N - 1 - \beta \geq -\beta$. So $|2 e_w| \leq \beta$, and $|e_w| \leq \beta$. $\square$

The proof gives $|e_w| \leq \beta / 2$. The source states the weaker bound.

### A weight for each regular parameter

The converse direction starts from distinct integers and builds the column counts from their gaps.

**Lemma.** Let $v \colon \iota \to \mathbb{Z}$ be injective, let $S$ be a finite subset of $\iota$, let $g \in \mathbb{Z}$ with $g \leq v_i$ for all $i \in S$, and let $f \colon \mathbb{N} \to \mathbb{N}$. Then there is $\kappa \colon \mathbb{N} \to \mathbb{N}$ with $\kappa(k) = f(k)$ for $k > |S|$, such that for every $i \in S$ there is $p < |S|$ with
$$v_i + p + 1 = g + |S| + \sum_{p < k \leq |S|} \kappa(k).$$

Lean: `New.Exchange.exists_eq_add_card_add_sum_Ioc` (New/Determinant/AuxiliaryForms/RegularParameters.lean).

*Proof.* Let $s = |S|$ and list the values on $S$ in decreasing order, $u_0 > u_1 > \cdots > u_{s-1}$. They are distinct since $v$ is injective. Give the index of $u_p$ the position $p$. Put $\kappa(s) = u_{s-1} - g$, put $\kappa(k) = u_{k-1} - u_k - 1$ for $1 \leq k < s$, put $\kappa(k) = f(k)$ for $k > s$, and put $\kappa(0) = f(0)$. These numbers are in $\mathbb{N}$, since $u_{s-1} \geq g$ and $u_{k-1} > u_k$. For $p = s - 1$ the claim reads $u_{s-1} + s = g + s + \kappa(s)$, which holds. For $p < s - 1$, subtract the claim for $p + 1$ from the claim for $p$. The left sides differ by $u_p - u_{p+1} - 1$, and the right sides differ by $\kappa(p + 1)$. These are equal by the definition of $\kappa(p + 1)$. So all claims hold by descending induction on $p$. $\square$

The source proves the lemma by induction on $S$. Each step removes the index of the smallest value, puts it at the last position, and applies the induction hypothesis to the rest with $g$ replaced by that value plus $1$.

**Theorem.** Let each $l_w$ be a parameter of gap $c$ for the signs $s$, and let $e_w \leq \lfloor l_w(i)/2 \rfloor + \lfloor N/2 \rfloor$ for all $w$ and $i$. Let $\kappa$ be any column counts. Then there is $f$ with
$$\mathrm{IsHCParam}\big(f,\ w \mapsto e_w + f_w(N),\ l\big),$$
and with $f_w(k) = \kappa_w(k)$ for all $k > N$.

Lean: `New.Exchange.exists_isHCParam_of_le` (New/Determinant/AuxiliaryForms/RegularParameters.lean).

*Proof.* The entries $l_w(i) + N - 1$ are even. So $l_w(i) = 2\lfloor l_w(i)/2 \rfloor + r$ with $r = (N - 1) \bmod 2$ for every $i$, and $i \mapsto \lfloor l_w(i)/2 \rfloor$ is injective. Apply the lemma with $v_i = \lfloor l_w(i)/2 \rfloor$, $S = n$, $g = e_w - \lfloor N/2 \rfloor$ and $f = \kappa_w$. The hypothesis $g \leq v_i$ is the hypothesis on $e_w$. This gives $f_w$ with $f_w = \kappa_w$ above $N$, and for each $i$ a position $p < N$ with
$$v_i + p + 1 = e_w - \lfloor N/2 \rfloor + N + \mu_w(p) + f_w(N),$$
where $\mu_w(p) = \sum_{p < h < N} f_w(h)$. Put $e'_w = e_w + f_w(N)$. Then
$$2 v_i = 2 e'_w + 2\mu_w(p) + 2N - 2\lfloor N/2 \rfloor - 2 - 2p.$$
Since $2N - 2\lfloor N/2 \rfloor = N + (N \bmod 2)$ and $r = 1 - (N \bmod 2)$, we get $l_w(i) = 2 v_i + r = 2(e'_w + \mu_w(p)) + N - 1 - 2p$. This is the entry of `hcParameter` at $(w, p)$. The injectivity of $l_w$ is part of the gap. $\square$

**Remark (Formalization).** The family $f$ is chosen with `choose`, one $f_w$ for each place. The theorem uses only the distinctness and the parity in the gap condition, not the size $c$. The power of the determinant of the weight is $e_w + f_w(N)$, not $e_w$. The column count $f_w(N)$ of height $N$ is a full column, so it shifts the determinant power.

**Corollary.** If every $l_w$ is a parameter of some gap for the signs $s$, then $l$ is twice the Harish-Chandra parameter of some weight $(\kappa, e)$.

Lean: `New.Exchange.exists_isHCParam_of_hasGap` (New/Determinant/AuxiliaryForms/RegularParameters.lean).

*Proof.* For each $w$ choose $e_w$ at most the least of the finitely many numbers $\lfloor l_w(i)/2 \rfloor + \lfloor N/2 \rfloor$. Apply the theorem with $\kappa = 0$. $\square$

### Where the results are used

Section 7 applies `exists_isHCParam_of_le` to the parameters of the nodes $(z, j, m)$ of the last path, with the columns above the rank prescribed by the weights of the theta lifts. It applies the two bounds to get the bounds of `natAbs_lastPathDetExp_le` and `boxes_lastPathColumns_le_natB_mul`. The corollary is used in Section 7 for the branching pairing, and also in [SpanningTheorem.lean](lean:New/Spanning/SecondMoment/SpanningTheorem.lean) and in [RowsFromEigensystems.lean](lean:New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).
