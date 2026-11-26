---
title: Weights, signs and b-places
lean:
  - New/Congruences/LocalLoss/Basic.lean
decls:
  - New.Selmer.cmSign
  - New.Selmer.complexEmbeddingOf
  - New.Selmer.IsMainSummandWeights
  - New.Selmer.lt_natAbs_of_abs_add_liftWeight_le
  - New.Selmer.crystallineLoss
  - New.Selmer.defectBound
  - New.Selmer.fixes_emb_of_fixes_rootsOfUnity
  - New.Selmer.map_sqrtNegDInE_eq_cmSign_mul
  - New.Selmer.map_zeta_eq_zpow_cmSign
  - New.Selmer.placeClass_eq_cmSign_mul_pow
  - New.Selmer.notMem_bPlaces_of_short_arc
  - New.Selmer.cmSign_eq_of_mem_bPlaces
  - New.Selmer.coefficientEmbedding
  - New.Selmer.coefficientEmbedding_surjective
  - New.Selmer.IsCompletionGroup.complexEmbeddingOf_eq_iff
  - New.Selmer.IsCompletionGroup.index_eq_card_range
  - New.Selmer.eq_of_complexEmbeddingOf_localChart_eq
  - New.Selmer.sum_complexEmbeddingOf_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Weights, signs and b-places

A main summand has Hodge-Tate weights, or *jumps*, at each complex embedding of $E$. The local loss at $\ell$ in [the local loss](/chapter/local-loss/) depends on where these jumps lie. This section fixes the shape of the jumps, the constants of the defect bound, and the facts on the signs of embeddings and the b-places that the local loss uses.

### Background on weights

- The field $E = K(\zeta)$ is a CM field with $K = \mathbb{Q}(\sqrt{-d})$ and $\zeta$ a root of unity of order $q_1$. Its CM type $\Phi$ picks one embedding at each infinite place. The infinite places form a group isomorphic to $(\mathbb{Z}/q_1)^\times$ through the action on $\zeta$. The cyclotomic conductor of $E$ is $q_1 d$ ([fields, places and twists](/chapter/fields-places-twists/)).
- The data fix $k = r + 1 - m$, $\mathrm{halfGap} = r^8$, $\Delta = \mathrm{gap} = 2\,\mathrm{halfGap}$, $t = 5r$, the weight $b$ and the lift weights $w_j$. The b-places are a set of infinite places of class $-1$ modulo $q_0$. They are *sparse for the primes up to $L = k t$*: for no prime $\ell \leq L$ and no $0 < i < n < l_0$ are there b-places $\sigma, \tau, \rho$ with $\tau/\sigma \equiv \pm\ell^i$ and $\rho/\sigma \equiv \pm\ell^n$ modulo the part of $q_1$ prime to $\ell$ ([the data and its sizes](/chapter/data-and-sizes/)).
- We fix an isomorphism $\iota : \mathbb{C} \to \bar{\mathbb{Q}}_\ell$ and write $G_\ell = \mathrm{Gal}(\bar{\mathbb{Q}}_\ell/\mathbb{Q}_\ell)$.

### The sign of an embedding

**Definition (Sign).** The *sign* of a complex embedding $\sigma$ of $E$ is $\epsilon_\sigma = 1$ if $\sigma = \Phi(\sigma|)$ is the embedding that the CM type picks at the place of $\sigma$, and $\epsilon_\sigma = -1$ otherwise.

Lean: `New.Selmer.cmSign` (New/Congruences/LocalLoss/Basic.lean).

**Definition (Embedding from a Galois element).** For an embedding $e : E \to \bar{\mathbb{Q}}_\ell$ and $g \in G_\ell$, put $\sigma_{e,g} = \iota^{-1} \circ g^{-1} \circ e$. It is a complex embedding of $E$.

Lean: `New.Selmer.complexEmbeddingOf` (New/Congruences/LocalLoss/Basic.lean).

### The weights of a main summand

The jumps of a main summand at $\sigma$ form a multiset $J(\sigma)$ of integers. The following definition says that each jump is either *low*, between $\Delta/4$ and $2m\Delta$ in absolute value, or *high*, near $-\epsilon_\sigma w_j$. It also bounds the number of small and of negative jumps.

**Definition (Main summand weights).** Let $r, t \in \mathbb{N}$ and let $J$ give a multiset $J(\sigma) \subset \mathbb{Z}$ for each complex embedding $\sigma$. The pair satisfies the *main summand weights* for $D$ if:

1. $1 \leq r \leq D.r$, and $t \leq D.t$;
2. there is $j \leq m$ such that every $u \in J(\sigma)$, for every $\sigma$, satisfies $\Delta \leq 4|u|$ and $|u| \leq 2m\Delta$, or satisfies $|\epsilon_\sigma u + w_j(\sigma)| \leq D.t$;
3. for every $\sigma$, $\#\{u \in J(\sigma) : |u| \leq 2\,\mathrm{halfGap}^2\} \cdot k \leq r m$;
4. for every $\sigma$, the number of negative $u$ in $J(\sigma)$ plus the number of negative $u$ in $J(\bar\sigma)$ is at most $r$.

Lean: `New.Selmer.IsMainSummandWeights` (New/Congruences/LocalLoss/Basic.lean).

**Remark (Formalization).** The counts in 3 and 4 count with multiplicity. The index $j$ in 2 can be $0$, since the source asks only $j \leq m$. The weight $w_j$ is read at the infinite place of $\sigma$, so $w_j(\sigma) = w_j(\bar\sigma)$.

**Lemma (High jumps are large).** Let $B \in \mathbb{N}$ with $B + D.t < w_j(\sigma)$. If $|\epsilon_\sigma u + w_j(\sigma)| \leq D.t$, then $B < |u|$.

Lean: `New.Selmer.lt_natAbs_of_abs_add_liftWeight_le` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* If $\epsilon_\sigma = 1$, then $u \leq D.t - w_j(\sigma) < -B$. If $\epsilon_\sigma = -1$, then $u \geq w_j(\sigma) - D.t > B$. In both cases $|u| > B$. $\square$

### The constants of the defect bound

**Definition (Crystalline loss).** For $h, b, l \in \mathbb{N}$, put
$$\mathrm{crysLoss}(h, b, l) = v_l\Big((2b)! \cdot \Big(\prod_{\max(b - 30h^3, 0) < k \leq b + 30h^3} k\Big)^{h^3}\Big).$$

Lean: `New.Selmer.crystallineLoss` (New/Congruences/LocalLoss/Basic.lean).

**Remark (Formalization).** The definition is marked irreducible, so later proofs use only its value through explicit unfolding. The subtraction $b - 30h^3$ is truncated at $0$, which is the $\max$ above.

**Definition (Defect bound).** For a prime $l$, put
$$\mathrm{defectBound}(l) = 10^6 \cdot \frac{m}{k}\,\big(b\, v_l(M) + \mathrm{crysLoss}(\mathrm{halfGap}, b, l)\big),$$
where $M = p_0 p_1$ is the product of the two level primes.

Lean: `New.Selmer.defectBound` (New/Congruences/LocalLoss/Basic.lean).

**Remark (Formalization).** The bound is a nonnegative real number. The quotient $m/k$ is a real quotient, not a quotient of natural numbers. For $l \nmid M$ with $l > 2b + 30\,\mathrm{halfGap}^3$ both valuations are $0$, so the bound is $0$. This is allowed: the bound is used only as an upper bound, and [the local loss](/chapter/local-loss/) proves it.

### Signs and the field

**Lemma (Embeddings fix the field).** Let $e : E \to \bar{\mathbb{Q}}_\ell$, and let $g \in G_\ell$ fix every $\zeta'$ with $\zeta'^{q_1 d} = 1$. Then $g(e(x)) = e(x)$ for all $x \in E$.

Lean: `New.Selmer.fixes_emb_of_fixes_rootsOfUnity` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* The field $E$ lies in the cyclotomic field $\mathbb{Q}(\mu_{q_1 d})$. Extend $e$ to an embedding $\psi$ of this field. The field is generated by one primitive root $\zeta'$, and $g\psi(\zeta') = \psi(\zeta')$. So $g \circ \psi = \psi$, and $g(e(x)) = g(\psi(x)) = \psi(x) = e(x)$. $\square$

**Lemma (Sign and the square root).** For every complex embedding $\sigma$, $\sigma(\sqrt{-d}) = \epsilon_\sigma \sqrt{-d}$, where on the right $\sqrt{-d}$ is the chosen complex root.

Lean: `New.Selmer.map_sqrtNegDInE_eq_cmSign_mul` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* Either $\sigma = \Phi(\sigma|)$, which sends $\sqrt{-d}$ to the chosen root, or $\sigma$ is its complex conjugate, which sends it to the other root. $\square$

**Lemma (Sign and the root of unity).** For every complex embedding $\sigma$, $\Phi(\sigma|)(\zeta) = \sigma(\zeta)^{\epsilon_\sigma}$.

Lean: `New.Selmer.map_zeta_eq_zpow_cmSign` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* If $\epsilon_\sigma = 1$, then $\sigma = \Phi(\sigma|)$. If $\epsilon_\sigma = -1$, then $\Phi(\sigma|) = \bar\sigma$, and complex conjugation inverts a root of unity. $\square$

### The class of a ratio of places

Write $[y]_m$ for the class modulo $m \mid q_1$ of an infinite place $y$, read in $(\mathbb{Z}/q_1)^\times$.

**Lemma (Class of a ratio).** Let $e : E \to \bar{\mathbb{Q}}_\ell$ and $g, g' \in G_\ell$. Suppose that $g' g^{-1}$ raises $e(\zeta)^{\ell^a}$ to the power $\ell^n$. Let $m \mid q_1$ with $\gcd(\ell^a, m) = 1$, and let $y$ be the place with $(\sigma_{e,g'}|)\, y = \sigma_{e,g}|$. Then $[y]_m = \epsilon_{\sigma_{e,g}}\, \epsilon_{\sigma_{e,g'}}\, \ell^n$ in $\mathbb{Z}/m$.

Lean: `New.Selmer.placeClass_eq_cmSign_mul_pow` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* Write $\sigma = \sigma_{e,g}$, $\sigma' = \sigma_{e,g'}$, $s = \epsilon_\sigma$, $s' = \epsilon_{\sigma'}$, $z = e(\zeta)$, and let $k$ be the class of $y$ in $\mathbb{Z}/q_1$. The place $y$ acts on $\zeta$ by the power $k$. By the lemma on the root of unity, $\sigma(\zeta)^{s} = (\sigma'(\zeta)^{s'})^k$. Apply $\iota$ and then $g'$. This gives $(g'g^{-1})(z)^{s} = z^{s' k}$. Raise to the power $\ell^a$ and use the hypothesis: $z^{\ell^n s \ell^a} = z^{s' k \ell^a}$. The root $z$ is primitive of order $q_1$, so $q_1 \mid (\ell^n s - s' k)\ell^a$. Since $m \mid q_1$ and $\ell^a$ is prime to $m$, we get $s' k \equiv \ell^n s$ modulo $m$. Multiply by $s'$, with $s'^2 = 1$. $\square$

**Lemma (b-places are spaced).** Let $\ell \leq k t$ be prime, let $e : E \to \bar{\mathbb{Q}}_\ell$, and let $0 < i < n < l_0$. Let $g, g', g_1 \in G_\ell$ such that $g' g^{-1}$ raises $e(\zeta)^{\ell^a}$ to the power $\ell^n$ and $g' g_1^{-1}$ raises it to the power $\ell^i$. If the places of $\sigma_{e,g}$ and $\sigma_{e,g'}$ are b-places, then the place of $\sigma_{e,g_1}$ is not a b-place.

Lean: `New.Selmer.notMem_bPlaces_of_short_arc` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* Suppose it is. Let $m$ be the part of $q_1$ prime to $\ell$, so $\ell^a$ is prime to $m$. By the lemma on the class of a ratio, the ratio of the places of $\sigma_{e,g_1}$ and $\sigma_{e,g'}$ is $\pm\ell^i$ modulo $m$, and the ratio of the places of $\sigma_{e,g}$ and $\sigma_{e,g'}$ is $\pm\ell^n$ modulo $m$. These are three b-places of the form that sparseness excludes. $\square$

**Lemma (b-places of one sign).** Let $\ell \mid q_1 d$, let $e : E \to \bar{\mathbb{Q}}_\ell$, and let $g, g' \in G_\ell$. If the places of $\sigma_{e,g}$ and $\sigma_{e,g'}$ are b-places, then $\epsilon_{\sigma_{e,g}} = \epsilon_{\sigma_{e,g'}}$.

Lean: `New.Selmer.cmSign_eq_of_mem_bPlaces` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* Suppose the signs are opposite. *Case $\ell \mid q_1$.* Let $x = e(\beta)$ with $\beta = (1 + \sqrt{-d})/2$. By the lemma on the square root, $\sigma_{e,g}(\sqrt{-d}) + \sigma_{e,g'}(\sqrt{-d}) = 0$. Apply $\iota$ and $g$: this gives $(g g'^{-1})(x) = 1 - x$. The group $G_\ell$ acts by isometries, so $\|1 - x\| = \|x\|$. Also $x(1 - x) = (d + 1)/4$, and the parameters give $\ell \mid (d + 1)/4$ when $\ell \mid q_1$. So $\|x\|^2 < 1$. Then $1 = \|x + (1 - x)\| \leq \max(\|x\|, \|1 - x\|) < 1$, a contradiction. *Case $\ell \nmid q_1$.* Then $\ell = d$. The element $g' g^{-1}$ acts on $e(\zeta)$ as some power $d^n$. By the lemma on the class of a ratio with $a = 0$ and $m = q_0$, the ratio of the two places is $-d^n$ modulo $q_0$. Both places have class $-1$ modulo $q_0$, so the ratio is $1$. So $d^n \equiv -1$ modulo $q_0$, which the parameters exclude. $\square$

### Embeddings at a place above $\ell$

Let $O$ be the ring of integers of a finite extension of $\mathbb{Q}_\ell$ in $\bar{\mathbb{Q}}_\ell$. For $g \in G_\ell$ let $c_g : O \to \mathbb{C}_\ell$ be $x \mapsto g(x)$.

Lean: `New.Selmer.coefficientEmbedding` (New/Congruences/LocalLoss/Basic.lean).

**Lemma (All embeddings of the coefficients).** Every map $O \to \mathbb{C}_\ell$ of $\mathbb{Z}_\ell$-algebras is $c_g$ for some $g \in G_\ell$.

Lean: `New.Selmer.coefficientEmbedding_surjective` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* The field $\bar{\mathbb{Q}}_\ell$ is algebraic over $O$, and $\mathbb{C}_\ell$ is algebraically closed. So the map extends to an embedding $\bar{\mathbb{Q}}_\ell \to \mathbb{C}_\ell$ over $\mathbb{Z}_\ell$. Each such embedding is given by an element of $G_\ell$. $\square$

Now let $j : \Gamma \to G_\ell$ be an open embedding whose image is the group of elements that fix $e(E)$ pointwise. Such a $j$ is a *completion group* for $e$.

**Lemma (Equal embeddings).** For a completion group $j$ for $e$ and $g, g' \in G_\ell$, $\sigma_{e,g} = \sigma_{e,g'}$ if and only if $g g'^{-1} \in j(\Gamma)$. The index of $j(\Gamma)$ in $G_\ell$ is the number of distinct embeddings $\sigma_{e,g}$.

Lean: `New.Selmer.IsCompletionGroup.complexEmbeddingOf_eq_iff`, `New.Selmer.IsCompletionGroup.index_eq_card_range` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* The equality $\sigma_{e,g} = \sigma_{e,g'}$ says that $g^{-1}$ and $g'^{-1}$ agree on $e(E)$, so that $g g'^{-1}$ fixes $e(E)$. That is the first claim. So $g$ and $g'$ give the same embedding if and only if $g^{-1}$ and $g'^{-1}$ lie in one left coset of $j(\Gamma)$. Inversion maps the left cosets onto the set of embeddings. $\square$

For each place $v$ of $E$ above $\ell$ we use a chart: an embedding $e_v$ of $\bar{\mathbb{Q}}$ into $\bar{\mathbb{Q}}_\ell$ that induces a place of $\bar{\mathbb{Q}}$ above $v$. The next section defines the chart.

**Lemma (An embedding knows its place).** If $\sigma_{e_v, g} = \sigma_{e_w, g'}$ for places $v, w$ above $\ell$ and $g, g' \in G_\ell$, then $v = w$. Hence, for every $a$ from complex embeddings to $\mathbb{N}$,
$$\sum_{v \mid \ell}\ \sum_{\sigma \in \{\sigma_{e_v, g}\}} a(\sigma) \leq \sum_\sigma a(\sigma) .$$

Lean: `New.Selmer.eq_of_complexEmbeddingOf_localChart_eq`, `New.Selmer.sum_complexEmbeddingOf_le` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* An element $x \in E$ lies in $v$ if and only if $\|e_v(x)\| < 1$. The group $G_\ell$ and the map $\iota$ do not change the norm. So the equality of embeddings gives $x \in v \iff x \in w$. For the sum, the sets of embeddings for distinct places are disjoint, so the double sum is a sum over their union. $\square$
