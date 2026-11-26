---
title: Scalings and ramified forms
lean:
  - New/UpperBound/Size/ShortColumns.lean
decls:
  - New.algFormCentralRep
  - New.sum_pow_apply_eq_zero_iff_exists_eq_sub
  - New.iInf_ker_sum_pow_eq_range
  - New.relIndex_mul_finrank_levelSpace
  - New.Data.not_isChosen_of_N_mem
  - New.Data.mem_levelX
  - New.Data.inf_supportedOn_le_chosenLevel
  - New.Data.IsScalingAt
  - New.Data.exists_isScalingAt_valuation_pow_iff
  - New.Data.scalingGenerator
  - New.Data.scalarFin_scalingGenerator_mem_chosenLevel
  - New.Data.scalarFin_scalingGenerator_pow_mem_levelX_iff
  - New.Data.centralRep
  - New.Data.centralRep_scalingGenerator_pow_eq_one
  - New.Data.ramifiedSourceForms
  - New.Data.ramifyingOp
  - New.Data.ramifiedSourceForms_eq_range
  - New.Data.sum_scalingGenerator_pow_eq_zero_iff_exists_eq_sub
  - New.Data.exists_eq_sub_scalingGenerator
  - New.Data.N_sub_one_le_relIndex_levelX
  - New.Data.finrank_ker_one_sub_scalingGenerator_le
  - New.finrank_ker_mul_le
  - New.Data.finrank_ker_ramifyingOp_le
  - New.Data.le_finrank_ramifiedSourceForms
  - New.Data.f_div_N_sub_one_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Scalings and ramified forms

The lifts of the chain kill a source form of the shape $\psi - z_w\psi$, where $z_w$ is a scaling at a prime $w \mid \pi$ (see [the objects of the upper bound](/chapter/upper-bound-objects/), Section 8). This section defines the scalings and the ramified source forms, shows that the ramified forms are exactly the image of $\prod_w(1 - z_w)$, and proves that they fill all but a fraction $f/(N-1) \le b^{-8}$ of the source forms. Section 4 then shows that they are spanned by short forms.

### Background for the scalings

The following facts come from earlier chapters. Each is stated in one line.

1. At a free level $K$ the dimension of the forms of a weight $W$ is $\#(\Gamma\backslash G_f/K)\cdot\dim W$ ([automorphic forms](/chapter/automorphic-forms/), Section 6).
2. At a free level the number of classes is the class sum $\Sigma_K(1)$, and for levels $K' \le K$ of finite type $\Sigma_{K'}(1) = [K : K']\,\Sigma_K(1)$ ([automorphic forms](/chapter/automorphic-forms/), Section 3).
3. In rank at most $2n_m$ every subgroup of the chosen level is free ([the freeness lemma](/decl/New.Data.classAut_eq_bot_of_le_chosenLevel/)).
4. The level $K_0$ is free, and source forms are the forms on $X_0$ of the weight $(c, e_0)$ fixed by $K_0$ ([the objects of the upper bound](/chapter/upper-bound-objects/), Section 7).
5. The set $\Pi_N$ is a split level for $N$: each $w \in \Pi_N$ has residue field of $N$ elements, the conjugate of a place in $\Pi_N$ is not in $\Pi_N$, and the places above $N$ are those of $\Pi_N$ and their conjugates ([the objects of the upper bound](/chapter/upper-bound-objects/), Section 5).
6. The chosen places lie above the level primes $p_i$, and $p_i < N$ ([the data and its sizes](/chapter/data-and-sizes/)).
7. An integral element of $G_f$ that is $1$ at every place other than a set $S$ of non-chosen places and their conjugates lies in the principal congruence subgroup of level $\pi_M$, which lies in the chosen level ([the objects of the upper bound](/chapter/upper-bound-objects/), Section 6).

The group $U(1)(\mathbb{A}_f)$ of finite ideles $z$ with $z\bar z = 1$ maps to $G_f$ by $z \mapsto z\cdot 1$, the scalar matrix. Scalar matrices commute with every element. So right translation by a scalar matrix maps the forms fixed by a level $J$ to forms fixed by $J$.

**Definition (Central action).** For a level $J$ and a character $\chi$ of $J$, the group $U(1)(\mathbb{A}_f)$ acts on the forms of level $(J, \chi)$ by $(z\varphi)(g) = \varphi(g\cdot z1)$, the action of the scalar matrix by the right regular representation.

Lean: `New.algFormCentralRep` (New/UpperBound/Size/ShortColumns.lean).

### Two facts of linear algebra

**Lemma.** Let $T$ be a linear map of a complex vector space $V$ with $T^r = 1$ for some $r \ge 1$. For $\varphi \in V$, $\sum_{i<r}T^i\varphi = 0$ if and only if $\varphi = \psi - T\psi$ for some $\psi \in V$.

Lean: `New.sum_pow_apply_eq_zero_iff_exists_eq_sub` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Suppose that $\sum_{i<r}T^i\varphi = 0$. For each $i$, $1 - T$ divides $1 - T^i$ in the ring of polynomials in $T$, so $\sum_{i<r}(1 - T^i) = (1 - T)S$ for some $S$ that commutes with $T$. Apply this to $\varphi$: the left side is $r\varphi - \sum_i T^i\varphi = r\varphi$. So $r\varphi = S\varphi - T(S\varphi)$, and $\psi = r^{-1}S\varphi$ works. Conversely, $\bigl(\sum_{i<r}T^i\bigr)(1 - T) = 1 - T^r = 0$. $\square$

**Lemma (Kernels and the image of a product).** Let $\pi$ be a complex representation of a commutative group on $V$, let $(z_w)_{w \in I}$ be a finite family of elements with $\pi(z_w)^r = 1$ for every $w$, and let $r \ge 1$. Then
$$\bigcap_{w\in I}\ker\Bigl(\sum_{i<r}\pi(z_w)^i\Bigr) = \mathrm{image}\Bigl(\prod_{w\in I}(1 - \pi(z_w))\Bigr).$$

Lean: `New.iInf_ker_sum_pow_eq_range` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Work in the commutative group algebra and write $\sigma_w = \sum_{i<r}z_w^i$. Let $\varphi$ be in every kernel. Then $(r - \sigma_w)\varphi = r\varphi$ for each $w$, and by induction on the number of factors $\prod_w(r - \sigma_w)\varphi = r^{|I|}\varphi$. As in the previous proof, $1 - z_w$ divides $r - \sigma_w = \sum_{i<r}(1 - z_w^i)$. So $\prod_w(r - \sigma_w) = \prod_w(1 - z_w)\cdot q$ for some $q$, and $\varphi = r^{-|I|}\prod_w(1 - z_w)(q\varphi)$ is in the image. Conversely, $\sigma_w(1 - z_w) = 1 - z_w^r$ acts as $0$, and the algebra is commutative, so $\sigma_w$ kills $\prod_u(1 - z_u)\psi$ for each $w$. $\square$

**Lemma (Index and dimension).** Let $K' \le K$ be levels, both free. Then $[K : K']\cdot\dim(\text{forms of level } K) = \dim(\text{forms of level } K')$, for every weight.

Lean: `New.relIndex_mul_finrank_levelSpace` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By fact 1 each dimension is the number of classes times $\dim W$. By fact 2 the number of classes is $\Sigma(1)$, and $\Sigma_{K'}(1) = [K : K']\,\Sigma_K(1)$. $\square$

### The levels at the primes over N

**Lemma.** Let $w$ be a finite place of $E$ above $N$. Then neither $w$ nor $\bar w$ is a chosen place.

Lean: `New.Data.not_isChosen_of_N_mem` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By fact 5 the norm of $w$ is $N$ (the source uses $N \equiv 1 \bmod q_1 d$ for this), and so is the norm of $\bar w$. A chosen place lies above some $p_i$ and has norm $p_i$. By fact 6, $p_i < N$. $\square$

**Lemma (Membership in K_j).** An element $k \in G_f$ on $X_j$ lies in $K_j$ if and only if it lies in the chosen level and, for every $w \in \Pi_N$ and every index $b$, the entry $(k_w - 1)(\mathrm{last}, b)$ has valuation at most $e^{-1}$ in $E_w$.

Lean: `New.Data.mem_levelX` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* An element of the chosen level is integral. For an integral finite adele $t$, $t$ lies in $\pi\hat{\mathcal O}$ if and only if $t_w$ lies in $\pi\mathcal O_w$ at every $w$. The valuation of $\pi$ at a place $w$ is $e^{-1}$ if $w \mid \pi$ and $1$ otherwise. So the condition holds at the places off $\Pi_N$, and at $w \in \Pi_N$ it says that the valuation of $t_w$ is at most $e^{-1}$. Apply this to the entries of the last row of $k - 1$. $\square$

**Lemma.** Let $S$ be a set of finite places above $N$. An integral element of $G_f$ on $X_j$ that is $1$ at every place outside $S$ and $\bar S$ lies in the chosen level.

Lean: `New.Data.inf_supportedOn_le_chosenLevel` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By the lemma before the previous one, no place of $S$ and no conjugate is chosen. Apply fact 7. $\square$

### Scalings

**Definition (Scaling).** Let $w \in \Pi_N$. A *scaling at $w$* is an element $z \in U(1)(\mathbb{A}_f)$ with integral components such that $z_u = 1$ for every finite place $u$ with $u \ne w$ and $\bar u \ne w$.

Lean: `New.Data.IsScalingAt` (New/UpperBound/Size/ShortColumns.lean).

**Lemma (Scalings exist).** For every $w \in \Pi_N$ there is a scaling $z$ at $w$ such that, for every $i \ge 0$, $v_w(z_w^i - 1) < 1$ if and only if $N - 1 \mid i$.

Lean: `New.Data.exists_isScalingAt_valuation_pow_iff` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By fact 5 the residue field at $w$ has $N$ elements. Its unit group is cyclic of order $N - 1$, and the map from the units of $\mathcal O_w$ onto it is onto. So there is a unit $x$ of $\mathcal O_w$ whose residue has order $N - 1$. Then $x^i \equiv 1$ modulo $w$, that is $v_w(x^i - 1) < 1$, if and only if $N - 1 \mid i$. Let $t$ be the idele that is $x$ at $w$ and $1$ elsewhere, and put $z = t/\bar t$. Then $z\bar z = 1$. At a place $u$, $z_u = t_u/t_{\bar u}$, where $t_{\bar u}$ is read through the conjugation. This is $1$ unless $u = w$ or $\bar u = w$, and every component is a unit. The prime $w$ splits, so $\bar w \ne w$, and $z_w = x/1 = x$. $\square$

**Definition (Chosen scaling).** For $w \in \Pi_N$, the chosen scaling $z_w$ is a scaling given by the previous lemma.

Lean: `New.Data.scalingGenerator` (New/UpperBound/Size/ShortColumns.lean).

**Remark (Formalization).** The chosen scaling is defined with `Exists.choose`. Only the two properties of the lemma are used, through `isScalingAt_scalingGenerator` and `valuation_scalingGenerator_pow_sub_one_lt_one_iff`.

**Lemma.** For every index set, the scalar matrix $z_w 1$ lies in the maximal compact subgroup at $w$: it is integral and it is $1$ at every place other than $w$ and $\bar w$. For the index set $X_j$, it lies in the chosen level.

Lean: `New.Data.scalarFin_scalingGenerator_mem_maxCompactAt`, `New.Data.scalarFin_scalingGenerator_mem_chosenLevel` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The first claim is the definition of a scaling, read entrywise on a diagonal matrix. For the second, apply the lemma on elements supported above $N$ with $S = \{w, \bar w\}$. $\square$

**Lemma (Powers of a scaling in K_j).** For $i \ge 0$, $(z_w1)^i \in K_j$ if and only if $N - 1 \mid i$.

Lean: `New.Data.scalarFin_scalingGenerator_pow_mem_levelX_iff` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The power lies in the chosen level by the previous lemma. By the lemma on membership in $K_j$ it is enough to look at the last row of $(z_w1)^i - 1$ at each $u \in \Pi_N$. At $u$ this matrix is the scalar $z_{w,u}^i - 1$. A valuation is less than $1$ if and only if it is at most $e^{-1}$. If the condition holds, take $u = w$ and the diagonal entry: $v_w(z_w^i - 1) < 1$, so $N - 1 \mid i$. If $N - 1 \mid i$, then at $u = w$ the diagonal entry has valuation less than $1$, and the other entries of the row are $0$. At $u \ne w$ in $\Pi_N$, also $\bar u \ne w$, since $\bar w$ is not in $\Pi_N$. So $z_{w,u} = 1$ and the matrix is $0$. $\square$

### Ramified source forms

**Definition (Central action on source forms).** The group $U(1)(\mathbb{A}_f)$ acts on source forms by the central action at the level $K_0$.

Lean: `New.Data.centralRep` (New/UpperBound/Size/ShortColumns.lean).

**Lemma.** For every $w \in \Pi_N$, the operator $z_w^{N-1}$ is the identity on source forms. The same holds for the forms on $X_j$ fixed by $K_j$.

Lean: `New.Data.centralRep_scalingGenerator_pow_eq_one`, `New.Data.algFormCentralRep_scalingGenerator_pow` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The operator is right translation by $(z_w1)^{N-1}$, which lies in $K_j$ by the previous lemma. The forms are fixed by $K_j$. $\square$

**Definition (Ramified source forms).** A source form $\varphi$ is *ramified* if $\sum_{i < N-1}z_w^i\varphi = 0$ for every $w \in \Pi_N$. They form a subspace $\mathrm{src}$. For a set $s \subseteq \Pi_N$, put $R_s = \prod_{w\in s}(1 - z_w)$, an operator on source forms.

Lean: `New.Data.ramifiedSourceForms`, `New.Data.ramifyingOp` (New/UpperBound/Size/ShortColumns.lean).

**Theorem (Ramified forms are an image).** The space $\mathrm{src}$ is the image of $R_{\Pi_N}$.

Lean: `New.Data.ramifiedSourceForms_eq_range` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Apply the lemma on kernels and the image of a product, with $r = N - 1$. This is nonzero in $\mathbb{C}$ since $N$ is a prime. The previous lemma gives $z_w^{N-1} = 1$. $\square$

**Theorem.** Let $w \in \Pi_N$ and let $\varphi$ be a form on $X_j$ fixed by $K_j$. Then $\sum_{i<N-1}z_w^i\varphi = 0$ if and only if $\varphi = \psi - z_w\psi$ for a form $\psi$ on $X_j$ fixed by $K_j$. In particular, if $\varphi$ is a ramified source form, then for each $w$ there is a source form $\psi$ with $\varphi = \psi - z_w\psi$.

Lean: `New.Data.sum_scalingGenerator_pow_eq_zero_iff_exists_eq_sub`, `New.Data.exists_eq_sub_scalingGenerator` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Apply the first lemma of linear algebra to $T = z_w$ on the forms fixed by $K_j$, with $r = N - 1$ and $T^r = 1$ from the previous lemma. For a ramified source form, the sum at $w$ is $0$ by definition, and $j = 0$. $\square$

### The forms that are not ramified are few

By rank-nullity, $\dim\mathrm{src} = \dim\mathcal F - \dim\ker R_{\Pi_N}$. So it is enough to bound the kernel.

**Lemma.** Let $K$ be a level that contains $z_w1$. Then $[K : K \cap K_0] \ge N - 1$.

Lean: `New.Data.N_sub_one_le_relIndex_levelX` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The level $K$ is compact and $K_0$ is open, so the index $r = [K : K \cap K_0]$ is finite and positive. The $r + 1$ cosets $(z_w1)^i(K\cap K_0)$, $0 \le i \le r$, cannot all be distinct. So $(z_w1)^i \in K_0$ for some $0 < i \le r$. By the lemma on powers of a scaling, $N - 1 \mid i$, so $N - 1 \le i \le r$. $\square$

**Lemma (Fixed forms of a scaling).** For $w \in \Pi_N$, the source forms with $z_w\varphi = \varphi$ form a space of dimension at most $(N-1)^{-1}\dim\mathcal F$.

Lean: `New.Data.finrank_ker_one_sub_scalingGenerator_le` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Let $K$ be the group generated by $K_0$ and $z_w1$. A source form fixed by $z_w$ is fixed by $K_0$ and by $z_w1$, so it is fixed by $K$ (`New.Data.coe_mem_levelSpace_sup_zpowers`). So the fixed forms embed in the forms of level $K$.

Both $K_0$ and $z_w1$ lie in the chosen level, so $K$ does too. So $K$ is integral, it is open since it contains $K_0$, and it is a level. The rank of $X_0$ is $n_0 \le 2n_m$, so by fact 3 the level $K$ is free, and $K_0$ is free by fact 4. The lemma on index and dimension gives
$$[K : K_0]\cdot\dim(\text{forms of level } K) = \dim\mathcal F.$$
The previous lemma gives $[K : K_0] \ge N - 1$. So the dimension of the fixed forms is at most $\dim(\text{forms of level } K) \le (N-1)^{-1}\dim\mathcal F$. $\square$

**Lemma.** For linear maps $F$ and $G$ of a finite-dimensional space, $\dim\ker(FG) \le \dim\ker F + \dim\ker G$.

Lean: `New.finrank_ker_mul_le` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* $\ker(FG) = G^{-1}(\ker F)$. The map $G$ sends it into $\ker F$ with kernel $\ker G$. $\square$

**Lemma.** For $s \subseteq \Pi_N$, $\dim\ker R_s \le |s|\,(N-1)^{-1}\dim\mathcal F$.

Lean: `New.Data.finrank_ker_ramifyingOp_le` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Induction on $s$. $R_\emptyset = 1$ has kernel $0$. For $w \notin s$, $R_{s\cup\{w\}} = (1 - z_w)R_s$ (`New.Data.ramifyingOp_cons`). The kernel of $1 - z_w$ is the space of fixed forms. Apply the previous lemma and the lemma on fixed forms. $\square$

**Theorem (Most source forms are ramified).** $\dim\mathrm{src} \ge \bigl(1 - f/(N-1)\bigr)\dim\mathcal F$.

Lean: `New.Data.le_finrank_ramifiedSourceForms` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* By the theorem that the ramified forms are an image and rank-nullity, $\dim\mathrm{src} + \dim\ker R_{\Pi_N} = \dim\mathcal F$. The set $\Pi_N$ has $f$ elements, so the previous lemma gives $\dim\ker R_{\Pi_N} \le f(N-1)^{-1}\dim\mathcal F$. $\square$

**Lemma.** $f/(N-1) \le b^{-8}$.

Lean: `New.Data.f_div_N_sub_one_le` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* The table of sizes gives $f \le b$ and $b^9 + 1 \le N$. So $f/(N-1) \le b/b^9 = b^{-8}$. $\square$

**Remark (Formalization).** The two size facts are proved by `le_of_hasLogBound`, which checks them against the table of sizes in [the data and its sizes](/chapter/data-and-sizes/), Section 6. In the source the statement $f \le b$ is the instance for the pair $(f, b)$, and $b^9 + 1 \le N$ is the instance for $(b^9 + 1, N)$.

**Example.** Take the toy case of one place $w$, $N = 5$, and a space of dimension $8$ on which $z_w$ acts with the eigenvalues $1, \zeta, \zeta^2, \zeta^3$, each twice, where $\zeta$ is a primitive fourth root of unity. Then $\sum_{l<4}z_w^l$ is $4$ times the projection to the eigenvalue $1$. Its kernel is the sum of the other eigenspaces, of dimension $6$. This is the image of $1 - z_w$, which kills the eigenvalue $1$ and is invertible on the others. The fixed space has dimension $2 = 8/4$, so the bound of the lemma on fixed forms is sharp here.
