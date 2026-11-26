---
title: Hyperplane sums and block ratios
lean:
  - New/OneLift/FalseLifts/BottomOfTower.lean
decls:
  - New.completeColumns
  - New.det_completeColumns
  - New.rowShear
  - New.rowShear_mul_eq_self_of_vecMul_eq_zero
  - New.rowShear_mul_inclMatrix
  - New.transpose_rowShear_mul_inclMatrix
  - New.det_rowShear
  - New.hyperplaneGroup
  - New.sum_inv_det_hyperplaneGroup_eq_zero
  - New.coeff_hyperplaneSum_eq_ite
  - New.hyperplaneSum_zero
  - New.asAlgebraHom_hyperplaneSum
  - New.HasIntegralBlockRatio
  - New.IsAnnihilatingRow
  - New.exists_isAnnihilatingRow_of_max
  - New.exists_isAnnihilatingRow_of_det_eq_zero
  - New.exists_isAnnihilatingRow_of_one_le
  - New.exists_isAnnihilatingRow_of_not_hasIntegralBlockRatio
  - New.DescentPair.HyperplaneSumsAnnihilate
  - New.DescentPair.blockAction
  - New.DescentPair.sum_formAction_mulSingle_eq_zero
  - New.DescentPair.sum_blockAction_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hyperplane sums and block ratios

This section collects the finite algebra of the bottom of the tower. It has three parts: block matrices and shears, a character sum over a hyperplane group, and a lemma that finds an annihilating row for a matrix without an integral block ratio. Section 3 puts them together.

Throughout, $\iota : r \hookrightarrow n$ is an embedding of finite index types, and $e = (1, 0)^T$ is the $n \times r$ matrix `inclMatrix R ι` whose columns are the unit vectors at $\iota$. For an $n \times r$ matrix $x$ we write $x'$ for the square block of the rows $\iota$ and $x''$ for the block of the other rows. For a row $l$ of length $n$ we write $\lambda = l \circ \iota$ and $\lambda'$ for the other entries. So $l x = \lambda x' + \lambda' x''$.

### Block matrices and shears

**Definition (Completed columns).** For an $n \times r$ matrix $u$, `completeColumns ι u` is $1 + (u - e)e^T$. Its columns $\iota$ are the columns of $u$, and its other columns are those of the identity. In block form it is $\begin{pmatrix} u' & 0 \\ u'' & 1 \end{pmatrix}$.

Lean: `New.completeColumns` (New/OneLift/FalseLifts/BottomOfTower.lean).

**Lemma.** $\det(\text{completeColumns}\ \iota\ u) = \det u'$.

Lean: `New.det_completeColumns` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* The matrix is block lower triangular with diagonal blocks $u'$ and $1$. $\square$

**Definition (Row shear).** For a column $v$ of length $r$ and a row $l$ of length $n$, the row shear is $h_v = 1 + (e v)\, l$. In block form it is $\begin{pmatrix} 1 + v\lambda & v\lambda' \\ 0 & 1 \end{pmatrix}$.

Lean: `New.rowShear` (New/OneLift/FalseLifts/BottomOfTower.lean).

**Lemma (Properties of the shear).** Let $h_v$ be the row shear of $v$ and $l$.

1. If $l x = 0$, then $h_v x = x$.
2. $h_v e = e(1 + v\lambda)$.
3. If $\lambda' = 0$, then $h_v^T e = e(1 + v\lambda)^T$.
4. $\det h_v = \det(1 + v\lambda)$.

Lean: `New.rowShear_mul_eq_self_of_vecMul_eq_zero`, `New.rowShear_mul_inclMatrix`, `New.transpose_rowShear_mul_inclMatrix`, `New.det_rowShear` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) $h_v x = x + (ev)(lx) = x$. (2) $h_v e = e + (ev)(l e) = e + ev\lambda$, since $l e = l \circ \iota = \lambda$. (3) $h_v^T = 1 + l^T (ev)^T$. If $\lambda' = 0$, then $l^T = e\lambda^T$, so $h_v^T e = e + e\lambda^T v^T e^T e = e(1 + \lambda^T v^T)$, as $e^T e = 1$. (4) By the matrix determinant lemma, $\det(1 + ab) = 1 + ba$ for a column $a$ and a row $b$. So $\det h_v = 1 + l e v = 1 + \lambda v = \det(1 + v\lambda)$. $\square$

Property 2 says that $h_v$ is block upper triangular with first block $1 + v\lambda$. Property 3 says that, if $\lambda' = 0$, it is block lower triangular with the same first block. These are the two shapes of matrices that the level group of a descent pair allows: at a chosen place the reduction must fix $e$ up to a first block, and at a twist place it must be block lower triangular. Section 3 uses this through `New.DescentPair.smul_chosenGLRep_eq_apply_of_triangular`.

### The hyperplane group and its character sum

Let $k$ be a field and $l$ a row of length $r$ over $k$.

**Definition (Hyperplane group).** `hyperplaneGroup l` is the set of the invertible matrices $s = 1 + vl$ in $GL_r(k)$, for all columns $v$.

Lean: `New.hyperplaneGroup` (New/OneLift/FalseLifts/BottomOfTower.lean).

It is a subgroup: $(1 + vl)(1 + v'l) = 1 + (v + v' + v(lv'))l$, and the inverse of $1 + vl$ is $1 - (1 + lv)^{-1} v l$. Each $s$ fixes the hyperplane $\ker l$ pointwise. Over a finite field it is finite, and the source gives it a `Fintype` instance through `Fintype.ofFinite`.

**Lemma (The character sum).** Let $k$ be finite, $\chi$ a character of $k^\times$ with $\chi \neq 1$, and $l \neq 0$. Then

$$\sum_{s \in \text{hyperplaneGroup}\ l} \chi^{-1}(\det s) = 0.$$

Lean: `New.sum_inv_det_hyperplaneGroup_eq_zero` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* The map $s \mapsto \chi^{-1}(\det s)$ is a homomorphism from the finite group `hyperplaneGroup l` to $\mathbb{C}^\times$. The sum of a nontrivial homomorphism from a finite group to $\mathbb{C}^\times$ is $0$. So it suffices to see that this homomorphism is not trivial. Since $\chi \neq 1$, there is $\tau \in k^\times$ with $\chi^{-1}(\tau) \neq 1$. Choose $b$ with $l_b \neq 0$, and let $v$ be the column with entry $(\tau - 1)/l_b$ at $b$ and $0$ elsewhere. Then $\det(1 + vl) = 1 + lv = 1 + (\tau - 1) = \tau$. So $s = 1 + vl$ is invertible, it lies in the group, and $\chi^{-1}(\det s) \neq 1$. $\square$

The hyperplane sum of $l$ for $\chi$ is the element $\sum_s \chi(\det s)^{-1} s$ of the group algebra $\mathbb{C}[GL_r(k)]$, summed over `hyperplaneGroup l`. It is defined in [Green's characters](/chapter/finite-gln/#greens-characters-with-squarefree-labels) as `New.hyperplaneSum`, through the condition "$s = 1 + ul$ for some $u$". The next lemmas give it in the form we use.

**Lemma (Hyperplane sums).** Let $k$ be finite.

1. The coefficient of $\text{hyperplaneSum}\ \chi\ l$ at $s$ is $\chi^{-1}(\det s)$ if $s$ lies in `hyperplaneGroup l`, and $0$ otherwise.
2. $\text{hyperplaneSum}\ \chi\ 0 = 1$.
3. In a representation $\sigma$ of $GL_r(k)$, the hyperplane sum acts by $y \mapsto \sum_{s} \chi^{-1}(\det s)\, \sigma(s) y$, summed over `hyperplaneGroup l`.

Lean: `New.coeff_hyperplaneSum_eq_ite`, `New.hyperplaneSum_zero`, `New.asAlgebraHom_hyperplaneSum` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) is the definition. (2) For $l = 0$ the only matrix $1 + v \cdot 0$ is $1$, and $\chi^{-1}(1) = 1$. So the sum is the unit of the group algebra. (3) An element $\sum_s c_s s$ of the group algebra acts by $\sum_s c_s \sigma(s)$. Use (1). $\square$

### Hyperplane sums on forms

Now let $O$ be a descent pair. The group $G_M = \prod_{w \in M} GL_r(k_w)$ acts on `O.FormV` by `O.formAction`: a family $(s_w)$ acts as $\prod_w \psi_w(\det s_w)$ times right translation by an element of the maximal level whose reductions are $\mathrm{diag}(s_w, 1)$ at the chosen places and $1$ at $Q$. See [the objects of the upper bound](/chapter/upper-bound-objects/). For a family of group algebra elements $a_w \in \mathbb{C}[GL_r(k_w)]$, the tensor product $\bigotimes_w a_w$ is the element `piTensorElem` of $\mathbb{C}[G_M]$ whose coefficient at $(s_w)$ is $\prod_w$ (coefficient of $a_w$ at $s_w$).

**Definition (Hyperplane sums annihilate).** The hyperplane sums annihilate the form $y$ if for every $i \in M$ and every family of rows $l_j$ over $k_j$, $j \in M$, with $l_i \neq 0$,

$$\text{formAction}\Big(\bigotimes_{j \in M} \text{hyperplaneSum}\ \psi_j\ l_j\Big)\, y = 0.$$

Lean: `New.DescentPair.HyperplaneSumsAnnihilate` (New/OneLift/FalseLifts/BottomOfTower.lean).

**Definition (Block action).** For a family $s = (s_j)$ of matrices $s_j \in GL_r(k_j)$ at all places $j \in M \sqcup Q$, the form `O.blockAction s y` is

$$\Big(\prod_{j \in M \sqcup Q} \psi_j(\det s_j)^{-1}\Big)\, \text{formAction}(\bar s)\, y,$$

where $\bar s$ is the part of $s$ at the chosen places.

Lean: `New.DescentPair.blockAction` (New/OneLift/FalseLifts/BottomOfTower.lean).

**Lemma (One place at a time).** Let the hyperplane sums annihilate $y$.

1. For $i \in M$ and a row $l \neq 0$ over $k_i$, $\sum_{s} \psi_i(\det s)^{-1}\, \text{formAction}(\text{mulSingle}\ i\ s)\, y = 0$, summed over `hyperplaneGroup l`. Here `mulSingle i s` is $s$ at $i$ and $1$ at the other chosen places.
2. Let $\psi_w \neq 1$ for every $w \in Q$. For every place $j \in M \sqcup Q$ of $O$ and every row $l \neq 0$ over $k_j$, $\sum_{s} \text{blockAction}(\text{mulSingle}\ j\ s)\, y = 0$, summed over `hyperplaneGroup l`.

Lean: `New.DescentPair.sum_formAction_mulSingle_eq_zero`, `New.DescentPair.sum_blockAction_eq_zero` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) Take $l_i = l$ and $l_j = 0$ for $j \neq i$. By part 2 of the lemma on hyperplane sums, the factors at $j \neq i$ are $1$. So the tensor product is the hyperplane sum of $l$ placed in the factor $i$, and by part 3 it acts as the sum in the statement. The definition of annihilation gives $0$.

(2) If $j = i \in M$, then $\text{blockAction}(\text{mulSingle}\ i\ s)\, y = \psi_i(\det s)^{-1}\,\text{formAction}(\text{mulSingle}\ i\ s)\, y$, since the other factors of the product are $\psi(\det 1)^{-1} = 1$. Apply (1). If $j \in Q$, then $\bar s = 1$, so $\text{blockAction}(\text{mulSingle}\ j\ s)\, y = \psi_j(\det s)^{-1} y$. The sum is $\big(\sum_s \psi_j^{-1}(\det s)\big) y$, and this is $0$ by the character sum, since $\psi_j \neq 1$. $\square$

At a twist place the form $y$ plays no role. The vanishing comes from the character alone. This is why the theorem of the bottom of the tower asks $\psi_w \neq 1$ only on $Q$.

### Block ratios and annihilating rows

Now let $w$ be a finite place of a number field, $F_w$ the completion, $\mathcal{O}_w$ its ring of integers and $|\cdot|$ the valuation at $w$, written multiplicatively. So $|a| \leq 1$ means that $a$ is integral and $|a| < 1$ means $a \equiv 0 \bmod w$. Let "chosen" be a proposition. In the applications it says that $w$ is a chosen place.

**Definition (Integral block ratio).** An $n \times r$ matrix $x$ over $F_w$ has an integral block ratio if $x'$ is invertible, the entries of $x''x'^{-1}$ are integral, and, if "chosen" holds, they are $\equiv 0 \bmod w$.

Lean: `New.HasIntegralBlockRatio` (New/OneLift/FalseLifts/BottomOfTower.lean).

The source writes the ratio as the rows outside $\iota$ of $x\,x'^{-1}$. The rows $\iota$ of this matrix are the identity.

**Definition (Annihilating row).** An annihilating row of $x$ is a row $l$ over $\mathcal{O}_w$ with $lx = 0$, with $\lambda \not\equiv 0 \bmod w$, and with $\lambda' \equiv 0 \bmod w$ unless "chosen" holds.

Lean: `New.IsAnnihilatingRow` (New/OneLift/FalseLifts/BottomOfTower.lean).

**Lemma (Normalising a row).** Let $\mu$ be a row over $F_w$ with $\mu x = 0$. Let $b \in r$ with $\mu_{\iota b} \neq 0$ and $|\mu_a| \leq |\mu_{\iota b}|$ for all $a$. Unless "chosen" holds, let also $|\mu_a| < |\mu_{\iota b}|$ for all $a$ outside $\iota$. Then $x$ has an annihilating row.

Lean: `New.exists_isAnnihilatingRow_of_max` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* Let $l = \mu / \mu_{\iota b}$. All its entries have $|l_a| \leq 1$, so $l$ is integral, and $l x = 0$. Its entry at $\iota b$ is $1$, so $\lambda \not\equiv 0$. Unless "chosen" holds, $|l_a| < 1$ for $a$ outside $\iota$, so $\lambda' \equiv 0$. $\square$

**Lemma (Two cases).** Let $x$ be an $n \times r$ matrix over $F_w$.

1. If $\det x' = 0$, then $x$ has an annihilating row.
2. Let $\det x'$ be a unit, $a \notin \iota$ and $b_0 \in r$, with $|(x x'^{-1})_{a b_0}| \geq 1$, and $> 1$ unless "chosen" holds. Then $x$ has an annihilating row.

Lean: `New.exists_isAnnihilatingRow_of_det_eq_zero`, `New.exists_isAnnihilatingRow_of_one_le` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) Since $x'$ is singular, there is a row $\lambda \neq 0$ with $\lambda x' = 0$. Let $\mu = (\lambda, 0)$. Then $\mu x = 0$. Take $b$ with $|\lambda_b|$ largest. Every entry outside $\iota$ is $0 < |\mu_{\iota b}|$. The normalising lemma applies.

(2) Let $R = x x'^{-1}$. The rows $\iota$ of $R$ are the identity, so $x = R x'$, and row $a$ of $x$ is $\sum_b R_{ab}\, x_{\iota b}$. So the row $\mu$ with entries $-R_{ab}$ at $\iota b$, $1$ at $a$ and $0$ elsewhere has $\mu x = 0$. Take $b$ with $|R_{ab}|$ largest. Then $|\mu_{\iota b}| \geq |R_{a b_0}| \geq 1$, so all entries of $\mu$ have modulus at most $|\mu_{\iota b}|$. Unless "chosen" holds, $|\mu_{\iota b}| > 1 \geq |\mu_{a'}|$ for every $a'$ outside $\iota$. The normalising lemma applies. $\square$

**Theorem (Points without an integral block ratio).** If $x$ has no integral block ratio, then $x$ has an annihilating row: an integral row $(\lambda, \lambda')$ with $\lambda x' + \lambda' x'' = 0$, with $\lambda \not\equiv 0 \bmod w$, and with $\lambda' \equiv 0 \bmod w$ unless "chosen" holds.

Lean: `New.exists_isAnnihilatingRow_of_not_hasIntegralBlockRatio` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* If $\det x' = 0$, use case 1. Otherwise $\det x'$ is a unit of the field $F_w$, and one of the two integrality conditions fails. So there are $a \notin \iota$ and $b_0$ with $|R_{ab_0}| > 1$, or "chosen" holds and $|R_{ab_0}| \geq 1$. In both cases the hypothesis of case 2 holds. $\square$

**Example.** Take $r = 1$, $n = 2$, $\iota$ the first index, and $x = (x_1, x_2)^T$. The block ratio is $x_2/x_1$. At a twist place, $x$ has an integral block ratio if $x_1 \neq 0$ and $|x_2| \leq |x_1|$. If this fails, either $x_1 = 0$ and the row is $l = (1, 0)$, or $|x_2| > |x_1|$ and $l = (1, -x_1/x_2)$ after normalising the row $(-x_2/x_1, 1)$. In both cases $\lambda = 1$ and $\lambda' \equiv 0$. The shear of $v$ and $l = (1, -x_1/x_2)$ is $\begin{pmatrix} 1 + v & -v x_1/x_2 \\ 0 & 1\end{pmatrix}$. It fixes $x$, its reduction is upper triangular with entry $1 + v$, and its reduction is also lower triangular, as $\lambda' \equiv 0$.

At a chosen place the stronger condition $|x_2| < |x_1|$ is asked. If $|x_2| = |x_1|$, the row $(-x_2/x_1, 1)$ has both entries of modulus $1$. It is a valid annihilating row there, since $\lambda'$ need not vanish at a chosen place.
