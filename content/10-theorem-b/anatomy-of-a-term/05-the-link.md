---
title: The link
lean:
  - New/Spanning/Unfolding/Link.lean
decls:
  - New.orthogonal_isotropicFramePair_iff
  - New.mem_link
  - New.mulVec_apply_inr_of_mem_besselU
  - New.Filling.link_inv_mul_mul_of_mem_besselU
  - New.Filling.mem_link_weylElem_mul_iff
  - New.Filling.link_weylElem_mul_eq_iff
  - New.Filling.commonIsotropic
  - New.Filling.isotropicPerp
  - New.Filling.finrank_link_add_finrank_commonIsotropic
  - New.Filling.finrank_link
  - New.Filling.positiveGram
  - New.Filling.linkSource
  - New.Filling.linkTarget
  - New.Filling.form_linkSource_eq_form_linkTarget
  - New.Filling.linkIsometry
  - New.Filling.dotProduct_positiveGram_mulVec_linkIsometry
  - New.Filling.mem_link_iff_linkIsometry
  - New.Filling.linkIsometry_eq_iff
  - New.Filling.linkIsometry_inv_mul_mul_of_mem_besselU
  - New.mem_link_iff_orthogonal
  - New.Filling.linkIsometry_frameImage_mulVec
  - New.Filling.mul_dotProduct_comp_indexX₀_eq_sub
  - New.Filling.exists_frameImage_eq_iff
  - New.Filling.exists_frameImage_eq_of_frameProducts_mulVec_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The link

The frame products see only the part of $\gamma$ on the frame. The link sees the part of $\gamma$ on the middle space. Let $A$ be the span of $e_0, \dots, e_{\varrho-1}$. It is totally isotropic, and $A^\perp/A$ is the middle space $X_0 \perp Ez$. A vector $t$ orthogonal to $A$ and to $\gamma A$ has a class $[t]$ in $A^\perp/A$, and so does $\gamma^{-1}t$. The link of $\gamma$ is the space of the pairs $([t], [\gamma^{-1}t])$. On the big cell it is the graph of the middle part of $\gamma$. In general it is the graph of an isometry $\Upsilon_\gamma$ of a positive definite space. [The chapter on Bessel functions at a real place](/chapter/bessel-real-place/) defines the link ([Definition](/decl/New.link/)) and uses it at the real places. This section proves its algebraic properties over $E$.

### The link in coordinates

In the basis of $V$ a vector $t$ has three blocks: the coordinates at the $e_a$, at the middle vectors and at the $e^*_a$. Since $h(e_a, e^*_b) = \delta_{ab}$, the product $h(e_a, t)$ is the coordinate $t_{e^*_a}$.

**Lemma (Orthogonality to $A$ and $\gamma A$).** Over a commutative ring with an involution, a vector $t$ is orthogonal to $A$ and to $\gamma A$ if and only if the coordinates of $t$ and of $\gamma^{-1}t$ at every $e^*_a$ vanish.

Lean: `New.orthogonal_isotropicFramePair_iff` (New/Spanning/Unfolding/Link.lean).

*Proof.* The first condition is $h(e_a, t) = t_{e^*_a} = 0$. Since $\gamma$ is an isometry, $h(\gamma e_a, t) = h(e_a, \gamma^{-1}t) = (\gamma^{-1}t)_{e^*_a}$. $\square$

The link is the image of these $t$ under $t \mapsto ([t], [\gamma^{-1}t])$, where $[t]$ is the middle block of $t$. We write a pair as $p = (p_1, p_2)$.

**Lemma (Membership in the link).** A pair $p$ lies in the link of $\gamma$ if and only if there is $a \in F^\varrho$ such that $\gamma(a, p_2, 0)$ has the middle block $p_1$ and the last block $0$.

Lean: `New.mem_link` (New/Spanning/Unfolding/Link.lean).

*Proof.* If $p = ([t], [\gamma^{-1}t])$ with $t$ as in the previous lemma, then $\gamma^{-1}t = (a, p_2, 0)$, where $a$ is the first block of $\gamma^{-1}t$. Its image under $\gamma$ is $t$, whose last two blocks are $(p_1, 0)$. Conversely, put $t = \gamma(a, p_2, 0)$. Its last block vanishes, and so does the last block of $\gamma^{-1}t = (a, p_2, 0)$. Then $[t] = p_1$ and $[\gamma^{-1}t] = p_2$. $\square$

**Lemma (The unipotent group fixes the tail).** Let $u \in \mathsf{U}$ and let $t$ have the last block $0$. Then $ut$ and $t$ have the same middle block and the same last block.

Lean: `New.mulVec_apply_inr_of_mem_besselU` (New/Spanning/Unfolding/Link.lean).

*Proof.* Let $i$ be a middle index or an index $e^*_a$. Then $(ut)_i = \sum_j u_{ij}t_j$. For $\operatorname{level}(j) \leq \operatorname{level}(i)$, $u_{ij} = \delta_{ij}$. Every $j$ with $\operatorname{level}(j) > \operatorname{level}(i) \geq \varrho$ is some $e^*_b$, and $t_j = 0$. So $(ut)_i = t_i$. $\square$

**Lemma (Invariance of the link).** Over a commutative ring with an involution, let $u, u' \in \mathsf{U}$. Then $u^{-1}\gamma u'$ and $\gamma$ have the same link.

Lean: `New.Filling.link_inv_mul_mul_of_mem_besselU` (New/Spanning/Unfolding/Link.lean).

*Proof.* We show that the link of $g$ lies in the link of $vgw^{-1}$ for all isometries $g$ and all $v, w \in \mathsf{U}$. With $g = u^{-1}\gamma u'$, $v = u$, $w = u'$ this gives one inclusion. With $g = \gamma$, $v = u^{-1}$, $w = u'^{-1}$ it gives the other. Let $t$ be orthogonal to $A$ and $gA$. Then $(vgw^{-1})^{-1}vt = wg^{-1}t$. The last blocks of $t$ and $g^{-1}t$ vanish. By the previous lemma $vt$ and $wg^{-1}t$ have the same middle and last blocks as $t$ and $g^{-1}t$. So $vt$ is orthogonal to $A$ and to $vgw^{-1}A$, and it gives the same pair $([t], [g^{-1}t])$. $\square$

### The big cell

Let $w_r$ be the Weyl element with the units $r$ and let $\rho$ lie in the floor group of level $\varrho$, as in [the previous section](/chapter/anatomy-of-a-term/#cells-and-the-discriminant). Then $\rho$ fixes every $e_a$ and $e^*_a$, so it acts on the middle space by a block $\rho_{\mathrm{mid}}$.

**Lemma (The link on the big cell).** Over a field with an involution, with a hermitian invertible Gram matrix, a pair $p$ lies in the link of $w_r\rho$ if and only if $\rho_{\mathrm{mid}}p_2 = p_1$.

Lean: `New.Filling.mem_link_weylElem_mul_iff` (New/Spanning/Unfolding/Link.lean).

*Proof.* The image $w_r\rho(a, p_2, 0)$ has the middle block $\rho_{\mathrm{mid}}p_2$ and the last block made of the $r_b a_b$. Take $a = 0$ and apply the lemma on membership. $\square$

**Theorem (The link determines the big cell).** In the same setting, let $\sigma$ and $\tau$ lie in the floor group of level $\varrho$. Then $w_p\sigma$ and $w_q\tau$ have the same link if and only if $\sigma = \tau$.

Lean: `New.Filling.link_weylElem_mul_eq_iff` (New/Spanning/Unfolding/Link.lean).

*Proof.* If $\sigma = \tau$, the previous lemma gives the same condition for both links, since it does not involve $p$ or $q$. Conversely, for every $b$ the pair $(\tau_{\mathrm{mid}}b, b)$ lies in the link of $w_q\tau$, hence in the link of $w_p\sigma$, so $\sigma_{\mathrm{mid}}b = \tau_{\mathrm{mid}}b$. An element of the floor group is fixed by its middle block, so $w_p\sigma = w_p\tau$ as matrices. Cancel $w_p$. $\square$

So on the big cell the link records $\sigma$, and it forgets $p$. The units $p$ are recorded by the frame products: $D_\varrho = \prod p_a$.

### The rank of the link

From here on the field is $E$ and the form is the rational form. Let $I_\gamma = A \cap \gamma A$ and let $P_\gamma = (A + \gamma A)^\perp$.

Lean: `New.Filling.commonIsotropic` (New/Spanning/Unfolding/Link.lean). Lean: `New.Filling.isotropicPerp` (New/Spanning/Unfolding/Link.lean).

**Lemma (The link is a quotient).** $\dim\operatorname{link}(\gamma) + \dim I_\gamma = \dim P_\gamma$.

Lean: `New.Filling.finrank_link_add_finrank_commonIsotropic` (New/Spanning/Unfolding/Link.lean).

*Proof.* The link is the image of $P_\gamma$ under $t \mapsto ([t], [\gamma^{-1}t])$. A vector lies in $A$ if and only if its middle and last blocks vanish. So $t \in I_\gamma$ if and only if $t \in P_\gamma$ and $[t] = [\gamma^{-1}t] = 0$: the kernel of the map on $P_\gamma$ is $I_\gamma$. Apply rank and nullity. $\square$

**Theorem (The rank of the link).** $\dim\operatorname{link}(\gamma) = k + 1$.

Lean: `New.Filling.finrank_link` (New/Spanning/Unfolding/Link.lean).

*Proof.* The space has dimension $r = 2\varrho + k + 1$. The form is nondegenerate, so $\dim(A + \gamma A) + \dim P_\gamma = r$. Both $A$ and $\gamma A$ have dimension $\varrho$, so $\dim(A + \gamma A) + \dim I_\gamma = 2\varrho$. With the previous lemma, $\dim\operatorname{link}(\gamma) = \dim P_\gamma - \dim I_\gamma = r - 2\varrho = k + 1$. $\square$

### The link isometry

Let $z^+$ be a vector of norm $N$, and let $X_0 \perp Ez^+$ be the positive space with the Gram matrix $\operatorname{diag}(1, \dots, 1, N)$. A pair in the link has the form $p = (y_0 + \lambda'z, y'_0 + \lambda z)$ with $y_0, y'_0 \in X_0$. Put

$$\operatorname{src}(p) = y_0 + \lambda z^+, \qquad \operatorname{tgt}(p) = y'_0 + \lambda'z^+.$$

So the two maps exchange the $z$-coordinates of the two members.

Lean: `New.Filling.positiveGram` (New/Spanning/Unfolding/Link.lean). Lean: `New.Filling.linkSource` (New/Spanning/Unfolding/Link.lean). Lean: `New.Filling.linkTarget` (New/Spanning/Unfolding/Link.lean).

**Lemma (Source and target have the same products).** For $p, q$ in the link of $\gamma$, the positive form gives $\langle\operatorname{src}(p), \operatorname{src}(q)\rangle = \langle\operatorname{tgt}(p), \operatorname{tgt}(q)\rangle$.

Lean: `New.Filling.form_linkSource_eq_form_linkTarget` (New/Spanning/Unfolding/Link.lean).

*Proof.* Let $p = ([t], [\gamma^{-1}t])$ and $q = ([s], [\gamma^{-1}s])$ with $t, s \in P_\gamma$. If two vectors have the last block $0$, their product is the product of their middle blocks, since the first block pairs only with the last. So $h(t, s) = h([t], [s])$ and $h(\gamma^{-1}t, \gamma^{-1}s) = h([\gamma^{-1}t], [\gamma^{-1}s])$. The two left sides are equal, since $\gamma$ is an isometry. Write $[t] = y_0 + \lambda'z$, $[\gamma^{-1}t] = y'_0 + \lambda z$, and $\mu', \mu, s_0, s'_0$ for the parts of $q$. Since $h(z, z) = -N$,

$$\langle y_0, s_0\rangle - N\bar{\lambda}'\mu' = \langle y'_0, s'_0\rangle - N\bar{\lambda}\mu.$$

Move the terms in $N$ across: $\langle y_0, s_0\rangle + N\bar{\lambda}\mu = \langle y'_0, s'_0\rangle + N\bar{\lambda}'\mu'$. This is the claim. $\square$

The positive form is positive definite: $\langle a, a\rangle = \sum|a_i|^2 + N|a_z|^2$ is totally positive for $a \neq 0$, since $E$ is a CM field. So if $\operatorname{src}(p) = 0$ for $p$ in the link, then $\operatorname{tgt}(p)$ has norm $0$, so $\operatorname{tgt}(p) = 0$, and $p = 0$ because $\operatorname{src}$ and $\operatorname{tgt}$ together recover $p$. The same holds with $\operatorname{src}$ and $\operatorname{tgt}$ exchanged. Both maps are injective on the link. The link and $X_0 \perp Ez^+$ have the dimension $k + 1$, so both maps are bijections from the link onto $X_0 \perp Ez^+$.

**Definition (The link isometry).** The link isometry is $\Upsilon_\gamma = \operatorname{tgt} \circ \operatorname{src}^{-1}$, a linear automorphism of $X_0 \perp Ez^+$.

Lean: `New.Filling.linkIsometry` (New/Spanning/Unfolding/Link.lean).

**Theorem (Properties of the link isometry).**

1. $\Upsilon_\gamma$ preserves the positive form.
2. A pair $p$ lies in the link if and only if $\Upsilon_\gamma(\operatorname{src}(p)) = \operatorname{tgt}(p)$. So the link is the graph of $\Upsilon_\gamma$, read through $\operatorname{src}$ and $\operatorname{tgt}$.
3. $\Upsilon_\gamma = \Upsilon_{\gamma'}$ if and only if $\gamma$ and $\gamma'$ have the same link.
4. $\Upsilon_{u^{-1}\gamma u'} = \Upsilon_\gamma$ for $u, u' \in \mathsf{U}$.

Lean: `New.Filling.dotProduct_positiveGram_mulVec_linkIsometry`, `New.Filling.mem_link_iff_linkIsometry`, `New.Filling.linkIsometry_eq_iff`, `New.Filling.linkIsometry_inv_mul_mul_of_mem_besselU` (New/Spanning/Unfolding/Link.lean).

*Proof.* (1) Write $a = \operatorname{src}(p)$ and $b = \operatorname{src}(q)$ with $p, q$ in the link, and apply the previous lemma. (2) One direction is the definition. For the other, let $q$ be the pair in the link with $\operatorname{src}(q) = \operatorname{src}(p)$. Then $\operatorname{tgt}(q) = \Upsilon_\gamma(\operatorname{src}(p)) = \operatorname{tgt}(p)$, so $p = q$. (3) By (2) the isometry determines the link. If the links are equal, then $\Upsilon_\gamma(\operatorname{src}(p)) = \operatorname{tgt}(p) = \Upsilon_{\gamma'}(\operatorname{src}(p))$ for every $p$ in the link, and $\operatorname{src}$ is onto. (4) follows from (3) and the invariance of the link. $\square$

**Lemma (The link is Lagrangian).** On pairs, let $\langle p, q\rangle_\Lambda = h(p_1, q_1) - h(p_2, q_2)$. A pair $p$ lies in the link if and only if $\langle q, p\rangle_\Lambda = 0$ for all $q$ in the link.

Lean: `New.mem_link_iff_orthogonal` (New/Spanning/Unfolding/Link.lean).

*Proof.* A direct expansion gives $\langle q, p\rangle_\Lambda = \langle\operatorname{src}(q), \operatorname{src}(p)\rangle - \langle\operatorname{tgt}(q), \operatorname{tgt}(p)\rangle$. If $p$ is in the link, this vanishes by the lemma on products. Conversely, put $d = \Upsilon_\gamma(\operatorname{src}(p)) - \operatorname{tgt}(p)$ and let $q$ be the pair in the link with $\operatorname{tgt}(q) = d$. The hypothesis and (1) give $\langle d, \Upsilon_\gamma\operatorname{src}(p)\rangle = \langle\operatorname{src}(q), \operatorname{src}(p)\rangle = \langle d, \operatorname{tgt}(p)\rangle$. So $\langle d, d\rangle = 0$, and $d = 0$. Apply (2). $\square$

### The link on the image frame

The link isometry gives a second proof of the norm identity of [the terms of a block](/chapter/anatomy-of-a-term/#the-terms-of-a-block). The source uses this proof in the lemma on vanishing discriminants.

**Theorem (The link isometry on a combination of the image frame).** Let $t = \gamma\mathfrak{f}\cdot c$ with $Z(\gamma)c = (0, \dots, 0, c')$, and let $t_0$ be its $X_0$-part. Then $\Upsilon_\gamma(t_0 + c_\varrho z^+) = -(c'/N)z^+$.

Lean: `New.Filling.linkIsometry_frameImage_mulVec` (New/Spanning/Unfolding/Link.lean).

*Proof.* The products $h(e_a, t) = 0$ are the coordinates of $t$ at $e^*_a$. The vector $\gamma^{-1}t = \mathfrak{f}\cdot c$ has the last block $0$. So $t \in P_\gamma$, and $([t], [\gamma^{-1}t])$ lies in the link. Next $c' = h(z, t) = -Nt_z$, so $[t] = t_0 - (c'/N)z$. Also $[\gamma^{-1}t] = c_\varrho z$. So $\operatorname{src} = t_0 + c_\varrho z^+$ and $\operatorname{tgt} = -(c'/N)z^+$. $\square$

**Theorem (The norm identity through the link).** In the same setting, $N\langle t_0, t_0\rangle = c'\bar{c}' - N^2c_\varrho\bar{c}_\varrho$.

Lean: `New.Filling.mul_dotProduct_comp_indexX₀_eq_sub` (New/Spanning/Unfolding/Link.lean).

*Proof.* By (1) the two vectors of the previous theorem have the same norm: $\langle t_0, t_0\rangle + Nc_\varrho\bar{c}_\varrho = N\cdot c'\bar{c}'/N^2$. Multiply by $N$. $\square$

**Lemma (Shared vectors from the products).** In the same setting, $t$ lies in the span of $\mathfrak{f}$ if and only if $t_0 = 0$. If $Z(\gamma)c = 0$, then $t$ lies in the span of $\mathfrak{f}$.

Lean: `New.Filling.exists_frameImage_eq_iff` (New/Spanning/Unfolding/Link.lean). Lean: `New.Filling.exists_frameImage_eq_of_frameProducts_mulVec_eq_zero` (New/Spanning/Unfolding/Link.lean).

*Proof.* The coordinates of $t$ at the $e^*_a$ vanish. So $t$ lies in the span of $\mathfrak{f}$ exactly when its $X_0$-part vanishes. If $c' = 0$, then $\Upsilon_\gamma(t_0 + c_\varrho z^+) = 0$, and $\Upsilon_\gamma$ is injective, so $t_0 = 0$. $\square$

**Example.** Take $\gamma = 1$. Every $t \in A^\perp$ gives the pair $([t], [t])$, so the link is the diagonal of $(X_0 \perp Ez)^2$. A pair $(y_0 + \lambda z, y_0 + \lambda z)$ has $\operatorname{src} = \operatorname{tgt} = y_0 + \lambda z^+$, and $\Upsilon_1 = 1$. For $\gamma \in \mathsf{U}$ the isometry is also $1$, by (4). For $\gamma = w_p\sigma$ the link is the graph of $\sigma_{\mathrm{mid}}$. If $\sigma_{\mathrm{mid}}$ is $\theta$ on $X_0$ and fixes $z$, then $\Upsilon_\gamma = \theta \oplus 1$.
