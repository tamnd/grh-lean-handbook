---
title: Tight frames and integrality
lean:
  - New/OneLift/LiftVolumeHeight.lean
decls:
  - New.Data.TightFrameIndex
  - New.Data.exists_frame_weightRep_eq_intCast
  - New.Data.exists_tight_frame_formTuples
  - New.Data.comparisonOp_eq_sum
  - New.Data.comparisonOp_mem_integralForms
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Tight frames and integrality

The operator $U_\vartheta = n_{\mathrm{Aut}}h_j^2\,\mathrm{glue}_\vartheta\mathrm{glue}_\vartheta^*$ is defined through an adjoint, and an adjoint does not see integrality. This section writes $U_\vartheta$ as a finite sum of operators of rank one, $\varphi \mapsto n_{\mathrm{Aut}}\langle\varphi', \varphi\rangle\varphi'$, where each $\varphi'$ is a glued form of an integral tuple. Then property 4 of a comparison operator follows from the integrality of inner products. The tool is a *tight frame*: a finite family of vectors $\eta_T$ with $\sum_T\langle\eta_T, \xi\rangle\eta_T = h^2\xi$ for every $\xi$.

### Tight frames in a Weyl module

Let $\mu^-$ be the family of Young diagrams that gives the weight of the forms on $V^\circ$, one diagram at each infinite place, with rows indexed by the basis of $V^\circ$. Let $M$ be the space of coordinate vectors $\xi$ indexed by the standard fillings of $\mu^-$ (`WeylIndex`). The integer Gram matrix $G$ of the Weyl module is positive definite ([the Gram matrix and Schur's lemma](/chapter/weyl-modules/#the-gram-matrix-and-schurs-lemma)). Write

$$\langle\xi, \xi'\rangle = \xi^*G\,\xi', \qquad \|\xi\|^2 = \mathrm{Re}\,\langle\xi, \xi\rangle$$

(`gramForm` and `weylNormSq`). Let $h_j$ be the hook number of $\mu^-$. The rational unitary group of $V^\circ$ acts on $M$ by the representation $\rho$ of weight $(\mu^-, 0)$ (`weightRep`). We use two results of Volume 5, stated in one line each.

- *Integral tight frame.* There are integer vectors $\eta^0_T$, one for each filling $T$ of $\mu^-$ with increasing columns (`ColumnFilling`), with $\sum_T\langle\eta^0_T, \xi\rangle\eta^0_T = h_j^2\,\xi$ for every $\xi \in M$ and $\|\eta^0_T\|^2 \leq h_j^2$ (`New.exists_tightFrame`, [GramMatrix.lean](lean:Lib/GLn/SchurModule/GramMatrix.lean#L447)).
- *Invariance.* For every ring map $\tau \colon \mathbb{C} \to \mathbb{C}$, every rational unitary $\gamma$ and all $a, b \in M$, $\langle\tau(\rho(\gamma)a), \tau(\rho(\gamma)b)\rangle = \langle\tau(a), \tau(b)\rangle$ (`New.gramForm_map_weightRep`, [SchurNorm.lean](lean:Lib/GLn/SchurModule/SchurNorm.lean#L360); see [norms, invariance and orthogonality](/chapter/weyl-modules/#norms-invariance-and-orthogonality)). We use it for $\tau = \mathrm{conj}$ and $\tau = \sigma\circ\mathrm{conj}$.

Here $\tau(a)$ applies $\tau$ to each coordinate.

**Lemma (A moved integral frame).** Let $\gamma$ be an element of the rational unitary group of $V^\circ$. There are vectors $\eta_T \in M$, one for each filling $T$ of $\mu^-$ with increasing columns, such that:

1. $\sum_T\langle\eta_T, \xi\rangle\,\eta_T = h_j^2\,\xi$ for every $\xi \in M$;
2. for every $T$, $\rho(\gamma)\big(\overline{\eta_T}\big)$ is an integer vector;
3. for every $T$ and every $\sigma \in \mathrm{Aut}(\mathbb{C})$, $\|\sigma(\eta_T)\|^2 \leq h_j^2$.

Lean: `New.Data.exists_frame_weightRep_eq_intCast` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Take the integral frame $\eta^0_T$. For a rational unitary $\delta$ define $u_\delta(\xi) = \overline{\rho(\delta)\,\overline{\xi}}$. The map $u_\delta$ is $\mathbb{C}$-linear, as it is the composite of two conjugate linear maps and a linear one. Since $\rho$ is a representation, $u_{\delta^{-1}}(u_\delta\,\xi) = \xi$. Put $\eta_T = u_{\gamma^{-1}}(\eta^0_T)$.

*Claim 1.* First, $\langle u_{\gamma^{-1}}\xi', \xi\rangle = \langle\xi', u_\gamma\xi\rangle$ for all $\xi', \xi$. Indeed, invariance with $\tau = \mathrm{conj}$ and the element $\gamma^{-1}$, applied to $a = \overline{\xi'}$ and $b = \overline{u_\gamma\xi}$, gives $\langle u_{\gamma^{-1}}\xi', u_{\gamma^{-1}}u_\gamma\xi\rangle = \langle\xi', u_\gamma\xi\rangle$, and $u_{\gamma^{-1}}u_\gamma\xi = \xi$. So

$$\sum_T\langle\eta_T, \xi\rangle\eta_T = u_{\gamma^{-1}}\Big(\sum_T\langle\eta^0_T, u_\gamma\xi\rangle\,\eta^0_T\Big) = u_{\gamma^{-1}}\big(h_j^2\,u_\gamma\xi\big) = h_j^2\,\xi .$$

*Claim 2.* The vector $\eta^0_T$ is real, so $\overline{\eta^0_T} = \eta^0_T$. Then $\overline{\eta_T} = \rho(\gamma^{-1})\eta^0_T$, and $\rho(\gamma)\overline{\eta_T} = \eta^0_T$, an integer vector.

*Claim 3.* Apply invariance with $\tau = \sigma\circ\mathrm{conj}$, the element $\gamma^{-1}$ and $a = b = \overline{\eta^0_T}$. It gives $\|\sigma(\eta_T)\|^2 = \|\sigma(\eta^0_T)\|^2$. The automorphism $\sigma$ fixes integers, so $\sigma(\eta^0_T) = \eta^0_T$, and $\|\eta^0_T\|^2 \leq h_j^2$. $\square$

The vectors $\eta_T$ are not integral. They are integral *after the move* by $\gamma$ and complex conjugation. This is the form in which a tuple value enters the gauge at the place $\iota\circ\mathrm{conj}$ (see the proof of the integrality lemma below).

### Tight frames of tuples

Recall from Section 3 the tuples $\zeta \in \mathcal{T}_j$: one value $\zeta_b \in M$ for each pair $b = (i, c)$ of a choice $i$ and a class $c$ of $V^\circ$. The inner product is $\langle\zeta, \zeta'\rangle = \sum_b\langle\zeta_b, \zeta'_b\rangle$, and the squared norm at $\sigma$ is $\|\zeta\|_\sigma^2 = \sum_b\|\sigma(\zeta_b)\|^2$ (`New.Rows.formTupleNormSq`).

**Definition (Index set of the frame).** The frame of tuples is indexed by the pairs $a = (b, T)$ of a pair $b = (i, c)$ as above and a filling $T$ of $\mu^-$ with increasing columns.

Lean: `New.Data.TightFrameIndex` (New/OneLift/LiftVolumeHeight.lean).

**Lemma (A tight frame of tuples).** Let $\delta(c)$ be a rational unitary of $V^\circ$ for every class $c$. There are tuples $f_a \in \mathcal{T}_j$, one for each index $a$ of the frame, such that:

1. $\sum_a\langle f_a, \zeta\rangle\,f_a = h_j^2\,\zeta$ for every tuple $\zeta$;
2. for every $a$ and every pair $(i, c)$, $\rho(\delta(c))\big(\overline{(f_a)_{(i,c)}}\big)$ is an integer vector;
3. for every $a$ and every $\sigma$, $\|f_a\|_\sigma^2 \leq h_j^2$.

Lean: `New.Data.exists_tight_frame_formTuples` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* For each pair $b = (i, c)$ take the moved frame $\eta_{b,T}$ of the previous lemma for $\gamma = \delta(c)$. Let $f_{(b, T)}$ be the tuple with value $\eta_{b,T}$ at $b$ and $0$ at every other pair.

*Claim 1.* Only the value at $b$ counts in the inner product, so $\langle f_{(b,T)}, \zeta\rangle = \langle\eta_{b,T}, \zeta_b\rangle$. The value at $b'$ of $\sum_a\langle f_a, \zeta\rangle f_a$ comes only from the indices $a = (b', T)$, and it is $\sum_T\langle\eta_{b',T}, \zeta_{b'}\rangle\eta_{b',T} = h_j^2\,\zeta_{b'}$.

*Claim 2.* At the pair $b$ of the index, this is claim 2 of the previous lemma. At every other pair the value is $0$, and $\rho(\delta(c))(0) = 0$ is an integer vector.

*Claim 3.* The tuple has one nonzero value, so $\|f_{(b,T)}\|_\sigma^2 = \|\sigma(\eta_{b,T})\|^2 \leq h_j^2$. $\square$

**Remark (Formalization).** The family $\eta$ is chosen by `choose`, one moved frame for each pair $b$. The statement is existential, so nothing later depends on the choice. In Lean the inner product of the value space $M$ is the Gram form, with the variables in the order of `dotProduct_comm`. The source proves this identity once, in the proof.

### The operator as a sum of rank one operators

**Lemma (Rank one decomposition).** Let $(f_a)$ be tuples with $\sum_a\langle f_a, \zeta\rangle f_a = h_j^2\zeta$ for every tuple $\zeta$. Then for every twist $\vartheta$ and every $\varphi \in \mathcal{F}_\vartheta$,

$$U_\vartheta\,\varphi = \sum_a\big(n_{\mathrm{Aut}}\,\langle\mathrm{glue}_\vartheta f_a, \varphi\rangle\big)\,\mathrm{glue}_\vartheta f_a .$$

Lean: `New.Data.comparisonOp_eq_sum` (New/OneLift/LiftVolumeHeight.lean).

*Proof.* Move the gluing map in each coefficient by the adjoint, and use linearity of $\mathrm{glue}_\vartheta$:

$$\sum_a\langle\mathrm{glue}_\vartheta f_a, \varphi\rangle\,\mathrm{glue}_\vartheta f_a = \mathrm{glue}_\vartheta\Big(\sum_a\langle f_a, \mathrm{glue}_\vartheta^*\varphi\rangle f_a\Big) = h_j^2\,\mathrm{glue}_\vartheta\,\mathrm{glue}_\vartheta^*\varphi .$$

Multiply by $n_{\mathrm{Aut}}$. The left side becomes the right side of the claim, and the right side becomes $U_\vartheta\varphi$. $\square$

### Integrality

**Lemma ($U_\vartheta$ keeps integrality).** Let $\vartheta$ be a twist, $\ell$ a prime with $\ell \nmid \mathrm{Nm}\,Q(\vartheta)$ and $\iota$ an $\ell$-adic place. If $\varphi \in \mathcal{F}_\vartheta$ is integral at $\iota$, then $U_\vartheta\varphi$ is integral at $\iota$.

Lean: `New.Data.comparisonOp_mem_integralForms` (New/OneLift/LiftVolumeHeight.lean).

The proof uses three results of earlier chapters.

- *Weak approximation above $\ell$.* For every $g \in G_f$ of $V^\circ$ there is a rational unitary $\gamma$ with $\gamma g \in \mathcal{K}_\ell$ (`New.exists_mul_mem_integralAbove`, [the p-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)).
- *Integrality of the gluing map.* If $\ell \nmid \mathrm{Nm}\,Q(\vartheta)$ and every value $\zeta_{(i,c)}$ of a tuple has $\|\overline{\zeta_{(i,c)}}\|_{c} \leq 1$ for the gauge of the place $\iota'\circ\mathrm{conj}$ at the representative of $c$, then $\mathrm{glue}_\vartheta\zeta$ is integral at $\iota'$ (`New.Rows.glue_mem_integralForms`, [the comparison operator, part 2](/chapter/comparison-operator-2/)).
- *Integrality of inner products.* If $n$ is divisible by the order of every stabilizer, $\varphi'$ is integral at $\iota\circ\mathrm{conj}$ and $\varphi$ is integral at $\iota$, then $|\iota(n\langle\varphi', \varphi\rangle)| \leq 1$ (`New.LevelPlaces.LevelForm.norm_nsmul_inner_le_one`, [the p-adic gauge](/chapter/automorphic-forms/#the-p-adic-gauge)). The chosen group order $n_{\mathrm{Aut}}$ is such an $n$ for every standard space with at most $2n_m$ basis vectors (`New.Data.card_classAut_dvd_chosenGroupOrder`, [chains of lifts and free levels](/chapter/upper-bound-objects/#chains-of-lifts-and-free-levels)), and the basis of $V_j$ has at most $2n_m$ elements.

*Proof.* For every class $c$ of $V^\circ$ choose, by weak approximation, a rational unitary $\delta(c)$ with $\delta(c)\,g_c \in \mathcal{K}_\ell$, where $g_c$ is the representative of $c$. Take the tight frame $(f_a)$ of tuples for $\delta$.

*Step 1: each glued form is integral at every place above $\ell$.* Let $\iota'$ be an $\ell$-adic place, and let $(i, c)$ be a pair. By property (a) of the gauge, the gauge of $\overline{(f_a)_{(i,c)}}$ at $g_c$ equals the gauge of $\rho(\delta(c))\overline{(f_a)_{(i,c)}}$ at $\delta(c)g_c$. The second vector is an integer vector by claim 2 of the frame lemma, and $\delta(c)g_c \in \mathcal{K}_\ell$. By property (d) its gauge is at most $1$, since $|\iota'\circ\mathrm{conj}(n)| \leq 1$ for every integer $n$. So the tuple $f_a$ satisfies the hypothesis of the integrality of the gluing map, and $\mathrm{glue}_\vartheta f_a$ is integral at $\iota'$. We use this for $\iota' = \iota$ and for $\iota' = \iota\circ\mathrm{conj}$.

*Step 2: the coefficients are integral.* By the rank one decomposition, $U_\vartheta\varphi = \sum_a c_a\,\mathrm{glue}_\vartheta f_a$ with $c_a = n_{\mathrm{Aut}}\langle\mathrm{glue}_\vartheta f_a, \varphi\rangle$. The form $\mathrm{glue}_\vartheta f_a$ is integral at $\iota\circ\mathrm{conj}$ by step 1, and $\varphi$ is integral at $\iota$. So $|\iota(c_a)| \leq 1$ by the integrality of inner products.

*Step 3.* The integral forms at $\iota$ are a module over the ring of $c$ with $|\iota(c)| \leq 1$. Each term $c_a\,\mathrm{glue}_\vartheta f_a$ is integral, so the sum is integral. $\square$

The frame index set and the factor $n_{\mathrm{Aut}}h_j^2$ cost nothing $\ell$-adically. They do cost at infinity, and Section 5 counts that cost.

**Example (Why the frame is needed).** Let $M = \mathbb{C}^2$ with $G = 1$, and let $g = \mathrm{glue}$ be the map $\mathbb{C}^2 \to \mathbb{C}^2$ with matrix $\begin{pmatrix}1 & 1\\ 0 & 2\end{pmatrix}$. Then $g g^* = \begin{pmatrix}2 & 2\\ 2 & 4\end{pmatrix}$, and its entries are integers. Its integrality comes from the standard basis $e_1, e_2$, which is a tight frame with $h = 1$: $g g^*\varphi = \langle g e_1, \varphi\rangle g e_1 + \langle g e_2, \varphi\rangle g e_2$, with $g e_1 = (1, 0)$ and $g e_2 = (1, 2)$. In the source the standard basis is not an integral frame for the Gram form of the Weyl module, so the source uses the frame $\eta^0_T$ with constant $h_j^2$ instead of $1$.
