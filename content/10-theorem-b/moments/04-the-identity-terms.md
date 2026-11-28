---
title: The identity terms
lean:
  - New/Spanning/Unfolding/Moments.lean
decls:
  - New.Filling.HasAmplitudeBlocks.adjoint_comp_rep_mul_right
  - New.Filling.HasAmplitudeBlocks.rep_comp_eq_comp_besselTranslate
  - New.Filling.HasAmplitudeBlocks.adjoint_comp_rep_mul_left
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_besselTranslate_sq
  - New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le
  - New.Filling.le_sourceDim_div_of_card_nsmul_le
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le
  - New.Filling.hilbertSchmidtNorm_one_sq_eq_sourceDim
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_adjoint_comp_sq_le
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sum_smul_sub_besselTranslate_sq_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The identity terms

In the Petersson formula the identity term gives the main term $1$ of $\langle P_m, P_m\rangle$. Here the terms in $R_0$ give the operator $r_\psi(s)$, and the analog of "$\langle P_m, P_m\rangle$ is near $1$" is "$P^*P$ is near the identity". This section proves it. The key fact is that the terms in $R_0$ make $P$ an intertwiner between $r_\psi$ and $\rho$ on $\bar R_0$. Then the bound of [the expansion of the squares](/chapter/moments/#the-expansion-of-the-squares), which is a bound for a sum over $\#\bar R_0$ elements, becomes a bound for one operator.

Throughout, $E$ contains a primitive root of unity of order $5040$, $S$ is admissible, $V$ has finite dimension, $\rho$ is a representation of $\bar G$ on $V$, and $P$ has amplitude blocks. We say that $\rho$ is *unitary* if $\langle\rho(s)v, \rho(s)v'\rangle = \langle v, v'\rangle$ for all $s, v, v'$. A result uses this only where it says so. Recall $P_s = P^*\rho(s)P$, and that $\|\cdot\|$ on operators is the Hilbert-Schmidt norm.

### Equivariance

**Lemma (Equivariance on the right).** For $s \in \bar G$ and $t \in \bar R_0$, $P_{st} = P_s\,r_\psi(t)$.

Lean: `New.Filling.HasAmplitudeBlocks.adjoint_comp_rep_mul_right` (New/Spanning/Unfolding/Moments.lean).

*Proof.* We compare the entries $(x, y)$ with $x = (c, i)$ and $y = (d, j)$. Choose a class $d'$ and a term $\delta \in R_0$ over $(d, t^{-1}, d')$ ([Lemma](/decl/New.Filling.exists_besselS_mem_termsOver/)), and a unitary $N$ with $W(\iota_\infty(\delta)y) = NW(y)$.

First, the column $y$ of $r_\psi(t)$. By the lemma on the inverse block, $\overline{\mathcal{A}_{R_0}(e, t, d)_{k, j}} = \mathcal{A}_{R_0}(d, t^{-1}, e)_{j, k}$. By the lemma on blocks of the Bessel group, applied to $\delta$, this is $\nu N_{j, k}$ if $e = d'$ and $0$ otherwise. So

$$r_\psi(t)e_{(d, j)} = \sum_kN_{j, k}\,e_{(d', k)}.$$

Second, the blocks of all terms. The set of all rational points is stable, and $\gamma \mapsto \gamma\delta^{-1}$ maps it to itself. Right translation by $\delta$, which is a term over $(d, t^{-1}, d')$, gives with $(t^{-1})^{-1} = t$

$$\mathcal{A}(c, st, d)_{i, j} = \sum_k\overline{N_{j, k}}\,\mathcal{A}(c, s, d')_{i, k}.$$

Now compute with the hypothesis on $P$:

$$\langle\rho(st)Pe_y, Pe_x\rangle = \sum_k\overline{N_{j, k}}\,\frac{\mathcal{A}(c, s, d')_{i, k}}{\nu} = \sum_k\overline{N_{j, k}}\,\langle\rho(s)Pe_{(d', k)}, Pe_x\rangle = \langle\rho(s)P\,r_\psi(t)e_y, Pe_x\rangle,$$

since the inner product is conjugate linear in the first argument. So $P_{st}$ and $P_sr_\psi(t)$ have the same entries. $\square$

**Lemma (The intertwining).** Let $\rho$ be unitary. Then $\rho(t)P = P\,r_\psi(t)$ for $t \in \bar R_0$.

Lean: `New.Filling.HasAmplitudeBlocks.rep_comp_eq_comp_besselTranslate` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Fix $\varphi$ and put $d = \rho(t)P\varphi - Pr_\psi(t)\varphi$. For every $s$, equivariance on the right with $s^{-1}$ gives $P^*\rho(s^{-1}t)P\varphi = P^*\rho(s^{-1})Pr_\psi(t)\varphi$, that is, $P^*\rho(s^{-1})d = 0$. So for every $\varphi'$

$$\langle\rho(s)P\varphi', d\rangle = \langle P\varphi', \rho(s^{-1})d\rangle = \langle\varphi', P^*\rho(s^{-1})d\rangle = 0,$$

by unitarity. Take $s = t$, $\varphi' = \varphi$, and $s = 1$, $\varphi' = r_\psi(t)\varphi$. Then $\langle d, d\rangle = \langle\rho(t)P\varphi, d\rangle - \langle Pr_\psi(t)\varphi, d\rangle = 0$. So $d = 0$. $\square$

**Lemma (Equivariance on the left).** Let $\rho$ be unitary. For $s \in \bar G$ and $t \in \bar R_0$, $P_{ts} = r_\psi(t)\,P_s$.

Lean: `New.Filling.HasAmplitudeBlocks.adjoint_comp_rep_mul_left` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Apply the intertwining to $t^{-1}$ and take adjoints. As $\rho(t^{-1})^* = \rho(t)$ for unitary $\rho$ and $r_\psi(t^{-1})^* = r_\psi(t)$ by the lemma on the adjoint, $P^*\rho(t) = r_\psi(t)P^*$. Then $P^*\rho(ts)P = P^*\rho(t)\rho(s)P = r_\psi(t)P^*\rho(s)P$. $\square$

### The norm of $P_s - r_\psi(s)$

**Lemma (The terms off $R_0$).** For each $s \in \bar G$, $\|P_s - r_\psi(s)\|^2 = \mathsf{E}(\mathcal{A}_{R_0^c}, \{s\})$.

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_besselTranslate_sq` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Split all terms into those off $R_0$ and those in $R_0$: $\mathcal{A} = \mathcal{A}_{R_0^c} + \mathcal{A}_{R_0}$ ([Lemma](/decl/New.Filling.amplitudeSum_eq_inter_compl_add_inter/)). The entry $(x, y)$ of $P_s$ is the conjugate of $\mathcal{A}(x_1, s, y_1)_{x_2, y_2}/\nu$, and that of $r_\psi(s)$ is the conjugate of $\mathcal{A}_{R_0}(x_1, s, y_1)_{x_2, y_2}/\nu$. So the entry of the difference has the modulus $|\mathcal{A}_{R_0^c}(x_1, s, y_1)_{x_2, y_2}|/\nu$. Sum the squares as in the lemma on the norm of $P_s$. $\square$

**Theorem (The identity terms near $\bar R_0$).** For $i = 0, 1$, let $\Omega_{i+1}$ be the set of $s$ that agree with an element of $\bar R_0$ above $p_{i+1}$, the level prime other than $p_i$. Then

$$\sum_{s \in \Omega_{i+1}}\|P_s - r_\psi(s)\|^2 \leq b^{-12}\mathcal{D}_{\mathrm{id}}.$$

Lean: `New.Filling.HasAmplitudeBlocks.sum_hilbertSchmidtNorm_sub_besselTranslate_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* By the previous lemma the sum is $\sum_{s \in \Omega_{i+1}}\mathsf{E}(\mathcal{A}_{R_0^c}, \{s\}) = \mathsf{E}(\mathcal{A}_{R_0^c}, \Omega_{i+1})$. [The second moment near $\bar R_0$](/decl/New.Filling.secondMoment_compl_besselS_le/) bounds it. $\square$

The index $i + 1$ is taken in $\mathbb{Z}/2$. The source states the theorem in this form because [the good forms](/chapter/moments/#good-forms) use the factor $G_i$ and the set $\bar R_0G_i$, which is contained in $\Omega_{i+1}$.

**Lemma (Division by $\#\bar R_0$).** Let $y$ be real with $\#\bar R_0\cdot y \leq b^{-12}\mathcal{D}_{\mathrm{id}}$. Then $y \leq D_X/b^{12}$.

Lean: `New.Filling.le_sourceDim_div_of_card_nsmul_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* $\mathcal{D}_{\mathrm{id}} = \#\bar R_0\cdot D_X$, and $\#\bar R_0 \geq 1$. Divide by $\#\bar R_0$. $\square$

The lemma needs no hypothesis on $S$.

**Theorem (Near isometry of $P$).** $\|P^*P - 1\|^2 \leq D_X/b^{12}$.

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Put $D = P^*P - 1$. Let $s \in \bar R_0$. Equivariance on the right with the first argument $1$ gives $P_s = (P^*P)\,r_\psi(s)$, so $P_s - r_\psi(s) = Dr_\psi(s)$. By unitary invariance and the invariance of the Hilbert-Schmidt norm under adjoints,

$$\|D\| = \|r_\psi(s^{-1})D^*\| = \|(Dr_\psi(s))^*\| = \|Dr_\psi(s)\| = \|P_s - r_\psi(s)\|.$$

Here $r_\psi(s^{-1}) = r_\psi(s)^*$. So

$$\#\bar R_0\,\|D\|^2 = \sum_{s \in \bar R_0}\|P_s - r_\psi(s)\|^2 \leq \sum_{s \in \Omega_1}\|P_s - r_\psi(s)\|^2 \leq b^{-12}\mathcal{D}_{\mathrm{id}},$$

since $\bar R_0 \subset \Omega_1$ and the terms are nonnegative. Divide by $\#\bar R_0$. $\square$

The theorem does not ask $\rho$ to be unitary: equivariance on the right uses only the hypothesis on $P$.

**Lemma (The norm of the identity).** The identity of the source has $\|1\|^2 = D_X$.

Lean: `New.Filling.hilbertSchmidtNorm_one_sq_eq_sourceDim` (New/Spanning/Unfolding/Moments.lean).

*Proof.* $\|1\|^2 = \sum_x\|e_x\|^2 = \#X = D_X$. $\square$

**Lemma (The norm of $P^*P$).** $\|P^*P\|^2 \leq 2D_X$.

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_adjoint_comp_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* As $b \geq 1000$, $D_X/b^{12} \leq D_X/9 = (\|1\|/3)^2$. So $\|P^*P - 1\| \leq \|1\|/3$. The triangle inequality gives $\|P^*P\| \leq \tfrac43\|1\|$, so $\|P^*P\|^2 \leq \tfrac{16}{9}D_X \leq 2D_X$. $\square$

[The section on the whole group](/chapter/moments/#the-second-moment-over-the-whole-group) uses this bound at $s = 1$, where $P_1 = P^*P$.

### Averages over one factor

The good forms of [a later section](/chapter/moments/#good-forms) need a bound for the operator $\sum_tx(t)(P_t - r_\psi(t))$, where $x$ is a central idempotent of the group algebra of one factor $G_i$ of $\bar G$. The factor $G_i$ is the product of the groups $\mathrm{GL}_r(\mathbb{F}_w)$ over the chosen places $w$ above $p_i$. It embeds in $\bar G$ by $t \mapsto \iota_i(t)$, the element with the component $t$ above $p_i$ and $1$ above the other prime. An element $x = \sum_tx(t)t$ of $\mathbb{C}[G_i]$ is a *central idempotent* if $x^2 = x$ and $t \mapsto x(t)$ is a class function ([Definition](/decl/New.IsCentralProj/)).

The tool is the contraction property of central idempotents. For a homomorphism $\varphi : G \to H$ of finite groups, a central idempotent $e$ of $\mathbb{C}[G]$ and every function $F : H \to V$,

$$\sum_{s \in H}\Big\|\sum_{t \in G}e(t)F(\varphi(t)^{-1}s)\Big\|^2 \leq \sum_{s \in H}\|F(s)\|^2,$$

as $e$ acts on $\ell^2(H, V)$ by an orthogonal projection ([Theorem](/decl/New.IsCentralProj.sum_norm_sq_conv_le/), in [the chapter on congruence subgroups](/chapter/congruence-subgroups/#characters-of-finite-groups)).

**Theorem (The remainder of one factor).** Let $\rho$ be unitary, $i \in \{0, 1\}$, and $x$ a central idempotent of $\mathbb{C}[G_i]$. Then

$$\Big\|\sum_{t \in G_i}x(t)\bigl(P_{\iota_i(t)} - r_\psi(\iota_i(t))\bigr)\Big\|^2 \leq \frac{D_X}{b^{12}}.$$

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sum_smul_sub_besselTranslate_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Put $P'_s = P_s - r_\psi(s)$ and $P'_x = \sum_tx(t)P'_{\iota_i(t)}$. Let $\Omega = \Omega_{i+1}$. Let $F(s) = P'_s$ for $s \in \Omega$ and $F(s) = 0$ otherwise, as a function with values in the Hilbert space of operators with the Hilbert-Schmidt norm.

For $s \in \bar R_0$ and $u \in \bar G$, equivariance on the left and multiplicativity on the left give $P'_{su} = r_\psi(s)P'_u$. For $t \in G_i$ the element $\iota_i(t)$ is $1$ above $p_{i+1}$, so $s\iota_i(t)$ agrees with $s$ above $p_{i+1}$ and lies in $\Omega$. So for $s \in \bar R_0$

$$\Big\|\sum_tx(t)F(s\iota_i(t))\Big\| = \Big\|r_\psi(s)\sum_tx(t)P'_{\iota_i(t)}\Big\| = \|P'_x\|,$$

by unitary invariance. Apply the contraction property to the function $s \mapsto F(s^{-1})$ and reindex the sums by $s \mapsto s^{-1}$:

$$\sum_{s \in \bar G}\Big\|\sum_tx(t)F(s\iota_i(t))\Big\|^2 \leq \sum_{s \in \bar G}\|F(s)\|^2 = \sum_{s \in \Omega}\|P'_s\|^2.$$

Keep only the $s \in \bar R_0$ on the left. Then

$$\#\bar R_0\,\|P'_x\|^2 \leq \sum_{s \in \Omega_{i+1}}\|P_s - r_\psi(s)\|^2 \leq b^{-12}\mathcal{D}_{\mathrm{id}},$$

by the theorem on the identity terms. Divide by $\#\bar R_0$. $\square$

**Remark (Formalization).** The theorem carries the hypotheses $S$ admissible and $\rho$ unitary as explicit arguments, not as section variables. Its statement is the same as with section variables. The idempotent $x$ is not assumed to be self-adjoint. A [central idempotent](/decl/New.IsCentralProj/) is self-adjoint (`New.IsCentralProj.self_adjoint`) for every invariant hermitian form, and the contraction property uses this inside its proof.
