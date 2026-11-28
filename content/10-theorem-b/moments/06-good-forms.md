---
title: Good forms
lean:
  - New/Spanning/Unfolding/Moments.lean
decls:
  - New.Filling.sum_norm_sq_coeff_of_isCentralProj
  - New.IsCentralProj.isSymmetricProjection
  - New.Filling.re_sum_coeff_mul_trace_besselTranslate_le
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le
  - New.Filling.finrank_source_eq_sourceDim
  - New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le
  - New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Good forms

This section proves the near isometry (NI) of [the plan](/chapter/theorem-b-plan/#the-four-layers-of-the-proof). The spanning argument of [the chapter on few translates](/chapter/few-translates/) cuts $V$ with a central idempotent $e_0 = g_0\otimes g_1$ of $\mathbb{C}[\bar G]$, which keeps the good forms. It needs $e_0P$ to stay almost an isometry. The idempotent $1 - g_i$ is small at $1$, and this makes the part $(1 - e_0)P$ small.

Throughout, $\rho$ is a representation of $\bar G$ on a finite-dimensional inner product space $V$ that preserves the inner product, and $P$ has amplitude blocks. $E$ carries Weil data, and $S$ is admissible. A group algebra element acts on $V$ by $\rho(x) = \sum_sx(s)\rho(s)$. $\|\cdot\|$ is the Hilbert-Schmidt norm.

### Central idempotents

A central idempotent of $\mathbb{C}[H]$, for a finite group $H$, is an idempotent $x$ whose coefficients form a class function ([Definition](/decl/New.IsCentralProj/), in [the chapter on congruence subgroups](/chapter/congruence-subgroups/#characters-of-finite-groups)). There, $\#H\cdot x$ is a character, so $x(s^{-1}) = \overline{x(s)}$, and $\rho(x)$ is self-adjoint for a unitary $\rho$. The tensor product $\mathtt{piTensorElem}$ of a family $x_i \in \mathbb{C}[G_i]$ has the coefficient $\prod_ix_i(s_i)$ at $s$. It is multiplicative, a family of central idempotents gives a central idempotent, $1 - x$ is a central idempotent with $x$, and $1\otimes x\otimes 1$ acts as $x$ does on the factor (Lean: `New.piTensorElem`, `New.IsCentralProj.piTensorElem`, `New.IsCentralProj.one_sub`, `New.asAlgebraHom_piTensorElem_mulSingle`, in Lib/General/Groups/CharacterTheory.lean).

**Lemma (The $\ell^2$ norm of a central idempotent).** For a central idempotent $x$ of $\mathbb{C}[H]$, $\sum_{s \in H}|x(s)|^2 = \operatorname{Re}x(1)$.

Lean: `New.Filling.sum_norm_sq_coeff_of_isCentralProj` (New/Spanning/Unfolding/Moments.lean).

*Proof.* The coefficient of $x\cdot x$ at $1$ is $\sum_sx(s)x(s^{-1}) = \sum_sx(s)\overline{x(s)} = \sum_s|x(s)|^2$. As $x\cdot x = x$, it equals $x(1)$. Take real parts. $\square$

**Lemma (A central idempotent acts as a projection).** If $\rho$ is a unitary representation of a finite group $H$ and $z$ is a central idempotent of $\mathbb{C}[H]$, then $\rho(z)$ is an orthogonal projection: it is idempotent and self-adjoint.

Lean: `New.IsCentralProj.isSymmetricProjection` (New/Spanning/Unfolding/Moments.lean).

*Proof.* The map $x \mapsto \rho(x)$ is an algebra map, so it keeps idempotents. Self-adjointness is the Volume 4 result `New.IsCentralProj.self_adjoint` on [central projections](/decl/New.IsCentralProj/). $\square$

### One prime

Fix $i$. An element $t$ of the factor $G_i$ gives $\iota_i(t) \in \bar G$, equal to $t$ above $p_i$ and to $1$ above the other prime.

**Lemma (The trace of $r_\psi(x)$).** Let $x$ be a central idempotent of $\mathbb{C}[G_i]$ with $\operatorname{Re}x(1) \leq b^{-8}/2$. Then

$$\operatorname{Re}\sum_{t \in G_i}x(t)\operatorname{tr}r_\psi(\iota_i(t)) \leq b^{-4}D_X.$$

Lean: `New.Filling.re_sum_coeff_mul_trace_besselTranslate_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* The element $\iota_i(t)$ is $1$ above the other prime $p_{i+1}$. [The trace theorem](/chapter/moments/#the-induced-character) with $j = i + 1$ gives $\operatorname{tr}r_\psi(\iota_i(t)) = D_X\psi_U(\iota_i(t))$.

Next, $\psi_U$ may be replaced by its mean $\psi_U^\natural$. For $g \in \bar G$, $g\,\iota_i(t)\,g^{-1} = \iota_i(g_itg_i^{-1})$, and $x(g_itg_i^{-1}) = x(t)$, as $x$ is a class function. So the substitution $t \mapsto g_itg_i^{-1}$ gives

$$\sum_tx(t)\psi_U(g\,\iota_i(t)\,g^{-1}) = \sum_tx(t)\psi_U(\iota_i(t)).$$

Average over $g$: $\sum_tx(t)\psi_U(\iota_i(t)) = \sum_tx(t)\psi_U^\natural(\iota_i(t))$.

The map $\iota_i$ is injective. So the bound on [the induced character](/decl/New.Filling.sum_norm_reducedCharMean_sq_le/) gives $\sum_t|\psi_U^\natural(\iota_i(t))|^2 \leq \sum_{s \in \bar G}|\psi_U^\natural(s)|^2 \leq 2$. By Cauchy-Schwarz and the previous lemma,

$$\Big|\sum_tx(t)\psi_U^\natural(\iota_i(t))\Big|^2 \leq \sum_t|x(t)|^2\sum_t|\psi_U^\natural(\iota_i(t))|^2 \leq \frac{b^{-8}}{2}\cdot 2 = (b^{-4})^2.$$

So the real part of the sum in the lemma is at most $D_X\cdot b^{-4}$. $\square$

**Theorem (One prime).** Let $\rho$ be unitary, let $x$ be a central idempotent of $\mathbb{C}[G_i]$ with $\operatorname{Re}x(1) \leq b^{-8}/2$, and let $x$ act on $V$ through the restriction $\rho\circ\iota_i$. Then $\|\rho(x)P\|^2 \leq 2b^{-4}D_X$.

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_asAlgebraHom_comp_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Let $e = \rho(x)$, an orthogonal projection by the lemma above. Then $(eP)^*eP = P^*e^*eP = P^*eP$. So

$$\|eP\|^2 = \operatorname{Re}\operatorname{tr}(P^*eP) = \operatorname{Re}\sum_tx(t)\operatorname{tr}r_\psi(\iota_i(t)) + \operatorname{Re}\operatorname{tr}P'_x,$$

with $P'_x = \sum_tx(t)\bigl(P^*\rho(\iota_i(t))P - r_\psi(\iota_i(t))\bigr)$ and $\|A\|^2 = \operatorname{tr}(A^*A)$ ([Lemma](/decl/New.hilbertSchmidtNorm_sq_eq_trace/)). The first part is at most $b^{-4}D_X$ by the previous lemma.

For the second part, $\operatorname{tr}P'_x = \langle 1, P'_x\rangle$ in the Hilbert-Schmidt inner product ([Lemma](/decl/New.inner_hilbertSchmidtVector/)). By Cauchy-Schwarz and $\|1\|^2 = D_X$ ([Lemma](/decl/New.Filling.hilbertSchmidtNorm_one_sq_eq_sourceDim/)),

$$|\operatorname{tr}P'_x|^2 \leq D_X\|P'_x\|^2 \leq D_X\cdot\frac{D_X}{b^{12}} \leq D_X\cdot\frac{D_X}{b^8} = (b^{-4}D_X)^2.$$

The bound on $\|P'_x\|^2$ is [the theorem on the combined error](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sum_smul_sub_besselTranslate_sq_le/) of [the section on the identity terms](/chapter/moments/#the-identity-terms), which uses that $x$ is a central idempotent. So the second part is at most $b^{-4}D_X$. Add the two parts. $\square$

The condition on $x(1)$ is used only in the first part. The second part holds for every central idempotent of one factor.

### Both primes

**Lemma (The dimension of the source).** The dimension of the source, as a real number, is $D_X$.

Lean: `New.Filling.finrank_source_eq_sourceDim` (New/Spanning/Unfolding/Moments.lean).

*Proof.* The source has the basis $e_x$ for $x$ in $\mathrm{Classes}\times\mathrm{Coord}$, and $D_X$ is the cardinality of this set. $\square$

Now let $g_0 \in \mathbb{C}[G_0]$ and $g_1 \in \mathbb{C}[G_1]$ be central idempotents with $\operatorname{Re}(1 - g_i)(1) \leq b^{-8}/2$ for both $i$. Let $e_0 = g_0\otimes g_1 \in \mathbb{C}[\bar G]$.

**Theorem (Both primes).** If $\rho$ is unitary, then $\|(1 - \rho(e_0))P\|^2 \leq 4b^{-4}D_X$.

Lean: `New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_one_sub_piTensorElem_comp_sq_le` (New/Spanning/Unfolding/Moments.lean).

*Proof.* Write $e_i$ for the action of $g_i$ through $\rho\circ\iota_i$. The family $(g_0, g_1)$ is the product of $(g_0, 1)$ and $(1, g_1)$, and the tensor product is multiplicative. So $\rho(e_0)$ is the product of the actions of $g_0\otimes 1$ and $1\otimes g_1$. The tensor $1\otimes x\otimes 1$ acts as $x$ acts through $\rho\circ\iota_i$, so $\rho(e_0) = e_0e_1$. The element $e_0$ of $\mathrm{End}(V)$ is an orthogonal projection. For an orthogonal projection $p$, any $q$ and any $A$,

$$\|(1 - pq)A\|^2 \leq \|(1 - p)A\|^2 + \|(1 - q)A\|^2$$

([Lemma](/decl/New.hilbertSchmidtNorm_one_sub_mul_comp_sq_le/), in [the chapter on few translates](/chapter/few-translates/)). The central idempotent $1 - g_i$ satisfies the hypothesis of the theorem on one prime, and $\rho(1 - g_i) = 1 - e_i$. So each part is at most $2b^{-4}D_X$, and the sum is at most $4b^{-4}D_X$. $\square$

**Theorem (Good forms).** If $\rho$ is unitary, then $\rho(e_0)P$ is a near isometry with the error $5b^{-4}$: for every subspace $U$ of the source,

$$\dim U - 5b^{-4}D_X \leq \|\rho(e_0)P\,\mathrm{pr}_U\|^2.$$

Lean: `New.Filling.HasAmplitudeBlocks.isNearIsometry_piTensorElem_comp` (New/Spanning/Unfolding/Moments.lean).

*Proof.* First, $P$ is a near isometry with the error $b^{-4}$. By [the defect of $P$](/decl/New.Filling.HasAmplitudeBlocks.hilbertSchmidtNorm_sub_one_sq_le/), $\|P^*P - 1\|^2 \leq b^{-12}D_X \leq (b^{-4})^2D_X$, as $b \geq 1000$. A map $A$ with $\|A^*A - 1\|^2 \leq \varepsilon^2\dim$ and $\varepsilon \geq 0$ is a near isometry with the error $\varepsilon$ ([Lemma](/decl/New.isNearIsometry_of_hilbertSchmidtNorm_le/)).

Second, $\rho(e_0)$ is an orthogonal projection, since $e_0$ is a central idempotent. The previous theorem gives $\|(1 - \rho(e_0))P\|^2 \leq 4b^{-4}\dim$, with $\dim = D_X$ by the lemma on the dimension. If $A$ is a near isometry with the error $\varepsilon$ and an orthogonal projection $\mathrm{pr}$ misses at most $\delta\dim$ of $\|A\|^2$, then $\mathrm{pr}\,A$ is a near isometry with the error $\varepsilon + \delta$ ([Lemma](/decl/New.IsNearIsometry.proj_comp/)). With $\varepsilon = b^{-4}$ and $\delta = 4b^{-4}$ the error is $5b^{-4}$. $\square$

**Remark (Formalization).** The near isometry is the mean-square notion of [Definition](/decl/New.IsNearIsometry/): the inequality holds for the squared Hilbert-Schmidt norm on every subspace. It does not say that $\|\rho(e_0)Pv\| \geq (1 - \varepsilon)\|v\|$ for each vector $v$ (finding F-059 of [the register of findings](/chapter/register-of-findings/)). [The chapter on few translates](/chapter/few-translates/) uses only the mean-square form. The hypothesis on $\rho$ is the equality $\langle\rho(s)v, \rho(s)v'\rangle = \langle v, v'\rangle$ for all $s$, $v$, $v'$.
