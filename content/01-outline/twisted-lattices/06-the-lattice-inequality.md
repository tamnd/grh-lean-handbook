---
title: The lattice inequality
lean:
  - New/Reduction/Lattices/TwistedLattice.lean
  - Lib/General/LinearAlgebra/GramDeterminant.lean
decls:
  - New.norm_det_mul_det_gram_mul_det_le_one
  - New.TwistedLattice.norm_det_mul_det_gram_le_one
  - New.TwistedLattice.exists_matrix_elim_mem_lattice
  - New.TwistedLattice.norm_pow_mul_det_gram_le
  - New.TwistedLattice.heightLe_pow_mul_det_gram
  - New.TwistedLattice.covolume_add_index_nonneg
  - New.Data.integral_forms_long
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The lattice inequality

This section proves the inequality of the chapter. The proof bounds one nonzero number, the Gram determinant $\mathrm{Gram}(1)$ of a basis, at every place. At the archimedean places the bound comes from the covolume (Section 4). At each $\iota$ the bound comes from the index, through a twist $\xi_\iota$ that may depend on $\iota$.

### The local bound

**Lemma (Integrality of a Gram determinant).** Let $F$ be a normed field with the ultrametric inequality, $\iota\colon \mathbb{C} \to F$ a ring homomorphism, $\varphi = (\varphi_k)_{k \in S}$ a finite family in a complex inner product space, and $u, u'$ complex matrices indexed by $S$. If $\|\iota \langle \sum_c u'_{ac} \varphi_c, \sum_c u_{bc} \varphi_c \rangle\| \leq 1$ for all $a, b \in S$, then
$$\|\iota \overline{\det u'}\| \cdot \|\iota \det \mathrm{Gram}(\varphi)\| \cdot \|\iota \det u\| \leq 1.$$

Lean: `New.norm_det_mul_det_gram_mul_det_le_one` (Lib/General/LinearAlgebra/GramDeterminant.lean).

*Proof.* The matrix of the inner products in the hypothesis is $\bar u' \,\mathrm{Gram}(\varphi)\, u^{\mathsf T}$. Its entries have norm at most $1$, so its determinant has norm at most $1$, by the ultrametric inequality. $\square$

**Lemma (Integrality in a twisted lattice).** Let $\xi$ be allowed at the prime of $\iota$, and let $w$ be a finite family in $V$. If $u$ takes the vectors $\Theta_\xi w_k$ into $\Lambda_{\xi,\iota}$ and $u'$ takes them into $\Lambda_{\xi,\bar\iota}$, then
$$\|\bar\iota \det u'\| \cdot \|\iota \det \mathrm{Gram}(\Theta_\xi w)\| \cdot \|\iota \det u\| \leq 1.$$

Lean: `New.TwistedLattice.norm_det_mul_det_gram_le_one` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Condition 3 of a twisted lattice gives the hypothesis of the previous lemma, and $\bar\iota(x) = \iota(\bar x)$. $\square$

To apply this to a basis $y \sqcup z$, the source needs a matrix for the auxiliary vectors $z$. It takes a scalar: a number $\gamma \neq 0$ with $\gamma\Theta_\xi z_i$ integral.

**Lemma (A matrix for the basis).** Let $\xi$ be allowed at the prime of $\iota$. Let $u$ over $\mathcal{O}_\iota$ take $y_1, \dots, y_n$ into the integral vectors of $V$ at $\iota$, and let $\gamma \Theta_\xi z_i \in \Lambda_{\xi,\iota}$ for $i = 1, \dots, n'$. Then the block diagonal matrix $v$ with blocks $u$ and $\gamma \cdot 1$ takes the vectors $\Theta_\xi y_1, \dots, \Theta_\xi z_{n'}$ into $\Lambda_{\xi,\iota}$, and $\det v = \det u \cdot \gamma^{n'}$.

Lean: `New.TwistedLattice.exists_matrix_elim_mem_lattice` (New/Reduction/Lattices/TwistedLattice.lean).

**Lemma (The local bound).** Let $\xi$ be allowed at the prime $\ell$ of $\iota$. Let $u$ carry $y$ into the integral vectors at $\iota$, and $u'$ carry $y$ into the integral vectors at $\bar\iota$, both with loss $a$. Let $\gamma\Theta_\xi z_i$ be integral both at $\iota$ and at $\bar\iota$. Then
$$\big\|\iota\big(|\gamma|^{2n'} \mathrm{Gram}(\xi)\big)\big\| \leq e^{2a\log \ell},$$
where $\mathrm{Gram}(\xi)$ is the Gram determinant of $\Theta_\xi y_1, \dots, \Theta_\xi y_n, \Theta_\xi z_1, \dots, \Theta_\xi z_{n'}$.

Lean: `New.TwistedLattice.norm_pow_mul_det_gram_le` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Take the matrices $v$ at $\iota$ and $v'$ at $\bar\iota$ of the previous lemma, and apply the integrality lemma. Since $|\gamma|^2 = \bar\gamma\gamma$, we have $\|\iota |\gamma|^{2n'}\| = \|\bar\iota\gamma\|^{n'} \|\iota\gamma\|^{n'}$. The losses give $\|\iota \det u\| \geq e^{-a\log\ell}$ and $\|\bar\iota \det u'\| \geq e^{-a\log\ell}$. $\square$

**Lemma (The height of the twisted Gram determinants).** Let $y$ have index at most $\delta$. For each $\iota$ let $\xi_\iota$ be a twist allowed at the prime of $\iota$, and let $\gamma_\iota \Theta_{\xi_\iota} z_i$ be integral at $\iota$ and at $\bar\iota$. Then the family $|\gamma_\iota|^{2n'} \mathrm{Gram}(\xi_\iota)$ has height at most $2\delta$.

Lean: `New.TwistedLattice.heightLe_pow_mul_det_gram` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* The index gives matrices at $\iota$ and at $\bar\iota$ with the same loss $e(\ell)$, since $\iota$ and $\bar\iota$ lie over the same prime. Both matrices serve for the twist $\xi_\iota$, because the matrices of the index do not depend on the twist. Apply the local bound and [the lemma](/decl/New.HeightLe.of_le/) with no multiplier, with $e(\ell) = 2e(\ell) \log \ell$. $\square$

### The inequality

**Theorem (Covolume plus twice the index is not negative).** Let $V$ be a complex inner product space of finite dimension with a twisted lattice whose maps $\Theta_\xi$ are all injective. Let $y_1, \dots, y_n, z_1, \dots, z_{n'}$ be linearly independent, with $\dim V = n + n'$. For each $\iota$ let $\xi_\iota$ be a twist allowed at the prime of $\iota$. Let $c, \delta, b_{\mathrm{short}}, b_{\mathrm{denom}}, b_{\mathrm{volume}} \in \mathbb{R}$. Suppose that:

1. $y$ has covolume at most $c$ and index at most $\delta$;
2. $\gamma\colon T \to \mathbb{C}$ has $\gamma(\xi) \neq 0$ for all $\xi$, and $\gamma(\xi)\Theta_\xi z_i \in \Lambda_{\xi,\iota}$ for all $i$, all $\iota$, and all $\xi$ allowed at the prime of $\iota$;
3. $\|\Theta_1 z_i\|_\sigma^2 \leq e^{b_{\mathrm{short}}}$ for all $i$ and all automorphisms $\sigma$ of $\mathbb{C}$;
4. the family $|\gamma(\xi_\iota)|^{-2}$ has height at most $b_{\mathrm{denom}}$;
5. the family $Z(1)/Z(\xi_\iota)$ has height at most $b_{\mathrm{volume}}$.

Then
$$0 \leq c + 2\delta + n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}}.$$

Lean: `New.TwistedLattice.covolume_add_index_nonneg` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Write $\mathrm{Gram}(\xi)$ for the Gram determinant of $\Theta_\xi$ applied to the basis $y \sqcup z$. By [the lemma](/decl/New.det_gram_comp/) on Gram determinants, $\mathrm{Gram}(\xi) = Z(\xi) \det\mathrm{Gram}(y \sqcup z)$. Since $Z(\xi_\iota) \neq 0$ and $\gamma(\xi_\iota) \neq 0$, for every $\iota$
$$\mathrm{Gram}(1) = |\gamma(\xi_\iota)|^{2n'} \mathrm{Gram}(\xi_\iota) \cdot \big(|\gamma(\xi_\iota)|^{-2}\big)^{n'} \cdot \frac{Z(1)}{Z(\xi_\iota)}.$$
The first factor has height at most $2\delta$, by the last lemma, with hypothesis 2 at $\iota$ and at $\bar\iota$. The second has height at most $n' b_{\mathrm{denom}}$ and the third at most $b_{\mathrm{volume}}$. By the lemma on products, the constant family $\mathrm{Gram}(1)$ has height at most $2\delta + n' b_{\mathrm{denom}} + b_{\mathrm{volume}}$. Since $\Theta_1$ is injective and $y \sqcup z$ is independent, $\mathrm{Gram}(1) \neq 0$. By [adjoining short vectors](/decl/New.TwistedLattice.CovolumeLe.sumElim/) and the theorem on conjugates of the Gram determinant, $|\sigma\,\mathrm{Gram}(1)| \leq e^{c + n' b_{\mathrm{short}}}$ for every $\sigma$. [The corollary](/decl/New.HeightLe.neg_le_of_norm_map_le/) of the product formula gives $-(2\delta + n' b_{\mathrm{denom}} + b_{\mathrm{volume}}) \leq c + n' b_{\mathrm{short}}$. $\square$

**Example (Rank one: Liouville's inequality).** Take the standard twisted lattice with $V = \mathbb{C}$, $n = 1$, $n' = 0$, and $\gamma = 1$. Then hypotheses 2 and 3 are empty, and hypotheses 4 and 5 hold with $b_{\mathrm{denom}} = b_{\mathrm{volume}} = 0$. For $y \in \mathbb{C}$, $y \neq 0$, the theorem says: if $|\sigma y|^2 \leq e^c$ for all $\sigma$ and $y$ has index at most $\delta$, then $c + 2\delta \geq 0$. For an algebraic integer $y$ the index is at most $0$, and so $\max_\sigma |\sigma y| \geq 1$. This is Liouville's inequality of Section 2. For $y = 1/2$, $c = -2\log 2$ and $\delta = \log 2$, so the inequality is an equality.

**Remark (The factor 2).** In the example $y = 1/2$, the sum $c + \delta = -\log 2$ is negative. So the factor $2$ cannot be removed. It appears because the Gram determinant is quadratic in the family: once through $\iota$ and once through $\bar\iota$. This is the square of the index in Section 2.

**Remark (The covolume only for the trivial twist).** The archimedean bound concerns the one number $\mathrm{Gram}(1)$, and the rational matrix $G$ exists only on $E_1$. The twist $\xi_\iota$ enters only at $\iota$, through the ratio $Z(1)/Z(\xi_\iota)$, which does not depend on the family (Section 4). This is why hypothesis 5 is about volumes and not about the family.

**Remark (Why a basis).** The hypothesis $\dim V = n + n'$ makes $y \sqcup z$ a basis, as the lemma on Gram determinants under a linear map needs. For fewer vectors, the ratio of the Gram determinants of two twists depends on the family. The auxiliary vectors $z$ are the cost, through the term $n'(b_{\mathrm{short}} + b_{\mathrm{denom}})$.

### How Theorem C uses the inequality

[Theorem C](/chapter/proof-of-theorem-c/) applies the theorem to the twisted lattice of [integral target forms](/chapter/integral-target-forms/).

**Theorem (Theorem C: integral forms are long).** Let $y_1, \dots, y_n$ be linearly independent target forms with $n \geq (1 - 4/b^2) d_T$. If $y$ has index at most $\delta$ and covolume at most $c$ in this twisted lattice, then
$$d_T\,(\mathrm{main} - 3 f a \log^4 b) \leq c + 2\delta.$$

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

The proof completes $y$ to a basis by auxiliary forms $z$, with $n' = d_T - n$. It applies the theorem with $b_{\mathrm{short}} = 2x_1^2 b^2$, $b_{\mathrm{denom}} = b$, and $b_{\mathrm{volume}} = d_T(b + f a \log^4 b - \mathrm{main})$. With $n'(2x_1^2b^2 + b) \leq d_T b$ and $b \leq f a \log^4 b$, the three extra terms sum to at most $d_T(3 f a \log^4 b - \mathrm{main})$. So the theorem gives $c + 2\delta \geq d_T(\mathrm{main} - 3 f a \log^4 b)$. Here $\log b$ is the number `D.logB` of the source.
