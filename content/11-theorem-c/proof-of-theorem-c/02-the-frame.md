---
title: The frame
lean:
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/Lattices/Heights.lean
  - New/Reduction/IntegralTargetForms.lean
  - Lib/General/LinearAlgebra/GramDeterminant.lean
decls:
  - New.HeightLe
  - New.TwistedLattice.IndexLe
  - New.TwistedLattice.CovolumeLe
  - New.TwistedLattice.CovolumeLe.sumElim
  - New.TwistedLattice.heightLe_pow_mul_det_gram
  - New.TwistedLattice.covolume_add_index_nonneg
  - New.Data.targetLattice
  - New.Data.normSqAt_targetLattice
  - New.Data.volume_targetLattice
  - New.Data.injective_lift_targetLattice
  - New.exists_extend_basis_of_span_eq_top
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The frame

The proof of Theorem C applies one general inequality for twisted lattices. This section states it as Lean states it, with the definitions in its hypotheses, and recalls its proof. The chapter [twisted lattices](/chapter/twisted-lattices/#the-lattice-inequality) of Volume 1 gives the proof in full. The section then gives the four facts about the target lattice that the frame needs, and the lemma that completes a family to a basis.

### Heights, index and covolume

**Definition (Height at most c).** A family $y = (y_\iota)$ of complex numbers, one for each $\iota$, has *height at most $c$* if there are $H \in \mathbb{C}$, $\alpha \in \mathbb{R}$ and reals $h_\ell \geq 0$, one for each $\ell \in \mathbb{N}$, such that $H \neq 0$, $|\sigma H| \leq e^\alpha$ for every automorphism $\sigma$ of $\mathbb{C}$, $\|\iota(H y_\iota)\| \leq \ell^{h_\ell}$ for every $\iota$ with prime $\ell$, and $\alpha + \sum_{\ell \in T} h_\ell\log\ell \leq c$ for every finite set $T$ of primes.

Lean: `New.HeightLe` (New/Reduction/Lattices/Heights.lean).

The multiplier $H$ is one number for all $\iota$. So a height bound for a family adds the losses at all primes in one sum. This is the reason that one twist for each $\iota$ is enough, whatever the twists are.

**Definition (Index at most δ).** Let $L$ be a twisted lattice on $V$ and $y : S \to V$ a finite family. Then $y$ has *index at most $\delta$* if there are reals $e_\ell \geq 0$, one for each $\ell \in \mathbb{N}$, with $\sum_{\ell \in U} e_\ell\log\ell \leq \delta$ for every finite set $U$ of primes, such that for every $\iota$ some matrix $u$ over the valuation ring $\mathcal{O}_\iota$, indexed by $S$, carries $y$ into the vectors integral at $\iota$ with loss $e_\ell$, where $\ell$ is the prime of $\iota$.

Lean: `New.TwistedLattice.IndexLe` (New/Reduction/Lattices/TwistedLattice.lean).

Here "carries with loss $a$" means that the vectors $\sum_k u_{ik}y_k$ are integral at $\iota$ and $\ell^{-a} \leq \|\iota(\det u)\|$. The matrix depends on $\iota$, but not on the twist.

**Definition (Covolume at most c).** The family $y$ has *covolume at most $c$* if for every automorphism $\sigma$ of $\mathbb{C}$ the determinant of the products $\langle\sigma\Theta_1 y_i, \sigma\Theta_1 y_k\rangle$, taken with the rational Gram matrix of $L$ on the coordinate vectors, has absolute value at most $e^c$.

Lean: `New.TwistedLattice.CovolumeLe` (New/Reduction/Lattices/TwistedLattice.lean).

For one vector $z$ the number $\|\Theta_1 z\|_\sigma^2 = \langle\sigma\Theta_1 z, \sigma\Theta_1 z\rangle$ is `L.normSqAt z σ`.

**Lemma (Adjoining short vectors).** If $y$ has covolume at most $c$ and $\|\Theta_1 z_i\|_\sigma^2 \leq e^h$ for $i = 1, \dots, n'$ and every $\sigma$, then the family $y$ together with $z_1, \dots, z_{n'}$ has covolume at most $c + n'h$.

Lean: `New.TwistedLattice.CovolumeLe.sumElim` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Fix $\sigma$ and let $M$ be the Gram matrix of the union at $\sigma$. It is positive semidefinite, because the rational Gram matrix is positive definite. Fischer's inequality gives $|\det M| \leq |\det M_{11}|\cdot|\det M_{22}|$ for the two diagonal blocks. The first block is the matrix of $y$, so $|\det M_{11}| \leq e^c$. Hadamard's inequality gives $|\det M_{22}| \leq \prod_i\|\Theta_1 z_i\|_\sigma^2 \leq e^{n'h}$. $\square$

### The local bound

**Lemma (The local bound).** Let $y$ have index at most $\delta$, let $\xi_\iota = \theta(\iota)$ be allowed at the prime of $\iota$, and let the vectors $\gamma_\iota\,\Theta_{\xi_\iota}z_i$ be integral at $\iota$ and at $\bar\iota$, where $\bar\iota(w) = \iota(\bar w)$. Let $\operatorname{Gram}(\xi)$ be the Gram determinant of $\Theta_\xi y_1, \dots, \Theta_\xi y_n, \Theta_\xi z_1, \dots, \Theta_\xi z_{n'}$. Then the family $\iota \mapsto |\gamma_\iota|^{2n'}\operatorname{Gram}(\xi_\iota)$ has height at most $2\delta$.

Lean: `New.TwistedLattice.heightLe_pow_mul_det_gram` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Take the reals $e_\ell$ of the index, and take $H = 1$, $\alpha = 0$ and the losses $2e_\ell\log\ell$ at the primes. Their sum over a finite set of primes is at most $2\delta$. At $\iota$, take the matrix $u$ of the index at $\iota$ and the matrix $u'$ at $\bar\iota$. Both have the same prime, so both have loss $e_\ell$. The vectors $\sum_k u_{ik}\Theta_\xi y_k$ and $\gamma_\iota\Theta_\xi z_i$ are integral at $\iota$. The same holds at $\bar\iota$ with $u'$. Products of vectors integral at $\bar\iota$ with vectors integral at $\iota$ are integral at $\iota$, because $\xi_\iota$ is allowed. So $\iota$ of the determinant of the mixed Gram matrix has absolute value at most $1$. That determinant is $\overline{\det u'}\cdot\det u\cdot|\gamma_\iota|^{2n'}\operatorname{Gram}(\xi_\iota)$, up to the conjugation in $\iota$. The two determinants have absolute value at least $\ell^{-e_\ell}$ at $\iota$. So $\|\iota(|\gamma_\iota|^{2n'}\operatorname{Gram}(\xi_\iota))\| \leq \ell^{2e_\ell} = \exp(2e_\ell\log\ell)$. $\square$

### The lattice inequality

**Theorem (A twist for each prime).** Let $L$ be a twisted lattice on $V$ whose maps $\Theta_\xi$ are all injective. Let $y_1, \dots, y_n$ and $z_1, \dots, z_{n'}$ be vectors such that the family $(y, z)$ is linearly independent and $\dim V = n + n'$. Let $\theta(\iota)$ be a twist allowed at the prime of $\iota$, for every $\iota$. Let $c$, $\delta$, $b_{\mathrm{volume}}$, $b_{\mathrm{short}}$, $b_{\mathrm{denom}}$ be reals, and let $\gamma(\xi) \in \mathbb{C}$ for every twist $\xi$. Suppose that:

1. $y$ has covolume at most $c$ and index at most $\delta$;
2. $\gamma(\xi) \neq 0$ for every twist $\xi$;
3. $\gamma(\xi)\,\Theta_\xi z_i$ is in the lattice of $\xi$ at $\iota$, for every $i$, every $\iota$ and every $\xi$ allowed at the prime of $\iota$;
4. $\|\Theta_1 z_i\|_\sigma^2 \leq \exp b_{\mathrm{short}}$ for every $i$ and every automorphism $\sigma$ of $\mathbb{C}$;
5. the family $\iota \mapsto (|\gamma(\theta(\iota))|^2)^{-1}$ has height at most $b_{\mathrm{denom}}$;
6. the family $\iota \mapsto \mathrm{vol}(1)/\mathrm{vol}(\theta(\iota))$ has height at most $b_{\mathrm{volume}}$, where $\mathrm{vol}(\xi)$, the square of the norm determinant of $\Theta_\xi$, is the volume of $L$ at $\xi$.

Then

$$0 \leq c + 2\delta + n'\,(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}}.$$

Lean: `New.TwistedLattice.covolume_add_index_nonneg` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Let $\operatorname{Gram}(\xi)$ be the Gram determinant of $\Theta_\xi\circ(y, z)$. As $(y, z)$ is a basis, $\operatorname{Gram}(\xi) = \mathrm{vol}(\xi)\cdot\operatorname{Gram}_V$, where $\operatorname{Gram}_V$ is the Gram determinant of $(y, z)$ in $V$ (`New.det_gram_comp`). The lift $\Theta_{\theta(\iota)}$ is injective, so $\mathrm{vol}(\theta(\iota)) \neq 0$. With $\gamma(\theta(\iota)) \neq 0$ this gives, for every $\iota$,

$$\operatorname{Gram}(1) = |\gamma(\theta(\iota))|^{2n'}\operatorname{Gram}(\theta(\iota))\cdot\bigl(|\gamma(\theta(\iota))|^2\bigr)^{-n'}\cdot\frac{\mathrm{vol}(1)}{\mathrm{vol}(\theta(\iota))}.$$

The first factor has height at most $2\delta$ by the local bound. Hypothesis 3 gives the integrality at $\iota$ and at $\bar\iota$, since $\bar\iota$ has the same prime. The second factor has height at most $n'b_{\mathrm{denom}}$, and the third at most $b_{\mathrm{volume}}$. So the constant family $\operatorname{Gram}(1)$ has height at most $2\delta + n'b_{\mathrm{denom}} + b_{\mathrm{volume}}$. It is not $0$, because $\Theta_1$ is injective and $(y, z)$ is linearly independent. By the lemma on adjoining short vectors, $(y, z)$ has covolume at most $c + n'b_{\mathrm{short}}$. So $|\sigma\operatorname{Gram}(1)| \leq \exp(c + n'b_{\mathrm{short}})$ for every $\sigma$ (`New.TwistedLattice.CovolumeLe.norm_map_det_gram_le`). The product formula `New.HeightLe.neg_le_of_norm_map_le` gives $-(2\delta + n'b_{\mathrm{denom}} + b_{\mathrm{volume}}) \leq c + n'b_{\mathrm{short}}$. This is the claim. $\square$

**Remark (Formalization).** The theorem does not assume $c$, $\delta$ or the three bounds to be nonnegative. The number $b_{\mathrm{volume}}$ is negative in the application: it is about $-d\cdot\mathrm{mainAmount}$. This is the point of the theorem. The scalar $\gamma$ is a function on all twists, and hypothesis 3 asks for every allowed twist, not only for the twists $\theta(\iota)$.

### The target lattice

**Definition (The target lattice).** The target lattice is the twisted lattice on the target forms with these data. The twists are the $m$-fold twists $\vartheta$. The map at $\vartheta$ is the chain of lifts $\Theta_\vartheta = D.\Theta\,\vartheta$. The lattice at $\iota$ is the module of forms integral at the place of $\iota$, for every $\vartheta$. The twist $\vartheta$ is allowed at $\ell$ if $\ell$ is prime to $\mathrm{Nm}\,Q(\vartheta) = \vartheta.\mathtt{normQ}$. The coordinates for the trivial twist are the values at representatives of the classes, in the standard basis of the Weyl module.

Lean: `New.Data.targetLattice` (New/Reduction/IntegralTargetForms.lean).

The chapter [integral target forms](/chapter/integral-target-forms/#the-target-lattice) proves that these data form a twisted lattice. The proof of Theorem C uses three facts about it.

**Lemma (The norm in the target lattice).** For every target form $y$ and every $\sigma$, the number $\|\Theta_1 y\|_\sigma^2$ of the target lattice is the number $(D.\Theta\,1\,y).\mathtt{normSqAt}\,\sigma$ of the forms on $Y_m$.

Lean: `New.Data.normSqAt_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* The second number is a sum over the classes, with the term of a class divided by the order of its stabiliser. The stabilisers are trivial at the last residue level. So the two sums agree. $\square$

**Lemma (The volume is the chain determinant).** For every $m$-fold twist $\vartheta$, the volume of the target lattice at $\vartheta$ is the chain determinant $Z(\vartheta) = \det(\Theta_\vartheta^*\Theta_\vartheta)$.

Lean: `New.Data.volume_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* The volume at $\vartheta$ is the square of the norm determinant of $\Theta_\vartheta$, and the chain determinant is defined as the same number. So the two sides agree by definition. $\square$

**Lemma (The lifts are injective).** For every $m$-fold twist $\vartheta$, the map $\Theta_\vartheta$ of the target lattice is injective.

Lean: `New.Data.injective_lift_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* The map is the chain of lifts at the level of $\vartheta$, restricted to the target. The chain is injective by `New.Data.lowerChainAtLevel_injective` ([the chain determinant](/chapter/chain-determinant/)), and the inclusion of the target is injective. $\square$

### Completion to a basis

**Lemma (Completion to a basis).** Let $V$ be a finite dimensional complex space, $S \subseteq V$ a set that spans $V$, and $y_1, \dots, y_n$ linearly independent. Then there are $n' \in \mathbb{N}$ and $z_1, \dots, z_{n'} \in S$ such that the family $(y, z)$ is linearly independent and $\dim V = n + n'$.

Lean: `New.exists_extend_basis_of_span_eq_top` (Lib/General/LinearAlgebra/GramDeterminant.lean).

*Proof.* Let $Y$ be the span of $y$. The images of $S$ span $V/Y$, so some of them form a basis $w$ of $V/Y$. Lift each $w_i$ to some $z_i \in S$. Then $(y, z)$ is linearly independent, and $n' = \dim V/Y = \dim V - n$. $\square$

The lemma chooses the $z_i$. Theorem C does not depend on the choice: it uses only $z_i \in S$, the independence and the count $n + n' = d$.
