---
title: Twisted lattices, index and covolume
lean:
  - New/Reduction/Lattices/TwistedLattice.lean
decls:
  - New.PrimePadicIso.conj
  - New.PrimePadicIso.integers
  - New.PrimePadicIso.inv_pow_le_norm_of_dvd
  - New.PrimePadicIso.Carries
  - New.PrimePadicIso.Carries.fromBlocks
  - New.TwistedLattice
  - New.TwistedLattice.integralVectors
  - New.TwistedLattice.mem_integralVectors
  - New.TwistedLattice.IndexLe
  - New.TwistedLattice.IndexLe.mono
  - New.TwistedLattice.IndexLe.of_comp_equiv
  - New.TwistedLattice.IndexLe.sumElim
  - New.TwistedLattice.indexLe_card_mul
  - New.TwistedLattice.conjCoord
  - New.TwistedLattice.normSqAt
  - New.TwistedLattice.CovolumeLe
  - New.conjAut
  - New.TwistedLattice.map_inner_lift_one
  - New.TwistedLattice.CovolumeLe.norm_map_det_gram_le
  - New.TwistedLattice.covolumeLe_of_normSqAt_le
  - New.TwistedLattice.CovolumeLe.sumElim
  - New.TwistedLattice.volume
  - New.TwistedLattice.volume_eq_det_adjoint_comp
  - New.TwistedLattice.volume_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Twisted lattices, index and covolume

In Section 2 the lower bound came from one integral lattice. In the source the integral structure is given one prime at a time, as a module over a valuation ring of $\mathbb{C}$. And the space carries several maps $\Theta_\xi$, one for each *twist* $\xi$, each with its own integral structure.

### The valuation ring of an isomorphism

**Definition (The conjugate isomorphism and the valuation ring).** Let $\iota \mid \ell$. The *conjugate* $\bar\iota \mid \ell$ is the isomorphism $\bar\iota(z) = \iota(\bar z)$. The ring $\mathcal{O}_\iota$ is the valuation ring $\{x \in \mathbb{C} : \|\iota x\| \leq 1\}$ of $\mathbb{C}$.

Lean: `New.PrimePadicIso.conj` (New/Reduction/Lattices/TwistedLattice.lean).

Lean: `New.PrimePadicIso.integers` (New/Reduction/Lattices/TwistedLattice.lean).

The ring $\mathcal{O}_\iota$ is not noetherian, and its value group is $\ell^{\mathbb{Q}}$. Complex conjugation need not keep the absolute value $x \mapsto \|\iota x\|$, so $\mathcal{O}_{\bar\iota}$ can be a different ring from $\mathcal{O}_\iota$.

**Lemma (Divisors of a power of the prime).** Let $x \in \mathcal{O}_\iota$ divide $\ell^j$ in $\mathcal{O}_\iota$. Then $\|\iota x\| \geq \ell^{-j}$.

Lean: `New.PrimePadicIso.inv_pow_le_norm_of_dvd` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* If $\ell^j = xw$ with $w \in \mathcal{O}_\iota$, then $\ell^{-j} = \|\iota x\| \|\iota w\| \leq \|\iota x\|$. $\square$

**Definition (A matrix carries a family).** Let $W$ be an $\mathcal{O}_\iota$-module, $M \subset W$ a submodule, $y = (y_k)_{k \in S}$ a finite family in $W$, and $a \in \mathbb{R}$. A square matrix $u$ over $\mathcal{O}_\iota$ indexed by $S$ *carries $y$ into $M$ with loss $a$* if $\|\iota \det u\| \geq \ell^{-a}$ and $\sum_k u_{ik} y_k \in M$ for every $i \in S$.

Lean: `New.PrimePadicIso.Carries` (New/Reduction/Lattices/TwistedLattice.lean).

The loss $a$ is an upper bound for the valuation of $\det u$, normalized so that $\ell$ has valuation $1$.

**Lemma (Block matrices).** If $u$ carries $y$ into $M$ with loss $a$, and $u'$ carries $y'$ into $M$ with loss $a'$, then the block diagonal matrix with blocks $u$ and $u'$ carries the joined family $y \sqcup y'$ into $M$ with loss $a + a'$.

Lean: `New.PrimePadicIso.Carries.fromBlocks` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* The determinant of the block matrix is $\det u \det u'$. $\square$

### Twisted lattices

**Definition (Twisted lattice).** Let $V$ be a complex vector space and $T$ a set with a distinguished element $1$, the *trivial twist*. A *twisted lattice* on $V$ with twists $T$ consists of:

1. for each $\xi \in T$, a complex inner product space $E_\xi$ and a linear map $\Theta_\xi\colon V \to E_\xi$;
2. for each prime $\ell$, a set of twists that are *allowed at $\ell$*;
3. for each $\xi \in T$ and each $\iota$, an $\mathcal{O}_\iota$-submodule $\Lambda_{\xi,\iota} \subset E_\xi$, the vectors *integral at $\iota$*, such that $\|\iota \langle \varphi, \varphi' \rangle\| \leq 1$ for $\varphi \in \Lambda_{\xi,\bar\iota}$ and $\varphi' \in \Lambda_{\xi,\iota}$, whenever $\xi$ is allowed at the prime $\ell$ of $\iota$;
4. a finite set $C$ and a linear map $\mathrm{coord}\colon E_1 \to \mathbb{C}^C$, the *coordinates*, and a matrix $G \in \mathbb{Q}^{C \times C}$, positive definite as a complex matrix, such that $\langle \varphi, \varphi' \rangle = \mathrm{coord}(\varphi)^* G \, \mathrm{coord}(\varphi')$ for all $\varphi, \varphi' \in E_1$.

Lean: `New.TwistedLattice` (New/Reduction/Lattices/TwistedLattice.lean).

The inner product is conjugate linear in the first variable. So the pair $\bar\iota$, $\iota$ in condition 3 is the natural one, as the next example shows.

**Example (The standard twisted lattice).** Let $V = E_1 = \mathbb{C}^n$ with the standard inner product, $T = \{1\}$, and $\Theta_1$ the identity. Let $1$ be allowed at every prime, let $\Lambda_{1,\iota} = \mathcal{O}_\iota^n$, let $C = \{1, \dots, n\}$ with the identity coordinates, and let $G = 1$. For $\varphi \in \mathcal{O}_{\bar\iota}^n$ and $\varphi' \in \mathcal{O}_\iota^n$, each term $\iota(\bar\varphi_k \varphi'_k) = \bar\iota(\varphi_k)\,\iota(\varphi'_k)$ has norm at most $1$. By the ultrametric inequality, so has their sum. So condition 3 holds. Section 6 computes the inequality of the chapter for $n = 1$.

The data of item 4 exist only for the trivial twist. The rational matrix $G$ gives meaning to $\sigma$ applied to an inner product of $E_1$. In Theorem C, $V$ is the space of target forms and $E_\xi$ is a space of forms for the twist $\xi$. The allowed twists at $\ell$ are those whose norm is prime to $\ell$: see [the lattice of integral target forms](/chapter/integral-target-forms/), where the source builds this twisted lattice as `New.Data.targetLattice`.

**Remark (Formalization).** The structure carries the normed group and the inner product space of $E_\xi$ as fields, and the source declares them as instances. So no other instance on $E_\xi$ can enter. The structure has no inner product on $V$ and no finiteness condition. The source assumes them only from the volume on.

**Definition (Integral vectors of V).** For $\iota \mid \ell$, the vectors of $V$ *integral at $\iota$* are those $y \in V$ with $\Theta_\xi y \in \Lambda_{\xi,\iota}$ for every twist $\xi$ allowed at $\ell$. They form an $\mathcal{O}_\iota$-submodule of $V$.

Lean: `New.TwistedLattice.integralVectors` (New/Reduction/Lattices/TwistedLattice.lean).

Lean: `New.TwistedLattice.mem_integralVectors` (New/Reduction/Lattices/TwistedLattice.lean).

### The index

**Definition (Index at most δ).** Let $y = (y_k)_{k \in S}$ be a finite family in $V$, and let $\delta \in \mathbb{R}$. The family has *index at most $\delta$* if there are real numbers $e(\ell) \geq 0$, for $\ell \in \mathbb{N}$, such that $\sum_{\ell \in U} e(\ell) \log \ell \leq \delta$ for every finite set $U$ of primes, and for every $\iota \mid \ell$ some square matrix over $\mathcal{O}_\iota$ carries $y$ into the vectors of $V$ integral at $\iota$ with loss $e(\ell)$.

Lean: `New.TwistedLattice.IndexLe` (New/Reduction/Lattices/TwistedLattice.lean).

In the model of Section 2, a family $v$ of $n$ vectors with $Dv \subset \mathcal{L}$ has index at most $n \log D$, with the matrix $D \cdot 1$ at each $\iota$.

**Example (Rank one).** In the standard twisted lattice with $n = 1$, let $y = 1/2$. At $\iota \mid 2$ the $1 \times 1$ matrix $(2)$ carries $y$ into $\mathcal{O}_\iota$, and $\|\iota 2\| = 2^{-1}$. At $\iota \mid \ell$ with $\ell$ odd, $y$ is already integral. So $y$ has index at most $\log 2$, with $\delta_2 = 1$ and $e(\ell) = 0$ for $\ell \neq 2$. No smaller bound holds: for any matrix $(u)$ with $u/2 \in \mathcal{O}_\iota$ we have $\|\iota u\| \leq 1/2$.

The matrix at $\iota$ does not depend on the twist. It must work for all twists allowed at $\ell$ at once.

**Lemma (The calculus of the index).** Let $y$ and $y'$ be finite families in $V$.

1. If $y$ has index at most $\delta$ and $\delta \leq \delta'$, then $y$ has index at most $\delta'$.
2. If $f$ is a bijection and $y \circ f$ has index at most $\delta$, then $y$ has index at most $\delta$.
3. If $y$ and $y'$ have index at most $\delta$ and $\delta'$, then the joined family $y \sqcup y'$ has index at most $\delta + \delta'$.
4. Let $J$ be a finite set, and for $s \in J$ let $A_s \subset V$ be a set such that every finite family in $A_s$ has index at most $\delta$. If every member of $y$ lies in some $A_s$, $s \in J$, then $y$ has index at most $\#J \cdot \delta$.

Lean: `New.TwistedLattice.IndexLe.mono` (New/Reduction/Lattices/TwistedLattice.lean).

Lean: `New.TwistedLattice.IndexLe.of_comp_equiv` (New/Reduction/Lattices/TwistedLattice.lean).

Lean: `New.TwistedLattice.IndexLe.sumElim` (New/Reduction/Lattices/TwistedLattice.lean).

Lean: `New.TwistedLattice.indexLe_card_mul` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Part 1 keeps the data. Part 2 permutes the rows and columns of each matrix. Part 3 adds the numbers $e(\ell)$ and uses block matrices. Part 4 is by induction on $J$: split $y$ into the members in $A_s$ for one $s$ and the others, and apply parts 2 and 3. For $J = \emptyset$ the family is empty, and the empty matrix carries it with loss $0$. $\square$

### The covolume

The covolume refers only to the trivial twist, and it is taken at every automorphism of $\mathbb{C}$.

**Definition (Conjugate coordinates and conjugate lengths).** Let $\sigma$ be an automorphism of $\mathbb{C}$ and $y \in V$. The *conjugate coordinates* $\sigma\Theta_1 y \in \mathbb{C}^C$ are the coordinates of $\Theta_1 y$ with $\sigma$ applied to each one. The *conjugate squared length* is $\|\Theta_1 y\|_\sigma^2 = \operatorname{Re}\big((\sigma\Theta_1 y)^* G \,(\sigma\Theta_1 y)\big)$.

Lean: `New.TwistedLattice.conjCoord` (New/Reduction/Lattices/TwistedLattice.lean).

Lean: `New.TwistedLattice.normSqAt` (New/Reduction/Lattices/TwistedLattice.lean).

Since $G$ is positive definite, the number inside the real part is real and $\geq 0$.

**Definition (Covolume at most c).** A finite family $y = (y_k)_{k \in S}$ in $V$ has *covolume at most $c$* if
$$\big|\det \mathrm{formGram}\big(G, (\sigma\Theta_1 y_k)_{k \in S}\big)\big| \leq e^c$$
for every automorphism $\sigma$ of $\mathbb{C}$.

Lean: `New.TwistedLattice.CovolumeLe` (New/Reduction/Lattices/TwistedLattice.lean).

For $\sigma$ the identity, the determinant is the Gram determinant of the vectors $\Theta_1 y_k$, the squared covolume of Section 2.

To apply $\sigma$ to an inner product, the source needs one more automorphism. Let $\sigma'$ be the automorphism $\sigma'(z) = \overline{\sigma(\bar z)}$.

Lean: `New.conjAut` (New/Reduction/Lattices/TwistedLattice.lean).

**Lemma (Conjugates of inner products).** For an automorphism $\sigma$ of $\mathbb{C}$ and $v, w \in V$,
$$\sigma \langle \Theta_1 v, \Theta_1 w \rangle = (\sigma'\Theta_1 v)^* G \,(\sigma \Theta_1 w).$$

Lean: `New.TwistedLattice.map_inner_lift_one` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Expand $\langle \Theta_1 v, \Theta_1 w\rangle = \sum_{a,b} \overline{v_a} G_{ab} w_b$ in coordinates. The automorphism $\sigma$ fixes $G_{ab} \in \mathbb{Q}$, and $\sigma(\bar x) = \overline{\sigma'(x)}$. $\square$

An automorphism of $\mathbb{C}$ other than the identity and complex conjugation does not commute with complex conjugation. So in general $\sigma' \neq \sigma$, and $\sigma\langle \Theta_1 v, \Theta_1 v\rangle$ need not be real. The next theorem handles this with the Cauchy-Schwarz inequality of Section 2.

**Theorem (Conjugates of the Gram determinant).** Let $y$ have covolume at most $c$. Then for every automorphism $\sigma$ of $\mathbb{C}$,
$$|\sigma \det \mathrm{Gram}(\Theta_1 y_k)_{k \in S}| \leq e^c.$$

Lean: `New.TwistedLattice.CovolumeLe.norm_map_det_gram_le` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* By the lemma, $\sigma \det \mathrm{Gram}(\Theta_1 y)$ is the determinant of the matrix $\big((\sigma'\Theta_1 y_i)^* G\, (\sigma\Theta_1 y_k)\big)_{i,k}$. By [the lemma](/decl/New.norm_det_pairing_sq_le/) of Section 2, its square is at most the product of the two determinants $|\det \mathrm{formGram}(G, \sigma'\Theta_1 y)|$ and $|\det \mathrm{formGram}(G, \sigma\Theta_1 y)|$. Each is at most $e^c$, by the hypothesis at $\sigma'$ and at $\sigma$. $\square$

**Theorem (Hadamard's inequality for a family).** Let $z_1, \dots, z_n \in V$ and $h \in \mathbb{R}$ with $\|\Theta_1 z_i\|_\sigma^2 \leq e^h$ for all $i$ and all $\sigma$. Then $z$ has covolume at most $nh$.

Lean: `New.TwistedLattice.covolumeLe_of_normSqAt_le` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* Apply [the corollary](/decl/New.norm_det_formGram_le/) of Section 2 at each $\sigma$. $\square$

**Theorem (Adjoining short vectors).** Let $y$ have covolume at most $c$. Let $z_1, \dots, z_n \in V$ and $h \in \mathbb{R}$ with $\|\Theta_1 z_i\|_\sigma^2 \leq e^h$ for all $i$ and all $\sigma$. Then the joined family $y \sqcup z$ has covolume at most $c + nh$.

Lean: `New.TwistedLattice.CovolumeLe.sumElim` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* At each $\sigma$, the Gram matrix of $y \sqcup z$ has the Gram matrices of $y$ and of $z$ as its diagonal blocks. Apply [Fischer's inequality](/decl/New.fischer_det_inequality/), the hypothesis on $y$, and the previous theorem. $\square$

[The main inequality](/chapter/main-inequality/) applies Hadamard's inequality to the short target forms of Theorem A, in `New.star_inequality`.

**Remark (Formalization).** The textbook covolume of a family is a single number (Section 2). The source's covolume is a bound at every automorphism of $\mathbb{C}$, applied to coordinates. The automorphisms other than the identity and complex conjugation are not continuous, so they do not act on $E_1$ in a natural way. The rational coordinates give the action. The product formula needs the bound at every $\sigma$.

### The volume of a twist

From here on $V$ is a complex inner product space of finite dimension.

**Definition (Volume of a twist).** The *volume* of the twist $\xi$ is $Z(\xi) = \operatorname{normDet}(\Theta_\xi)^2$, where $\operatorname{normDet}$ is as in Section 2. It is the Gram determinant of the images under $\Theta_\xi$ of an orthonormal basis of $V$.

Lean: `New.TwistedLattice.volume` (New/Reduction/Lattices/TwistedLattice.lean).

**Lemma (The volume as a determinant).** If $E_\xi$ has finite dimension, then $Z(\xi) = \det(\Theta_\xi^* \Theta_\xi)$, the determinant of an endomorphism of $V$. If $\Theta_\xi$ is injective, then $Z(\xi) \neq 0$.

Lean: `New.TwistedLattice.volume_eq_det_adjoint_comp` (New/Reduction/Lattices/TwistedLattice.lean).

Lean: `New.TwistedLattice.volume_ne_zero` (New/Reduction/Lattices/TwistedLattice.lean).

*Proof.* The first statement is the definition of $\operatorname{normDet}$ (Mathlib's `LinearMap.normDet`) for a map between spaces of finite dimension. For the second, $\operatorname{normDet}(\Theta_\xi) = 0$ only if $\Theta_\xi$ has a nonzero kernel. $\square$

By [the lemma](/decl/New.det_gram_comp/) on Gram determinants of Section 2, for a basis $x$ of $V$,
$$\det \mathrm{Gram}(\Theta_\xi x) = Z(\xi) \det \mathrm{Gram}(x).$$
So the ratio $\det \mathrm{Gram}(\Theta_1 x) / \det \mathrm{Gram}(\Theta_\xi x) = Z(1)/Z(\xi)$ does not depend on the basis $x$. Section 6 uses this ratio to pass from the trivial twist to the twist $\xi_\iota$ at each $\iota$.
