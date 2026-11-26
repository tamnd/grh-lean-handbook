---
title: Two bounds in one lattice
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/MainInequality.lean
decls:
  - New.Data.span_short_integralRamified_eq_top
  - New.Data.normalizedPoincare_mem_integralVectors
  - New.Data.indexLe_normalizedPoincare
  - New.TwistedLattice.covolumeLe_of_normSqAt_le
  - New.TwistedLattice.covolume_add_index_nonneg
  - New.Data.integral_forms_long
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Two bounds in one lattice

The proof compares two bounds for the covolume of one family $y_1, \dots, y_n$ of target forms. Theorem A bounds the covolume from above by the sizes of the forms, and bounds the index from above by their divisibility. Theorem C bounds $c + 2\delta$ from below, where $c$ and $\delta$ are any bounds for the covolume and the index. The comparison makes sense only if both theorems speak about the same integral vectors, the same norms and the same index. [Theorems A, B and C](/chapter/theorems-a-b-c/) states the three theorems together. This section states them in the target lattice.

### Theorem A in the lattice

The forms of Theorem A are images of the source forms under the normalized maps $s\mathfrak{p}$, for $s$ in the finite group $\mathsf{G}$ (`New.Data.normalizedPoincare`). [The normalized map](/chapter/theorems-a-b-c/#the-normalized-map-and-its-two-chosen-constants) defines them. A source form is *integral* if it is integral at every $\iota$ (`New.Data.integralRamified`).

**Theorem (Theorem A (a)).** The source is spanned by the integral source forms $\varphi$ such that
$$\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 \leq \exp\big(A_{\mathrm{main}} - m \cdot \mathrm{rem} + f a \log^4 b\big)$$
for every $s \in \mathsf{G}$ and every $\sigma \in \mathrm{Aut}(\mathbb{C})$. Here $A_{\mathrm{main}}$ is the main amount and $\mathrm{rem}$ is the total remainder of the data.

Lean: `New.Data.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean).

By the lemma on norms in the target lattice, the norm in Theorem A (a) is the squared norm of the form in the lattice. So Hadamard's inequality applies.

**Lemma (Hadamard's inequality in a twisted lattice).** If $\|y_i\|_\sigma^2 \leq e^h$ in the lattice for all $i \leq n$ and all $\sigma$, then the family $y$ has covolume at most $nh$.

Lean: `New.TwistedLattice.covolumeLe_of_normSqAt_le` (New/Reduction/Lattices/TwistedLattice.lean).

The integrality part of Theorem A goes through the lemma on integral target forms of Section 4.

**Lemma (Integrality of the images).** Let $\iota \mid \ell$ and $s \in \mathsf{G}$. Let $\varphi$ be a source form such that, for every twist $\vartheta$ with $\mathrm{Nm}\,Q$ prime to $\ell$ and every chain datum $\Psi$ of $\vartheta$, the upper chain $B_\vartheta \varphi$ has gauge at most $\ell^{\mathrm{err}_\ell - \mathrm{gain}_\ell}$ at $\iota$. Then $s\mathfrak{p}\,\varphi$ is an integral vector of the target lattice at $\iota$.

Lean: `New.Data.normalizedPoincare_mem_integralVectors` (New/Reduction/ShortAndEnough.lean).

*Proof.* By the lemma on integral target forms it suffices to show that $\Theta_\vartheta(s\mathfrak{p}\,\varphi)$ is integral at the place of $\iota$ for every $m$-fold twist $\vartheta$ with $\mathrm{Nm}\,Q$ prime to $\ell$. The seesaw identity gives a chain datum $\Psi$ with $\iota_\vartheta(z) = B_\vartheta\varphi$, where $z$ is the Poincaré image of $\varphi$. The gain factor $\ell^{-g_\ell}$, with $g_\ell \leq \mathrm{gain}_\ell - \mathrm{err}_\ell$, makes $B_\vartheta\varphi$ integral. The map $s\mathfrak{p}$ is this factor times $\#\mathsf{G}$ times the good part of a translate of $z$, which keeps integrality (`New.Data.goodProjTranslate_mem_integralForms`). $\square$

**Theorem (Theorem A (b)).** Let $\mathcal{T}$ be a finite set of elements of $\mathsf{G}$, and let $y_1, \dots, y_n$ be target forms such that each $y_i$ is $s\mathfrak{p}\,\varphi$ for some $s \in \mathcal{T}$ and some integral source form $\varphi$. Then $y$ has index at most
$$\#\mathcal{T} \cdot \dim(\mathrm{src}) \cdot 2 f a \log^3 b$$
in the target lattice, where $\mathrm{src}$ is the space of ramified source forms.

Lean: `New.Data.indexLe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

### Theorem C in the lattice

Theorem C is an instance of the lower bound for twisted lattices, applied to the target lattice.

**Theorem (The lattice inequality).** Let $L$ be a twisted lattice on $V$ with all maps $\Theta_\xi$ injective. Let $y_1, \dots, y_n, z_1, \dots, z_{n'}$ be a basis of $V$, and let $\xi_\iota$ be a twist allowed at the prime of $\iota$, for each $\iota$. Suppose that

- $y$ has covolume at most $c$ and index at most $\delta$;
- there is $\gamma(\xi) \neq 0$ for each twist such that $\gamma(\xi)\Theta_\xi z_i$ is integral at every $\iota \mid \ell$ for $\xi$ allowed at $\ell$;
- $\|z_i\|_\sigma^2 \leq \exp b_{\mathrm{short}}$ for every $i$ and every $\sigma$;
- the families $|\gamma(\xi_\iota)|^{-2}$ and $Z(1)/Z(\xi_\iota)$ have height at most $b_{\mathrm{denom}}$ and $b_{\mathrm{volume}}$.

Then $c + 2\delta + n'(b_{\mathrm{short}} + b_{\mathrm{denom}}) + b_{\mathrm{volume}} \geq 0$.

Lean: `New.TwistedLattice.covolume_add_index_nonneg` (New/Reduction/Lattices/TwistedLattice.lean).

[Twisted lattices](/chapter/twisted-lattices/#the-lattice-inequality) proves it. The proof writes the Gram determinant for the trivial twist as a product of three factors. Let $\Gamma(\xi)$ be the Gram determinant of the family $\Theta_\xi(y, z)$. By the identity of the volume, $\Gamma(\xi) = Z(\xi) \cdot \det\langle (y,z), (y,z)\rangle$ for every $\xi$. So
$$\Gamma(1) = \big(|\gamma(\xi_\iota)|^{2n'}\, \Gamma(\xi_\iota)\big) \cdot |\gamma(\xi_\iota)|^{-2n'} \cdot \frac{Z(1)}{Z(\xi_\iota)}.$$
The three factors have heights at most $2\delta$, $n' b_{\mathrm{denom}}$ and $b_{\mathrm{volume}}$. The covolume bounds the conjugates of $\Gamma(1)$, and the product formula closes the argument.

**Theorem (Theorem C).** Let $y_1, \dots, y_n$ be linearly independent target forms with $n \geq (1 - 4/b^2) d_T$. If $y$ has index at most $\delta$ and covolume at most $c$ in the target lattice, then
$$d_T \big(A_{\mathrm{main}} - 3 f a \log^4 b\big) \leq c + 2\delta.$$

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

*Proof.* Take the family $\theta$ of the theorem on single lifts at good twists in Section 5, and put $\xi_\iota = \theta(\iota)$. It is allowed at the prime of $\iota$, since it has small ratios. Complete $y$ to a basis of $T$ by auxiliary forms $z_1, \dots, z_{n'}$ (`New.Data.IsAuxiliaryForm`). These are integral up to a scalar $\gamma(\vartheta)$ and satisfy $\|z_i\|_\sigma^2 \leq \exp(2 x_1^2 b^2)$. The family $|\gamma(\theta(\iota))|^{-2}$ has height at most $b$. By Section 5 the maps are injective, and $Z(1)/Z(\theta(\iota))$ has height at most $d_T(b + f a \log^4 b - A_{\mathrm{main}})$. The lattice inequality gives
$$0 \leq c + 2\delta + n'(2x_1^2 b^2 + b) + d_T(b + f a\log^4 b - A_{\mathrm{main}}).$$
Since $n' \leq 4 d_T / b^2$, the completion cost $n'(2x_1^2b^2 + b)$ is at most $d_T b$ (`New.Data.mul_completion_cost_le`). The two terms $d_T b$ are at most $2 d_T f a \log^4 b$. Rearrange. $\square$

### What each part of the lattice does

Four points explain why one lattice serves both theorems.

First, the integral vectors are tested through all twists allowed at $\ell$. Theorem A can prove this strong condition, since the seesaw identity and the divisibility of the upper chain hold for every twist. Theorem C uses one twist $\xi_\iota$ for each $\iota$, and this twist depends on $\iota$.

Second, the index matrix does not depend on the twist. The index at $\iota$ is a matrix over $\mathcal{O}_\iota$ that carries $y$ into the integral vectors of $T$, which is an intersection over the allowed twists. So one matrix serves for the twist $\xi_\iota$ in the proof of the lattice inequality, and for the trivial twist in Theorem A (b).

Third, the norms are the same. Theorem A bounds the class sum $\|\Theta_1 y\|_\sigma^2$, a statement about algebraic forms. Theorem C uses the norm of the lattice, a statement about rational coordinates. The lemma on norms in the target lattice identifies them, and it needs the trivial stabilisers.

Fourth, the volume carries the main amount. If $\xi_\iota = 1$ for every $\iota$, then $Z(1)/Z(\xi_\iota) = 1$, and the lattice inequality holds with $b_{\mathrm{volume}} = 0$. The bound of Theorem C would then have no term $d_T A_{\mathrm{main}}$, and the comparison with Theorem A (a) would give nothing. The twists make $Z(1)/Z(\xi_\iota)$ small in height by $d_T A_{\mathrm{main}}$, and the lattice inequality turns this into the lower bound.

### The comparison

[The main inequality](/chapter/main-inequality/) puts the two bounds together. With $n$ forms from Theorem A (a), the covolume is at most $c = n(A_{\mathrm{main}} - m\,\mathrm{rem} + f a \log^4 b)$ by Hadamard's inequality. Theorem B ([enough forms](/chapter/theorems-a-b-c/#theorem-b-enough-forms)) gives a set $\mathcal{T}$ with $n \geq (1 - 4/b^2) d_T$ independent forms and $\#\mathcal{T} \cdot \dim(\mathrm{src}) \leq 5 d_T \log(1 + 2b^2)$. So Theorem A (b) gives $\delta \leq d_T \cdot 10 \log(1 + 2b^2) f a \log^3 b$. Theorem C gives
$$d_T(A_{\mathrm{main}} - 3 f a \log^4 b) \leq n(A_{\mathrm{main}} - m\,\mathrm{rem} + f a\log^4 b) + 2\delta.$$
Since $n \leq d_T$ and $A_{\mathrm{main}} + f a \log^4 b \geq 0$, the term $n(A_{\mathrm{main}} + f a \log^4 b)$ is at most $d_T(A_{\mathrm{main}} + f a \log^4 b)$. So the terms $d_T A_{\mathrm{main}}$ cancel, and
$$n \cdot m\,\mathrm{rem} \leq d_T \big(4 f a \log^4 b + 20 \log(1+2b^2) f a \log^3 b\big).$$
With $d_T \leq 2n$ the source concludes $m\,\mathrm{rem} \leq f a \log^5 b$. The amount $A_{\mathrm{main}}$ appears on both sides with the same coefficient $d_T$, because both bounds are taken in one lattice, with one norm and one volume.
