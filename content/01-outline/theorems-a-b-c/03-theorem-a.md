---
title: Theorem A, short forms of small index
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/UpperBound/Size/ShortColumns.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
decls:
  - New.Data.span_short_integralRamified_eq_top
  - New.Data.indexLe_normalizedPoincare
  - New.Data.span_isShort_ramifiedSourceForms_eq_top
  - New.Data.weylNormSq_compositeLift_le
  - New.Data.normSqAt_goodProjTranslate_le
  - New.Data.normalizedPoincare_mem_integralVectors
  - New.Data.indexLe_of_mem_image_normalizedPoincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theorem A, short forms of small index

Theorem A is the upper bound of the argument. Part (a) says that the source is spanned by integral forms whose images under every translate $s\mathfrak{p}$ are short at every conjugate. Part (b) says that the images of integral forms have small index in the target lattice. The size bound contains the term $-m\,\mathrm{rem}$, and this is where the prime remainder enters the geometry.

### The statements

Recall the main amount and the total remainder of [the prime sums](/chapter/prime-sums/). The main amount is $\mathrm{main} = m k \sum_\tau (s_\infty(\kappa(\tau)) - s_{\mathrm{fin}}(\kappa(\tau), \tau))$, summed over the infinite places $\tau$ of $E$, where $\kappa$ is the weight, $s_\infty(j) = \log j! + j\log(M/\Omega)$ is the size of a derivative of order $j$, and $s_{\mathrm{fin}}$ is the prime sum that measures its divisibility. The total remainder is $\mathrm{rem} = \sum_{\tau \in \Phi_a} (s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}})$, summed over the $a$-places, with the main part $s_{\mathrm{main}}$ of the prime sums.

**Theorem (Theorem A (a), short forms).** The span over $\mathbb{C}$ of the set of $\varphi \in \mathrm{src}_{\mathrm{int}}$ such that

$$\|\Theta_1(s\mathfrak{p}\varphi)\|_\sigma^2 \leq \exp\bigl(\mathrm{main} - m \cdot \mathrm{rem} + f a \log^4 b\bigr)$$

for every $s \in \bar G$ and every automorphism $\sigma$ of $\mathbb{C}$ is all of $\mathrm{src}$.

Lean: `New.Data.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean).

**Theorem (Theorem A (b), small index).** Let $\mathcal{T}$ be a finite subset of $\bar G$, and let $y_1, \dots, y_n$ be target forms such that each $y_i$ is $s\mathfrak{p}\varphi$ for some $s \in \mathcal{T}$ and some $\varphi \in \mathrm{src}_{\mathrm{int}}$. Then $y$ has index at most

$$\#\mathcal{T} \cdot \dim \mathrm{src} \cdot 2 f a \log^3 b$$

in the target lattice.

Lean: `New.Data.indexLe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

Part (a) bounds every conjugate $\sigma$ at once, as the covolume requires. Part (b) needs no shortness, and its bound is linear in the number of translates.

### The inputs

The proof of part (a) uses three results of Volume 9 and the seesaw identity of Section 2. A form on a unitary group is *$B$-short* if each of its values is integral for the Weyl lattice at every $p$-adic embedding, and every conjugate of each value under $\mathrm{Aut}(\mathbb{C})$ has squared Weyl norm at most $B$.

**Theorem (Short source forms).** The space $\mathrm{src}$ is spanned by the $\varphi \in \mathrm{src}$ that are $\exp(f a \log^3 b)$-short.

Lean: `New.Data.span_isShort_ramifiedSourceForms_eq_top` (New/UpperBound/Size/ShortColumns.lean).

**Theorem (Size of the composite lift).** Let $\Psi$ be a chain datum for the trivial twist, let $\sigma$ be an automorphism of $\mathbb{C}$, let $\varphi$ be a source form, and let $B$ be real. Suppose that every value of $\sigma\varphi$ has squared Weyl norm at most $e^B$. Then every value of the $\sigma$-conjugate of $B_1\varphi$ has squared Weyl norm at most $\exp(B + \beta)$, where

$$\beta = \mathrm{main} - m\cdot \mathrm{rem} + 2\sum_{p \in \mathcal{S}} \mathrm{gain}_p \log p + f a \log^3 b.$$

Lean: `New.Data.weylNormSq_compositeLift_le` (New/UpperBound/Size/ArchimedeanSize.lean).

**Lemma (Size of the good part).** Let $z$ be a form on $Y_0$, let $s \in \bar G$, let $\sigma$ be an automorphism of $\mathbb{C}$, and let $B$ be real. If every value of $\sigma$ applied to $\iota_1 z$ has squared Weyl norm at most $e^B$, then $\|\Theta_1(\#\bar G\, e_0\, s\, z)\|_\sigma^2 \leq \exp(x^{99} + B)$.

Lean: `New.Data.normSqAt_goodProjTranslate_le` (New/UpperBound/Size/ArchimedeanSize.lean).

The proof of part (b) uses the divisibility of the composite lift (Section 2) and one lemma on integrality.

**Lemma (Integrality of the images).** Let $\iota$ lie above the prime $\ell$, let $s \in \bar G$, and let $\varphi \in \mathrm{src}$. Suppose that for every twist $\vartheta$ with $\mathrm{Nm}\,Q(\vartheta)$ prime to $\ell$ and every chain datum $\Psi$ of $\vartheta$, the form $B_\vartheta\varphi$ has valuation at least $\mathrm{gain}_\ell - \mathrm{err}(\ell)$ at $\iota$. Then $s\mathfrak{p}\varphi$ is integral at $\iota$.

Lean: `New.Data.normalizedPoincare_mem_integralVectors` (New/Reduction/ShortAndEnough.lean).

*Proof.* Let $\vartheta$ be an $m$-fold twist with $\mathrm{Nm}\,Q(\vartheta)$ prime to $\ell$, and let $\Psi$ be its chain datum from the seesaw identity, so that $\iota_\vartheta z = B_\vartheta\varphi$ for $z = \mathcal{P}(c_{ss}^{-1}\varphi)$. Since $g_\ell \leq \mathrm{gain}_\ell - \mathrm{err}(\ell)$, the form $\ell^{-g_\ell} B_\vartheta\varphi$ is integral at $\iota$. The $\iota$-adic absolute value of $c_B$ equals that of $\ell^{-g_\ell}$ (Section 2). So $c_B\,\iota_\vartheta z$ is integral at $\iota$. The map $\#\bar G\, e_0\, s$ keeps integrality, because the coefficients of $\#\bar G\, e_0$ are algebraic integers. So $\Theta_\vartheta(s\mathfrak{p}\varphi) = c_B\,\Theta_\vartheta(\#\bar G\, e_0\, s\, z)$ is integral at $\iota$. $\square$

**Lemma (Index of one translate).** Let $s \in \bar G$, and let $y_1, \dots, y_n$ be target forms of the form $s\mathfrak{p}\varphi$ with $\varphi \in \mathrm{src}_{\mathrm{int}}$. Then $y$ has index at most $\dim \mathrm{src} \cdot 2 f a \log^3 b$.

Lean: `New.Data.indexLe_of_mem_image_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* Fix $\iota$ above $\ell$. The lemma on the properties of the errors gives $j \leq \mathrm{err}(\ell) D_X$ and a module $S$ on which $B_\vartheta$ has valuation at least $\mathrm{gain}_\ell - \mathrm{err}(\ell)$ for all twists prime to $\ell$, such that the forms of $\mathrm{src}$ integral at $\iota$ are carried into $S$ by a matrix whose determinant divides $\ell^j$. By the lemma on integrality, $s\mathfrak{p}$ maps $S$ into the target forms integral at $\iota$. So the images of the forms integral at $\iota$ are carried into the integral target forms with loss $j$, by the same matrix for every twist. The rule that a colength gives an index ([twisted lattices](/chapter/twisted-lattices/)) gives index at most $\delta$ with $e(\ell) = D_X\,\mathrm{err}(\ell)$. The ramified forms have at least half the dimension of all source forms, since $\dim \mathrm{src} \geq (1 - f/(N-1)) D_X$ and $f/(N - 1) \leq b^{-8} \leq 1/2$ (`New.Data.finrank_sourceForm_le_two_mul`). So $\sum_\ell e(\ell)\log \ell \leq 2\dim\mathrm{src} \sum_\ell \mathrm{err}(\ell)\log \ell \leq 2\dim\mathrm{src}\cdot f a \log^3 b$. $\square$

### The proofs

*Proof of Theorem A (a).* It suffices to show that every $\exp(f a\log^3 b)$-short form $\varphi \in \mathrm{src}$ lies in the set of the statement, since these forms span $\mathrm{src}$ by the theorem on short source forms. Let $\varphi$ be such a form. Its values are integral at every $p$-adic embedding, so $\varphi \in \mathrm{src}_{\mathrm{int}}$. Fix $s$ and $\sigma$, and let $z = \mathcal{P}(c_{ss}^{-1}\varphi)$.

1. The seesaw identity gives a chain datum $\Psi$ of the trivial twist with $\iota_1 z = B_1\varphi$.
2. Every value of $\sigma\varphi$ has squared norm at most $\exp(f a \log^3 b)$. The theorem on the size of the composite lift, with $B = f a\log^3 b$, bounds every value of $\sigma B_1 \varphi = \sigma\iota_1 z$ by $\exp(f a \log^3 b + \beta)$.
3. The lemma on the good part gives $\|\Theta_1(\#\bar G\,e_0\,s\,z)\|_\sigma^2 \leq \exp(x^{99} + f a\log^3 b + \beta)$.
4. The factor $c_B$ multiplies this by $\exp(2\log c_B)$, and the lemma on the logarithm of the gain factor gives $2\log c_B \leq -2\sum_{p\in\mathcal{S}}\mathrm{gain}_p\log p + 2 f a\log^3 b + 2b$.

The gains cancel, and the exponent is at most

$$\mathrm{main} - m\cdot\mathrm{rem} + x^{99} + 4 f a \log^3 b + 2b.$$

The sizes give $x^{99} + 4 f a\log^3 b + 2b \leq f a\log^4 b$. $\square$

*Proof of Theorem A (b).* Sort the family by translates. For each $s \in \mathcal{T}$, the members of the form $s\mathfrak{p}\varphi$ have index at most $\dim\mathrm{src} \cdot 2 f a \log^3 b$ by the lemma on one translate. Index bounds add over a union of families ([twisted lattices](/chapter/twisted-lattices/)), so the whole family has index at most $\#\mathcal{T}$ times this bound. $\square$

### What Theorem A costs

Part (a) costs $f a \log^4 b$ per vector. The slack has three parts. The projection to the good part costs $x^{99}$. The short forms, the composite lift and the gains (twice) cost $f a\log^3 b$ each. The integer parts of the gains cost $2b$. All three are far below $f a \log^4 b$: the sizes give $x^{10^{12}} \leq b$, so $x^{99} < b$, and $b \leq a$.

Part (b) costs $2 f a \log^3 b$ per dimension of the source and per translate. With the bound $\#\mathcal{T} \dim\mathrm{src} \leq 5 d_T\log(1 + 2b^2)$ of Theorem B, the index of the family of the main inequality is at most $d_T \cdot 10\log(1 + 2b^2)\cdot f a\log^3 b$.

### The plan in Volume 9

Volume 9 proves the inputs of Theorem A. [Theorem A and its plan](/chapter/theorem-a-plan/) gives the overview, and [the proof of Theorem A](/chapter/proof-of-theorem-a/) assembles it.

1. *The objects.* The source forms, the hermitian spaces $X_j$ and $Y_j$, the chains of lifts, and the composite lift are set up in [the objects of the upper bound](/chapter/upper-bound-objects/), with the theta kernels and the gauges that measure integrality in [theta kernels and gauges](/chapter/theta-kernels-gauges/).
2. *The seesaw identity.* [Part 1](/chapter/seesaw-identity-1/) and [part 2](/chapter/seesaw-identity-2/) unfold the lower chain of a Poincaré series and identify it with a composite lift. The constant is chosen, as in Section 2.
3. *The archimedean size.* [The archimedean size of the composite lift](/chapter/archimedean-size/) bounds each lift by the size of a derivative of order $\kappa(\tau)$ at each infinite place $\tau$. This gives the term $s_\infty$ in the main amount.
4. *The divisibility.* [Short columns and the gain](/chapter/short-columns-gain/#the-gain-and-its-measures) defines the gain $\mathrm{gain}_p$. Chapters 4 to 7 and 13 of Volume 9 study the field $E$ at the primes, [the CM curve and its formal group](/chapter/cm-formal-group/), [normal forms](/chapter/normal-forms/), [the integral vacuum](/chapter/integral-vacuum/), and [elementary divisors of a Hecke operator](/chapter/elementary-divisors/). [Divisibility prime by prime](/chapter/divisibility/) proves the theorem of Section 2. The local prime sums in the gains add up to the term $s_{\mathrm{fin}}$ of the main amount.

The hard part is the balance in item 3 and item 4. The main amount is the difference of an archimedean size and a non-archimedean divisibility, and both must be computed with an error of size $f a \log^3 b$ against a main term of size at least $x^4 f a$.
