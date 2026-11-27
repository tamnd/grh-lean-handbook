---
title: How the inputs meet
lean:
  - New/UpperBound/Size/ShortColumns.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
  - New/Reduction/ShortAndEnough.lean
decls:
  - New.IsShort
  - New.Data.span_isShort_ramifiedSourceForms_eq_top
  - New.Data.normSqAt_goodProjTranslate_le
  - New.Data.invGainFactor
  - New.Data.log_invGainFactor_le
  - New.Data.normSqAt_normalizedPoincare
  - New.Data.normalizedPoincare_mem_integralVectors
  - New.Data.finrank_sourceForm_le_two_mul
  - New.Data.indexLe_of_mem_image_normalizedPoincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## How the inputs meet

This section proves Theorem A from the three inputs of Section 3 and five further lemmas. Part (a) uses the seesaw identity and the archimedean size for the trivial twist, and the gain factor $c_B$. Part (b) uses the seesaw identity and the divisibility for all twists. The divisibility and the size meet in the number $c_B$: its absolute value at $\ell$ removes the divisibility, and its square at infinity removes the term $2\sum_p\mathrm{gain}_p\log p$ of the size. [The proof of Theorem A](/chapter/proof-of-theorem-a/) gives the same proof with every detail of the passage to the target.

### Short forms

Part (a) starts from source forms that are small and integral.

**Definition (Short forms).** Let $B$ be real. A form $\varphi$ on the unitary group of a definite hermitian space over $E$ is *$B$-short* if for every prime $p$ and every $p$-adic place of $\mathbb{C}$ each value $\varphi(g)$ is integral for the Weyl lattice at $g$, and for every automorphism $\sigma$ of $\mathbb{C}$ and every finite adelic point $g$ the squared Weyl norm of $\sigma(\varphi(g))$ is at most $B$.

Lean: `New.IsShort` (New/UpperBound/Size/ShortColumns.lean).

**Theorem (Short source forms).** The ramified source forms that are $\exp(f a\log^3 b)$-short span $\mathrm{src}$ over $\mathbb{C}$.

Lean: `New.Data.span_isShort_ramifiedSourceForms_eq_top` (New/UpperBound/Size/ShortColumns.lean).

*Proof.* Put $Z = \exp(f a \log^3 b)/4^f$. The source forms that are $Z$-short span all source forms. This is a lemma of [short columns and the gain](/chapter/short-columns-gain/). If $\varphi$ is $B$-short and $k$ is a finite adelic point with integral entries, then $\varphi$ minus its right translate by $k$ is $4B$-short. The operator $\prod_w(1 - z_w)$ has $f$ factors of this kind, so it sends $Z$-short forms to $4^f Z$-short forms. Its image is $\mathrm{src}$ (Section 1). So the images of the $Z$-short forms span $\mathrm{src}$, and they are $\exp(f a\log^3 b)$-short. $\square$

### The size of the good part

The target forms are good parts of forms on $Y_0$. The passage to the good part costs a factor that does not depend on the form.

**Lemma (Size of the good part).** Let $\sigma$ be an automorphism of $\mathbb{C}$, let $z$ be a form of principal level on $Y_0$, let $s \in \bar G$ and let $B$ be real. If every value of $\sigma\circ\iota_1 z$ has squared Weyl norm at most $e^B$, then $\|\Theta_1(\#\bar G\, e_0\, s\, z)\|_\sigma^2 \leq \exp(x^{99} + B)$.

Lean: `New.Data.normSqAt_goodProjTranslate_le` (New/UpperBound/Size/ArchimedeanSize.lean).

The idea of the proof is a count. The coefficients of $\sigma(e_0)$ have absolute value at most $1$, since $\#\bar G\,\sigma(e_0)$ is the character of a representation of dimension at most $\#\bar G$. So each value of $\Theta_1(\#\bar G\, e_0\, s\, z)$ is a sum of $\#\bar G$ right translates of values of $\iota_1 z$, each of norm at most $\#\bar G\, e^{B/2}$. The squared norm $\|\cdot\|_\sigma^2$ is a sum over classes, and there are at most $\exp(x^{30})$ classes. The bound $\exp(x^{30})(\#\bar G)^4 \leq \exp(x^{99})$ ends the proof.

### The gain factor

**Definition (The gain factor).** For $l \in \mathcal{S}\cup\{N\}$ put $g_l = \lfloor\mathrm{gain}_l - \mathrm{err}(l)\rfloor$. The *gain factor* is the positive rational number

$$c_B = \prod_{l \in \mathcal{S}\cup\{N\}} l^{-g_l}.$$

Lean: `New.Data.invGainFactor` (New/Reduction/ShortAndEnough.lean).

At a prime $\ell$ and an $\ell$-adic place $\iota$, the absolute value of $c_B$ is $\ell^{g_\ell}$ if $\ell \in \mathcal{S}\cup\{N\}$ and $1$ otherwise. The gain at $N$ is $0$, as $N \geq x_1$, so $g_N = \lfloor -\mathrm{err}(N)\rfloor \leq 0$. The factor $N^{-g_N}$ is a positive power of $N$ that pays for the loss at the level. The integer parts cost little.

**Lemma (Logarithm of the gain factor).** $\log c_B \leq -\sum_{l\in\mathcal{S}}\mathrm{gain}_l\log l + f a\log^3 b + b$.

Lean: `New.Data.log_invGainFactor_le` (New/Reduction/ShortAndEnough.lean).

*Proof.* We have $\log c_B = -\sum_l g_l\log l$ and $g_l > \mathrm{gain}_l - \mathrm{err}(l) - 1$. So $\log c_B < -\sum_l \mathrm{gain}_l\log l + \sum_l\mathrm{err}(l)\log l + \sum_l\log l$, with the sums over $\mathcal{S}\cup\{N\}$. The gain at $N$ is $0$. Property 3 of the divisibility bounds the second sum by $f a\log^3 b$. The third sum is at most $\lceil x_1\rceil x_1 + \log N \leq b$. $\square$

**Lemma (The factor $c_B$ at infinity).** For $s \in \bar G$, $\varphi \in \mathrm{src}$ and every automorphism $\sigma$ of $\mathbb{C}$,

$$\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 = \exp(2\log c_B)\,\|\Theta_1(\#\bar G\, e_0\, s\, \mathcal{P}(c_{ss}^{-1}\varphi))\|_\sigma^2.$$

Lean: `New.Data.normSqAt_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* The number $c_B$ is rational and positive, so $|\sigma(c_B)|^2 = c_B^2 = \exp(2\log c_B)$. $\square$

### The proof of part (a)

*Proof of [Theorem A (a)](/decl/New.Data.span_short_integralRamified_eq_top/).* By the theorem on short source forms it is enough to show that every $\exp(f a\log^3 b)$-short $\varphi \in \mathrm{src}$ lies in the set of the statement. Let $\varphi$ be such a form. It is integral at every $\iota$, so $\varphi\in\mathrm{src}_{\mathrm{int}}$. Fix $s \in \bar G$ and $\sigma$, and put $z = \mathcal{P}(c_{ss}^{-1}\varphi)$.

1. The seesaw identity for $c_{ss}^{-1}\mathcal{P}$, for the trivial twist, gives a chain datum $\Psi$ with $\iota_1 z = B_{1,\Psi}\varphi$.
2. The theorem on the size of the composite lift, with $B = f a\log^3 b$, gives that every value of $\sigma\circ\iota_1 z$ has squared norm at most $\exp(f a\log^3 b + \beta)$.
3. The lemma on the good part gives $\|\Theta_1(\#\bar G\, e_0\, s\, z)\|_\sigma^2 \leq \exp(x^{99} + f a\log^3 b + \beta)$.
4. The lemma on $c_B$ at infinity multiplies this by $\exp(2\log c_B)$, and the lemma on $\log c_B$ bounds $2\log c_B$ by $-2\sum_{l\in\mathcal{S}}\mathrm{gain}_l\log l + 2 f a\log^3 b + 2b$.

The term $2\sum_l\mathrm{gain}_l\log l$ in $\beta$ cancels against step 4. The exponent is at most $\mathrm{mainAmount} - m\cdot\mathrm{rem} + x^{99} + 4 f a\log^3 b + 2b$. The sizes of the data give $x^{99} + 4 f a\log^3 b + 2b \leq f a\log^4 b$ ([the data and its sizes](/chapter/data-and-sizes/)). $\square$

The cancellation in step 4 is exact. The factor $2$ in $\beta$ comes from the lemma on the sum of the gains (Section 3), and the factor $2$ in $2\log c_B$ comes from the square in the norm. No part of the gain is lost, except the integer parts and the errors, which cost $2 f a \log^3 b + 2b$. The table lists all the terms of the exponent.

| term | source | amount |
|---|---|---|
| shortness of $\varphi$ | short source forms | $f a\log^3 b$ |
| size of the chain | composite lift | $\mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\Sigma + f a\log^3 b$ |
| good part | size of the good part | $x^{99}$ |
| gain factor | $2\log c_B$ | $-2\Sigma + 2 f a\log^3 b + 2b$ |

Here $\Sigma = \sum_{l\in\mathcal{S}}\mathrm{gain}_l\log l$. The total is $\mathrm{mainAmount} - m\cdot\mathrm{rem} + x^{99} + 4 f a\log^3 b + 2b$.

### The proof of part (b)

Part (b) needs integrality, not size, and it needs it for every twist of level prime to $\ell$.

**Lemma (Integrality of the images).** Let $\iota$ lie above the prime $\ell$, let $s \in \bar G$ and $\varphi\in\mathrm{src}$. Suppose that for every twist $\vartheta$ with $\mathrm{Nm}\,Q(\vartheta)$ prime to $\ell$ and every chain datum $\Psi$ for $\vartheta$, every value of $B_{\vartheta,\Psi}\varphi$ has $\iota$-adic gauge at most $\ell^{\mathrm{err}(\ell) - \mathrm{gain}_\ell}$. Then $s\mathfrak{p}\,\varphi$ is integral at $\iota$: $\Theta_\vartheta(s\mathfrak{p}\,\varphi)$ is integral at $\iota$ for every $m$-fold twist $\vartheta$ of level prime to $\ell$.

Lean: `New.Data.normalizedPoincare_mem_integralVectors` (New/Reduction/ShortAndEnough.lean).

*Proof.* Fix $\vartheta$ and take the chain datum $\Psi$ of the seesaw identity for $c_{ss}^{-1}\mathcal{P}$, so that $\iota_\vartheta z = B_{\vartheta,\Psi}\varphi$ with $z = \mathcal{P}(c_{ss}^{-1}\varphi)$. As $g_\ell \leq \mathrm{gain}_\ell - \mathrm{err}(\ell)$, the form $\ell^{-g_\ell}B_{\vartheta,\Psi}\varphi$ is integral at $\iota$, and $|c_B|_\iota = |\ell^{-g_\ell}|_\iota$. So $c_B\,\iota_\vartheta z$ is integral at $\iota$. The map $\#\bar G\, e_0\, s$ keeps integrality, as the coefficients of $\#\bar G\, e_0$ are algebraic integers. $\square$

**Lemma (Dimension of the source).** $D_X \leq 2\dim_{\mathbb{C}}\mathrm{src}$.

Lean: `New.Data.finrank_sourceForm_le_two_mul` (New/Reduction/ShortAndEnough.lean).

*Proof.* The source has dimension at least $(1 - f/(N-1))D_X$, and $f/(N-1) \leq 1/2$ by the sizes. $\square$

**Lemma (Index of one translate).** Let $s\in\bar G$ and let $y_1, \dots, y_n$ be target forms with each $y_i \in s\mathfrak{p}(\mathrm{src}_{\mathrm{int}})$. Then $y$ has index at most $\dim_{\mathbb{C}}\mathrm{src}\cdot 2 f a\log^3 b$ in the target lattice.

Lean: `New.Data.indexLe_of_mem_image_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* Fix $\iota$ above $\ell$, and let $\mathcal{O}$ be the ring of complex numbers that the place of $\iota$ sends to $\ell$-adic integers. Property 4 of the divisibility, in the form of the lemma `New.Data.exists_colengthDvd_gaugeLe_divisibilityError`, gives $j \leq \mathrm{err}(\ell)D_X$ and an $\mathcal{O}$-submodule $S$ of the space of all source forms, with colength dividing $\ell^j$ in the module $L$ of integral ramified source forms, on which every composite lift prime to $\ell$ has gauge at most $\ell^{\mathrm{err}(\ell) - \mathrm{gain}_\ell}$. The colength lives in the space of all source forms, and integrality lives in $T$. So the proof moves the colength in two steps. Let $A = s\mathfrak{p}$ as an $\mathcal{O}$-linear map $\mathrm{src} \to T$, let $T_\iota$ be the target forms integral at $\iota$, and let $M \subseteq \mathrm{src}$ be the module of ramified forms integral at $\iota$, the pull back of the integral source forms along the inclusion of $\mathrm{src}$.

1. *Pull back.* A form in $M$ lies in $L$. A form in $M \cap S$ satisfies the hypothesis of the lemma on integrality, so $A$ maps it into $T_\iota$. The rule for the pull back of a colength ([colength](/chapter/twisted-lattices/#colength)) gives $\mathrm{ColengthDvd}(M, A^{-1}(T_\iota), \ell^j)$: the colength of $A^{-1}(T_\iota)$ in $M$ divides $\ell^j$.
2. *Push forward.* The rule for the push forward along $A$ gives $\mathrm{ColengthDvd}(A(M), T_\iota, \ell^j)$, as $A(M) \subseteq A(M) + T_\iota$ and $A(A^{-1}(T_\iota)) \subseteq T_\iota$.

Every $\varphi \in \mathrm{src}_{\mathrm{int}}$ lies in $M$, so each $y_i$ lies in $A(M)$. The rule that a colength gives an index ([twisted lattices](/chapter/twisted-lattices/)) applies to the module $A(M)$ with $e(\ell) = D_X\,\mathrm{err}(\ell)$. Then $\sum_\ell e(\ell)\log\ell \leq 2\dim\mathrm{src}\sum_\ell\mathrm{err}(\ell)\log\ell \leq 2\dim\mathrm{src}\cdot f a\log^3 b$, by the lemma on the dimension and property 3. [The proof of part (b)](/chapter/proof-of-theorem-a/#the-proof-of-part-b) gives the two steps in full. $\square$

*Proof of [Theorem A (b)](/decl/New.Data.indexLe_normalizedPoincare/).* Sort the family by the translates $s\in t$. Each part has index at most $\dim\mathrm{src}\cdot 2 f a\log^3 b$ by the lemma on one translate. Index bounds add over a finite union of families ([twisted lattices](/chapter/twisted-lattices/)). So the family has index at most $\#t$ times this bound. $\square$

**Remark (Formalization).** The two parts use the seesaw identity differently. Part (a) uses it for the trivial twist only, as the size theorem is proved only for chain data of the trivial twist. Part (b) uses it for every twist of level prime to $\ell$, because integrality in the target lattice is tested by all such twists. As the divisibility holds for every chain datum, it does not matter which one the seesaw identity provides.
