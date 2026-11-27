---
title: The inputs from the volume
lean:
  - New/UpperBound/Divisibility/LocalDivisibility.lean
  - New/UpperBound/Seesaw/SeesawIdentity.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
  - New/UpperBound/Size/ShortColumns.lean
  - New/UpperBound/Size/Estimates.lean
decls:
  - New.Data.gain
  - New.Data.gain_eq_zero
  - New.Data.exists_err_gaugeLe_compositeLift
  - New.Data.seesaw_identity
  - New.Data.weylNormSq_compositeLift_le
  - New.IsShort
  - New.Data.span_isShort_ramifiedSourceForms_eq_top
  - New.Data.normSqAt_goodProjTranslate_le
  - New.Data.goodProjTranslate_mem_integralForms
  - New.Data.le_finrank_ramifiedSourceForms
  - New.Data.f_div_N_sub_one_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The inputs from the volume

This section states the results of chapters 9 to 14 that the proof of Theorem A uses. Each statement is the statement of the source, with a link to the section that proves it. The proofs are not repeated. Section 8 gives the file and the line of each input.

### The composite lift and the gain

The objects are those of [the objects of the upper bound](/chapter/upper-bound-objects/#columns-and-the-composite-lift). For a twist $\vartheta$ and a finitely supported function $\Psi$ on the tuples of translations, the composite lift $B_{\vartheta,\Psi}\varphi$ of a source form $\varphi$ is the chain of $m$ theta lifts from $X_0$ to $X_m$, with the glued tensor of $\Psi$ as data, followed by the restriction to $Y_m$. The function $\Psi$ is a chain datum for $\vartheta$ if it satisfies the four conditions of [the three inputs](/chapter/theorem-a-plan/#the-three-inputs). The lower chain $\iota_\vartheta$ is the chain of $m$ lifts from $Y_0$ to $Y_m$ for the tame character of $\vartheta$. A twist $\vartheta$ has a level $\mathrm{Nm}\,Q(\vartheta)$, the product of the norms of the places of its modulus.

For a prime $p$, an embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$ and a real number $c$, a form $F$ satisfies $\mathrm{GaugeLe}(1, c, F)$ if for every finite adelic point $g$ the $p$-adic gauge of $F(g)$ for the Weyl lattice at $g$ is at most $c$ ([the p-adic gauge](/chapter/automorphic-forms/)). If $c = p^{-v}$, the form has valuation at least $v$.

**Definition (The gain).** For a natural number $p$, $\mathrm{gain}_p = m\bigl(\sum_{\tau\in\Phi_a}s_p(a,\tau) + k\,F(p)\bigr)$, where $s_p$ is the local prime sum and $F(p) = \sum_{\tau\in\Phi}s_p(\kappa(\tau),\tau)$.

Lean: `New.Data.gain` (New/UpperBound/Size/ShortColumns.lean).

[The gain and its measures](/chapter/short-columns-gain/#the-gain-and-its-measures) gives the definition and the meaning of $s_p$.

**Lemma (Vanishing gain).** If $\chi_K(p) = 1$ or $x_1 \leq p$, then $\mathrm{gain}_p = 0$.

Lean: `New.Data.gain_eq_zero` (New/UpperBound/Size/Estimates.lean).

This is proved in [prime sums and allowed losses](/chapter/archimedean-size/#prime-sums-and-allowed-losses). The level satisfies $x_1 \leq N$, so $\mathrm{gain}_N = 0$.

### Input 1: the divisibility

**Theorem (Divisibility of the composite lift).** There is a function $\mathrm{err} : \mathbb{N} \to \mathbb{R}$ with four properties.

1. $\mathrm{err}(p) \geq 0$ for every $p$.
2. If $p \neq N$, and $\chi_K(p) = 1$ or $x_1 \leq p$, then $\mathrm{err}(p) = 0$.
3. For every finite set $U$ of natural numbers, $\sum_{p\in U}\mathrm{err}(p)\log p \leq f a\log^3 b$.
4. For every prime $p$ and every embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$, let $\mathcal{O}$ be the ring of complex numbers that $\iota_p$ sends to $p$-adic integers, and let $L$ be the $\mathcal{O}$-module of integral ramified source forms. There are a natural number $l \leq \mathrm{err}(p)\,D_X$ and an $\mathcal{O}$-submodule $S$ of the source forms with $S \subseteq L$, such that $\mathrm{ColengthDvd}(L, S, p^l)$, and such that for every twist $\vartheta$, every chain datum $\Psi$ for $\vartheta$ with $p$ prime to $\mathrm{Nm}\,Q(\vartheta)$, and every $\varphi \in S$,

$$\mathrm{GaugeLe}\bigl(1,\ p^{\mathrm{err}(p) - \mathrm{gain}_p},\ B_{\vartheta,\Psi}\varphi\bigr).$$

Lean: `New.Data.exists_err_gaugeLe_compositeLift` (New/UpperBound/Divisibility/LocalDivisibility.lean).

This is proved in [the four cases](/chapter/divisibility/#the-four-cases). The relation $\mathrm{ColengthDvd}$ is the colength of Section 3: every finite family in $L$ is carried into $S$ by a square matrix over $\mathcal{O}$ whose determinant divides $p^l$. The proof takes $\mathrm{err}$ equal to the allowed loss, but the statement is an existence statement.

### Input 2: the seesaw identity

**Theorem (Seesaw identity).** Let $t$ be a linear form on the values of forms on $X_0$, and let $g$ be an archimedean point of the unitary group of $Y_0$. There is $c \in \mathbb{C}^\times$ such that every twist $\vartheta$ has a chain datum $\Psi$ for $\vartheta$ with

$$\iota_\vartheta(\mathcal{P}_{g,t}\varphi) = c\cdot B_{\vartheta,\Psi}\varphi$$

for every ramified source form $\varphi$. Here $\mathcal{P}_{g,t}$ is the Poincaré map defined by $g$ and $t$.

Lean: `New.Data.seesaw_identity` (New/UpperBound/Seesaw/SeesawIdentity.lean).

This is proved in [the assembly and the seesaw identity](/chapter/seesaw-identity-2/#the-assembly-and-the-seesaw-identity). Theorem A uses it with the Bessel form and the Bessel point of the data. Then $\mathcal{P}_{g,t}$ is the map $\mathcal{P}$ of Section 1.

### Input 3: the archimedean size

**Theorem (Size of the composite lift).** Let $\Psi$ be a chain datum for the trivial twist, $\sigma$ an automorphism of $\mathbb{C}$, $\varphi$ a source form and $B$ a real number. Suppose that $|\sigma\varphi(g)|^2 \leq e^B$ for every finite adelic point $g$ of the unitary group of $X_0$, where $|\cdot|^2$ is the squared Weyl norm. Then for every finite adelic point $y$ of the unitary group of $Y_m$,

$$|\sigma(B_{1,\Psi}\varphi)(y)|^2 \leq \exp(B + \beta), \qquad \beta = \mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal{S}}\mathrm{gain}_p\log p + f a\log^3 b.$$

Lean: `New.Data.weylNormSq_compositeLift_le` (New/UpperBound/Size/ArchimedeanSize.lean).

This is proved in [the size of the composite lift](/chapter/archimedean-size/#the-size-of-the-composite-lift). The theorem is a statement about one chain datum of the trivial twist. It says nothing about other twists.

### Short forms

**Definition (Short forms).** Let $B$ be real. A form $\varphi$ is $B$-short if two conditions hold. For every prime $p$ and every embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$, $\mathrm{GaugeLe}(1, 1, \varphi)$. For every automorphism $\sigma$ of $\mathbb{C}$ and every finite adelic point $g$, $|\sigma\varphi(g)|^2 \leq B$.

Lean: `New.IsShort` (New/UpperBound/Size/ShortColumns.lean).

**Theorem (Short ramified forms span).** The ramified source forms that are $\exp(f a\log^3 b)$-short span $\mathrm{src}$ over $\mathbb{C}$.

Lean: `New.Data.span_isShort_ramifiedSourceForms_eq_top` (New/UpperBound/Size/ShortColumns.lean).

This is proved in [short ramified forms span](/chapter/short-columns-gain/#short-ramified-forms-span). The bound $B = e^{\mathrm{err}_0}$ matches the hypothesis of the size theorem with $B = \mathrm{err}_0$ in the exponent.

### The good part

The map $\#\bar G\,e_0\,s$ sends a form $z$ of principal level on $Y_0$ to $\#\bar G$ times the good part of its translate by $s$. The source calls it `goodProjTranslate s`. Its image lies in the target $T$. For a tame character $\vartheta$, the map $\iota_\vartheta$ followed by the passage to the level of $\vartheta$ is `lowerChainAtLevel`. On target forms it is $\Theta_\vartheta$.

**Lemma (Size of the good part).** Let $\sigma$ be an automorphism of $\mathbb{C}$, $z$ a form of principal level on $Y_0$, $s \in \bar G$ and $B$ real. Suppose that $|\sigma(\iota_1 z)(g)|^2 \leq e^B$ for every finite adelic point $g$ of the unitary group of $Y_m$. Then

$$\|\iota_1(\#\bar G\,e_0\,s\,z)\|_\sigma^2 \leq \exp(x^{99} + B),$$

where $\iota_1$ on the left is taken at the level of the trivial twist.

Lean: `New.Data.normSqAt_goodProjTranslate_le` (New/UpperBound/Size/ArchimedeanSize.lean).

**Lemma (The good part keeps integrality).** Let $\ell$ be a prime and $j : \mathbb{C} \to \mathbb{C}_\ell$ an embedding. Let $\vartheta$ be a tame character, $c \in \mathbb{C}$, $z$ a form of principal level on $Y_0$ and $s \in \bar G$. If $c\cdot\iota_\vartheta z$ is integral at $j$, then $c\cdot\iota_\vartheta(\#\bar G\,e_0\,s\,z)$ is integral at $j$.

Lean: `New.Data.goodProjTranslate_mem_integralForms` (New/UpperBound/Size/ArchimedeanSize.lean).

Both lemmas are proved in [the good part](/chapter/archimedean-size/#the-good-part). The first is a count: each value of $\iota_1(\#\bar G\,e_0\,s\,z)$ is a sum of $\#\bar G$ right translates of values of $\iota_1 z$ with coefficients $\#\bar G\,e_0(t)$, and $|\sigma e_0(t)| \leq 1$. There are at most $\exp(x^{30})$ classes, and $\exp(x^{30})(\#\bar G)^4 \leq \exp(x^{99})$. The second uses that the coefficients $\#\bar G\,e_0(t)$ are algebraic integers, as $\#\bar G\,e_0$ is a character, and that the gauge is ultrametric.

### The dimension of the source

**Lemma (Ramified forms are many).** $(1 - f/(N-1))\,D_X \leq \dim_{\mathbb{C}}\mathrm{src}$.

Lean: `New.Data.le_finrank_ramifiedSourceForms` (New/UpperBound/Size/ShortColumns.lean).

**Lemma (A small proportion).** $f/(N-1) \leq b^{-8}$.

Lean: `New.Data.f_div_N_sub_one_le` (New/UpperBound/Size/ShortColumns.lean).

Both are proved in [scalings and ramified forms](/chapter/short-columns-gain/#scalings-and-ramified-forms). The second uses $f \leq b$ and $b^9 + 1 \leq N$.

**Remark (Formalization).** The four inputs above are stated in the source with the data $D$ implicit or explicit, and with instances for the prime $p$ and the place. The divisibility quantifies over the type `D.Twist` of twists, not over the $m$-fold twists of the target lattice. Every $m$-fold twist has an underlying twist, so the divisibility applies to it. The seesaw identity quantifies over `D.Twist` too. The size theorem and the size of the good part are proved only for the trivial character `TameChar.one`. This is the reason why part (a) of Theorem A uses only the trivial twist.
