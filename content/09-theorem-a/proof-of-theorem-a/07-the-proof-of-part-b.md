---
title: The proof of part (b)
lean:
  - New/Reduction/ShortAndEnough.lean
decls:
  - New.Data.normalizedPoincare_mem_integralVectors
  - New.Data.finrank_sourceForm_le_two_mul
  - New.Data.indexLe_of_mem_image_normalizedPoincare
  - New.Data.indexLe_normalizedPoincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The proof of part (b)

This section proves part (b) of Theorem A in three steps. The first step is local: at one $\iota$, a source form whose composite lifts have enough valuation maps to an integral target form. The second step fixes one translate $s$ and turns the colength of the divisibility into an index. The third step adds the translates. A lemma on the dimension of the source converts $D_X$ into $\dim\mathrm{src}$.

### Integrality at one place

**Lemma (Integral images).** Let $\iota$ lie above the prime $\ell$, let $s \in \bar G$ and let $\varphi \in \mathrm{src}$. Suppose that for every twist $\vartheta$ and every chain datum $\Psi$ for $\vartheta$ with $\ell$ prime to $\mathrm{Nm}\,Q(\vartheta)$,

$$\mathrm{GaugeLe}\bigl(1,\ \ell^{\mathrm{err}(\ell) - \mathrm{gain}_\ell},\ B_{\vartheta,\Psi}\varphi\bigr)$$

at the place of $\iota$. Then $s\mathfrak{p}\,\varphi$ is integral at $\iota$ in the target lattice.

Lean: `New.Data.normalizedPoincare_mem_integralVectors` (New/Reduction/ShortAndEnough.lean).

*Proof.* By the lemma on integral target forms, it suffices to show that $\Theta_\vartheta(s\mathfrak{p}\,\varphi)$ is integral at the place of $\iota$ for every $m$-fold twist $\vartheta$ with $\ell$ prime to $\mathrm{Nm}\,Q(\vartheta)$. Fix such a $\vartheta$.

*Step 1: the seesaw identity.* The seesaw identity for $c_{ss}^{-1}\mathcal{P}$, applied to the underlying twist of $\vartheta$, gives a chain datum $\Psi$ with $\iota_\vartheta z = B_{\vartheta,\Psi}\varphi$, where $z = \mathcal{P}(c_{ss}^{-1}\varphi)$.

*Step 2: removing the power.* The hypothesis applies to $\vartheta$ and $\Psi$, since an $m$-fold twist extends its underlying twist and has the same level. It gives $\mathrm{GaugeLe}(1, \ell^{r}, B_{\vartheta,\Psi}\varphi)$ with $r = \mathrm{err}(\ell) - \mathrm{gain}_\ell$. The floor gives $g_\ell \leq \mathrm{gain}_\ell - \mathrm{err}(\ell) = -r$. The lemma on removing a power, with $\beta = g_\ell$, gives

$$\mathrm{GaugeLe}\bigl(1,\ 1,\ \ell^{-g_\ell}\,B_{\vartheta,\Psi}\varphi\bigr).$$

*Step 3: the gain factor.* By the lemma on the gain factor at a prime, $\|\iota_\ell(c_B)\| = \|\iota_\ell(\ell^{-g_\ell})\|$. The gauge of a scalar multiple is the absolute value of the scalar times the gauge. So at every finite adelic point $g$ the gauge of $c_B\,(\iota_\vartheta z)(g)$ is the gauge of $\ell^{-g_\ell}(B_{\vartheta,\Psi}\varphi)(g)$, which is at most $1$ by Step 2. So $c_B\cdot\iota_\vartheta z$ is integral at the place of $\iota$, at the level of $\vartheta$.

*Step 4: the good part.* The map $\Theta_\vartheta$ is linear, so $\Theta_\vartheta(s\mathfrak{p}\,\varphi) = c_B\,\Theta_\vartheta(s\mathfrak{p}_0\,\varphi) = c_B\cdot\iota_\vartheta(\#\bar G\,e_0\,s\,z)$. The lemma on the good part, which keeps integrality, applies with $c = c_B$, by Step 3. So $\Theta_\vartheta(s\mathfrak{p}\,\varphi)$ is integral at the place of $\iota$. $\square$

The proof uses the seesaw identity for each $m$-fold twist, with a chain datum that depends on the twist. The hypothesis is asked for every chain datum, so the choice does not matter. The lemma does not use the size of $\varphi$ and does not use the integrality of $\varphi$ either: the integrality of the image comes from the hypothesis on the composite lifts.

### Half the source forms

**Lemma (Half the source forms are ramified).** $D_X \leq 2\dim_{\mathbb{C}}\mathrm{src}$.

Lean: `New.Data.finrank_sourceForm_le_two_mul` (New/Reduction/ShortAndEnough.lean).

*Proof.* By the lemma on a small proportion, $f/(N-1) \leq b^{-8}$. As $b \geq 2$ by the sizes of the data, $b^{-8} \leq 1/2$. So $1 - 1/2 \leq 1 - f/(N-1)$. The lemma on ramified forms gives $(1 - f/(N-1))\,D_X \leq \dim\mathrm{src}$. Hence $\tfrac12 D_X \leq \dim\mathrm{src}$. $\square$

The constant $2$ is the factor $2$ in the bound of part (b). The lemma is far from sharp: $\dim\mathrm{src}$ is $D_X$ up to a proportion $b^{-8}$. The source uses $2$ because a clean constant is enough downstream.

### One translate

**Lemma (Index of one translate).** Fix $s \in \bar G$. Let $y_1, \dots, y_n$ be target forms with $y_i \in s\mathfrak{p}(\mathrm{src}_{\mathrm{int}})$ for each $i$. Then $y$ has index at most $\dim_{\mathbb{C}}\mathrm{src}\cdot 2 f a\log^3 b$ in the target lattice.

Lean: `New.Data.indexLe_of_mem_image_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* Apply the theorem on index from colength with $e(\ell) = D_X\,\mathrm{err}(\ell)$. Three things need proof.

*The numbers $e(\ell)$ are nonnegative.* This holds as $D_X \geq 0$ and $\mathrm{err}(\ell) \geq 0$ by property 1.

*The sum.* Let $U$ be a finite set of primes. By property 3 and then the lemma on the dimension of the source,

$$\sum_{\ell\in U}D_X\,\mathrm{err}(\ell)\log\ell = D_X\sum_{\ell\in U}\mathrm{err}(\ell)\log\ell \leq D_X\,\mathrm{err}_0 \leq 2\dim\mathrm{src}\cdot\mathrm{err}_0.$$

The second inequality uses $\mathrm{err}_0 \geq 0$. The right side is $\dim\mathrm{src}\cdot 2\,\mathrm{err}_0$.

*The colength at $\iota$.* Fix $\iota$ above $\ell$, and let $\mathcal{O} = \mathcal{O}_\iota$. Property 4 of the errors gives a natural number $j \leq \mathrm{err}(\ell)\,D_X$ and an $\mathcal{O}$-submodule $S$ of the source forms with $\mathrm{ColengthDvd}(L, S, \ell^j)$, where $L$ is the module of integral ramified source forms. On $S$, every composite lift prime to $\ell$ satisfies the gauge bound of the lemma on integral images. Consider three objects.

- $A : \mathrm{src} \to T$ is the map $s\mathfrak{p}$, seen as an $\mathcal{O}$-linear map.
- $M \subseteq \mathrm{src}$ is the $\mathcal{O}$-module of the ramified forms that are integral at the place of $\iota$. It is the pull back of the integral source forms along the inclusion of $\mathrm{src}$.
- $T_\iota \subseteq T$ is the module of target forms integral at $\iota$.

First, pull back along the inclusion $\mathrm{src} \to$ source forms. The claim is

$$\mathrm{ColengthDvd}\bigl(M,\ A^{-1}(T_\iota),\ \ell^j\bigr).$$

The rule for the pull back needs two facts. A form in $M$ is integral and ramified, so it lies in $L$. A form $\varphi \in M$ with $\varphi \in S$ satisfies the hypothesis of the lemma on integral images, by property 4. So $A\varphi \in T_\iota$, that is $\varphi \in A^{-1}(T_\iota)$.

Second, push forward along $A$. The claim is

$$\mathrm{ColengthDvd}\bigl(A(M),\ T_\iota,\ \ell^j\bigr).$$

The rule for the push forward needs two facts. The inclusion $A(M) \subseteq A(M) + T_\iota$ is clear. The image $A(A^{-1}(T_\iota))$ lies in $T_\iota$.

Third, the family lies in $A(M)$. A form in $\mathrm{src}_{\mathrm{int}}$ is integral at every $\iota$, so $\mathrm{src}_{\mathrm{int}} \subseteq M$. Each $y_i$ lies in $A(\mathrm{src}_{\mathrm{int}}) \subseteq A(M)$.

So at $\iota$ the theorem on index from colength gets the natural number $j \leq D_X\,\mathrm{err}(\ell) = e(\ell)$ and the module $A(M)$. The theorem gives index at most $\dim\mathrm{src}\cdot 2\,\mathrm{err}_0$. $\square$

The module $A(M)$ depends on $\iota$, and so does $j$. The number $e(\ell)$ depends only on $\ell$. This is the form that the index of Section 3 asks for.

**Remark (Formalization).** The pull back and the push forward are needed because the colength of the divisibility lives in the space of all source forms, while the index lives in the target $T$. The source writes $A$ as `(D.normalizedPoincare s).restrictScalars _` and $M$ as `D.integralSourceForms.comap (D.ramifiedSourceForms.subtype.restrictScalars _)`. The module $A^{-1}(T_\iota)$ is `(D.targetLattice.integralVectors ι).comap A`. [Colength](/chapter/twisted-lattices/#colength) states that this proof uses the theorem on index from colength with $M$ the image of a module of integral source forms. That image is $A(M)$.

### All translates

**Theorem (Theorem A (b), small index).** Let $t$ be a finite subset of $\bar G$, and let $y_1, \dots, y_n$ be target forms such that for each $i$ there are $s \in t$ and $\varphi \in \mathrm{src}_{\mathrm{int}}$ with $y_i = s\mathfrak{p}\,\varphi$. Then the family $y$ has index at most

$$\#t\cdot\dim_{\mathbb{C}}\mathrm{src}\cdot 2 f a\log^3 b$$

in the target lattice.

Lean: `New.Data.indexLe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* Write the bound as $\#t\cdot(\dim\mathrm{src}\cdot 2\,\mathrm{err}_0)$. Apply the theorem on the index of a union with $A_s = s\mathfrak{p}(\mathrm{src}_{\mathrm{int}})$ and $\delta = \dim\mathrm{src}\cdot 2\,\mathrm{err}_0$. Its hypothesis is the lemma on the index of one translate, for each $s \in t$. $\square$

### The constants of part (b)

| Constant | Value | Origin |
|---|---|---|
| exponent at $\ell$ | $e(\ell) = D_X\,\mathrm{err}(\ell)$ | colength $j \leq \mathrm{err}(\ell)D_X$, property 4 |
| sum over primes | $D_X\,\mathrm{err}_0$ | property 3 |
| dimension | $D_X \leq 2\dim\mathrm{src}$ | $f/(N-1) \leq b^{-8} \leq 1/2$ |
| one translate | $\dim\mathrm{src}\cdot 2\,\mathrm{err}_0$ | product of the two rows above |
| all translates | $\#t\cdot\dim\mathrm{src}\cdot 2\,\mathrm{err}_0$ | indices add |

**Remark (Formalization).** If $\mathrm{err}(\ell) = 0$, then $j = 0$ and the colength is trivial: every finite family of $L$ is carried into $S$ by a matrix with unit determinant, so $L \subseteq S$, as $S$ is a module and the matrix is invertible. This holds at every prime outside $\mathcal{S}\cup\{N\}$. So only finitely many primes contribute to the index. The source does not use this. It bounds the sum for every finite set $U$ by property 3, which holds for all $U$ at once.

**Example (A trivial bound).** Suppose that $\mathrm{err}(\ell) = 0$ for every $\ell$. Then $e(\ell) = 0$, every $j$ is $0$, and the lemma on the index of one translate gives index at most $0$: there are matrices with unit determinant that carry the family into the integral target forms. In this case $c_B = \prod_{\ell\in\mathcal{S}}\ell^{-\lfloor\mathrm{gain}_\ell\rfloor}$, and the composite lifts are divisible by $\ell^{\mathrm{gain}_\ell}$ on the integral forms. The loss $2\,\mathrm{err}_0$ per dimension pays for the case where the divisibility fails on a part of the integral forms of colength up to $\mathrm{err}(\ell)D_X$.
