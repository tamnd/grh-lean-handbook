---
title: The three inputs
lean:
  - New/UpperBound/Objects/Columns.lean
  - New/UpperBound/Size/ShortColumns.lean
  - New/UpperBound/Size/Estimates.lean
  - New/UpperBound/Divisibility/LocalDivisibility.lean
  - New/UpperBound/Seesaw/SeesawIdentity.lean
  - New/UpperBound/Size/ArchimedeanSize.lean
  - New/Reduction/ShortAndEnough.lean
  - New/Reduction/Data/LevelAndTwists.lean
decls:
  - New.Data.Twist
  - New.Data.IsChainDatum
  - New.Data.compositeLift
  - New.Data.localPrimeSum
  - New.Data.gain
  - New.Data.two_mul_sum_gain_mul_log
  - New.Data.allowedLoss
  - New.Data.exists_err_gaugeLe_compositeLift
  - New.Data.seesaw_identity
  - New.Data.seesawConst
  - New.Data.exists_lowerChain_poincare_eq
  - New.Data.weylNormSq_compositeLift_le
  - New.Data.chainSize
  - New.Data.mainAmount_sub_add_two_mul_sum_gain
  - New.Data.card_aPlaces_mul_excess_le
  - New.Data.chainSize_sub_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The three inputs

The form $\Theta_1(\mathcal{P}\varphi)$ has no direct formula, as $\mathcal{P}\varphi$ is a Poincaré series. The proof replaces $\Theta_1(\mathcal{P}\varphi)$ by a second object, the composite lift $B_\vartheta\varphi$, on which the theta kernels act on $\varphi$ itself. This section states the three results about the composite lift that the proof uses: its divisibility at each prime, its equality with the lower chain (the seesaw identity), and its archimedean size. The later chapters of the volume prove them.

### The composite lift

The composite lift goes along the *upper chain* of hermitian spaces $X_0, \dots, X_m$ over $E$, where $X_0$ carries the source forms and $m = 2\varrho + 2$. Each step is a theta lift, the kernels are taken in pairs, and the data of the chain is one tensor of Schwartz functions. At the end, the forms on $X_m$ are restricted to the subspace $Y_m$, the last space of the *lower chain* $Y_0, \dots, Y_m$ on which the target forms live.

The lifts are twisted by characters. A *tame character* is a character $\vartheta$ of $U(1)(\mathbb{A})$ of weight $0$ whose tame part is trivial outside a finite set $Q(\vartheta)$ of finite places of $E$, of norms prime to $MN$ and disjoint from its complex conjugate. A *twist* is a tame character whose tame part is nontrivial at every place of $Q(\vartheta)$. The trivial twist $1$ has $Q = \emptyset$. In this section and the next, "every twist" means every element of the type of twists. The composite lift and the lower chain of a twist are taken for its underlying tame character.

Lean: `New.Data.Twist` (New/Reduction/Data/LevelAndTwists.lean).

The data of the upper chain come from a finitely supported function $\Psi$ on the set of *translations*: tuples of finite adelic matrices, one for each lift. The *glued tensor* of $\Psi$ is the sum over $x$ of $\Psi(x)$ times the vacuum data translated by $x$. For a twist $\vartheta$, the *composite lift* $B_\vartheta\varphi$ of a source form $\varphi$ is the chain of $m$ lifts from $X_0$ to $X_m$, with the twisting character of $\vartheta$ and the glued tensor of $\Psi$ as data, followed by the restriction to $Y_m$. When $\Psi$ matters, this text writes $B_{\vartheta, \Psi}$.

Lean: `New.Data.compositeLift` (New/UpperBound/Objects/Columns.lean).

Not every $\Psi$ gives a useful lift. The theorems below use the following condition. Let $Q(\vartheta)$ be the finite set of places at which the tame part of $\vartheta$ is not trivial, and let $q$ be the product of their norms.

**Definition (Chain datum).** The function $\Psi$ is a *chain datum* for $\vartheta$ if:

1. every translation in the support of $\Psi$ vanishes at the places prime to $Mq$, and it is admissible for $q$;
2. the values of $\Psi$ are integral away from $q$, with denominator $1$;
3. if $Q(\vartheta)$ is empty, then $\sum_x |\sigma(\Psi(x))| \leq M^{3 f m n_m^2}$ for every automorphism $\sigma$ of $\mathbb{C}$, where $n_m$ is the rank of $X_m$;
4. the glued tensor of $\Psi$ is invariant under the levels of all the spaces $X_j$.

Lean: `New.Data.IsChainDatum` (New/UpperBound/Objects/Columns.lean).

The function $\Psi = 0$ satisfies all four conditions. Its composite lift is $0$. The divisibility below holds for every chain datum. The seesaw identity gives some chain datum, and the remark after it returns to this point.

### Input 1: divisibility prime by prime

The divisibility that the chain should have at a prime $p$ is a sum of local prime sums, one for each lift and each weight. The definition follows the shape of the model case: only the nonsplit primes contribute, and the weight is $\Lambda_K$.

**Definition (The local prime sum).** Let $p$ be a prime, $y$ a real number and $\sigma$ an infinite place of $E$. Put

$$s_p(y, \sigma) = v(\pi_p)\sum_{e \in I_p}\Bigl(\frac{y}{p^e} - \kappa\bigl(u(-p^e)\,\sigma\bigr)\Bigr)_+.$$

Here $v(\pi_p)$ is $\frac12$ if $p = d$ and $1$ otherwise. The set $I_p$ is the set of odd $e \geq 1$ if $p$ is inert in $K$, all $e \geq 1$ if $p = d$, and empty if $p$ splits. The infinite places of $E$ form a group isomorphic to $(\mathbb{Z}/q_1)^\times$, and $u(\nu)$ is the place given by the class of $\nu$ if $\nu$ is prime to $q_1$, and the identity place otherwise. The function $\kappa$ is the weight.

Lean: `New.Data.localPrimeSum` (New/UpperBound/Size/ShortColumns.lean).

**Remark (Formalization).** The sum over $e \in I_p$ is a `tsum` over all $e \in \mathbb{N}$, with the term set to $0$ for $e \notin I_p$. A `tsum` of a family that is not summable is $0$ by convention. For a prime $p$ this junk value does not occur: the weights are at least $1$, so the term is $0$ once $p^e > y$, and the family has finite support. The definition is used only at primes.

**Definition (The gain).** The *gain* at $p$ is

$$\mathrm{gain}_p = m\Bigl(\sum_{\tau \in \Phi_a} s_p(a, \tau) + k\, F(p)\Bigr), \qquad F(p) = \sum_{\tau \in \Phi} s_p(\kappa(\tau), \tau).$$

Lean: `New.Data.gain` (New/UpperBound/Size/ShortColumns.lean).

The two terms match the two terms of the size of the chain in Input 3: a term $s_\infty(a)$ at each $a$-place, where the diagrams of the lifts have $a$ columns of height $1$, and $k$ terms $s_\infty(\kappa(\tau))$ at each place $\tau$, for each of the $m$ lifts. The gain is $0$ if $p$ splits in $K$ or $p \geq x_1$.

The gains add up to the prime sums $s_{\mathrm{fin}}$ of the main amount.

**Lemma (Sum of the gains).** With $\mathcal{S}$ the set of primes $p < x_1$ that do not split in $K$,

$$2\sum_{p \in \mathcal{S}}\mathrm{gain}_p\log p = m\sum_{\tau\in\Phi_a}s_{\mathrm{fin}}(a, \tau) + m k\sum_{\tau\in\Phi}s_{\mathrm{fin}}(\kappa(\tau), \tau).$$

Lean: `New.Data.two_mul_sum_gain_mul_log` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* For $e \in I_p$ the weight $\Lambda_K(p^e) = \Lambda(p^e)(1 - \chi_K(p^e))$ equals $2 v(\pi_p)\log p$: it is $2\log p$ for odd $e$ at an inert $p$, and $\log d$ at $p = d$. For $e \notin I_p$ it is $0$. So $2\log p \cdot s_p(y, \sigma)$ is the part of $s_{\mathrm{fin}}(y, \sigma)$ at the powers of $p$. The gain is $0$ at split primes, so the sum may run over all primes below $x_1$, and the prime powers $\nu \geq x_1$ give no term in $s_{\mathrm{fin}}$. $\square$

The factor $2$ is the factor $2$ of the model case: an inert prime $p$ has norm $p^2$, and $\Lambda_K(p) = 2\log p$. It is also the factor that the square $c_B^2$ cancels in Section 4.

**Theorem (Divisibility of the composite lift).** There is a function $\mathrm{err} : \mathbb{N} \to \mathbb{R}$ with the following properties.

1. $\mathrm{err}(p) \geq 0$ for every $p$.
2. If $p \neq N$, and $p$ splits in $K$ or $p \geq x_1$, then $\mathrm{err}(p) = 0$.
3. For every finite set $U$ of natural numbers, $\sum_{p\in U}\mathrm{err}(p)\log p \leq f a \log^3 b$.
4. Let $p$ be a prime and $\iota_p$ a $p$-adic place of $\mathbb{C}$. Let $R$ be the ring of complex numbers that $\iota_p$ sends to $p$-adic integers, and let $L$ be the $R$-module of ramified source forms that are integral at $\iota_p$. Then there are a natural number $l \leq \mathrm{err}(p) D_X$ and an $R$-submodule $S \subseteq L$ whose colength in $L$ divides $p^l$, such that the following holds. For every twist $\vartheta$ with $\mathrm{Nm}\,Q(\vartheta)$ prime to $p$, every chain datum $\Psi$ for $\vartheta$ and every $\varphi \in S$, every value of $B_{\vartheta,\Psi}\varphi$ has $\iota_p$-adic gauge at most $p^{\mathrm{err}(p) - \mathrm{gain}_p}$.

Lean: `New.Data.exists_err_gaugeLe_compositeLift` (New/UpperBound/Divisibility/LocalDivisibility.lean).

The gauge is measured against the Weyl lattice, so the last condition says that $B_{\vartheta,\Psi}\varphi$ is divisible by $p^{\mathrm{gain}_p - \mathrm{err}(p)}$, with a real exponent. At a split prime $p \neq N$, and at $p \geq x_1$ with $p \neq N$, the gain and the error are $0$. Then $l = 0$, so $S = L$, and the statement says that the composite lift of every integral ramified form is integral at $\iota_p$. The same $S$ serves every twist of level prime to $p$ and every chain datum. Part (b) of Theorem A needs this, as the index is defined by all twists at once.

The proof sets $\mathrm{err}$ equal to the *allowed loss*.

**Definition (The allowed loss).** For a natural number $p$,

$$\mathrm{allowedLoss}(p) = \begin{cases} 2 f \log^2 b\cdot \dfrac{a}{p}\cdot \mu_p & \text{if } p \in \mathcal{S},\\ 2 m f b & \text{if } p = N,\\ 0 & \text{otherwise,}\end{cases}$$

where $\mu_p = m$ if $p \equiv \pm 1 \bmod m$, and $\mu_p = 1$ otherwise.

Lean: `New.Data.allowedLoss` (New/UpperBound/Size/Estimates.lean).

Property 3 for this witness is a bound for a harmonic sum. The loss at $N$ comes from the lift at the level, where the source uses the operator $U_p^{m/2}$ ([divisibility prime by prime](/chapter/divisibility/)).

**Remark (Formalization).** Theorem A uses the function $\mathrm{err} = $ `New.Data.divisibilityError`, chosen from this theorem by `choose`. As Section 1 notes, nothing about $\mathrm{err}$ is used except the four properties. The lemma `New.Data.exists_colengthDvd_gaugeLe_divisibilityError` of New/Reduction/ShortAndEnough.lean restates property 4 for this choice, and it drops the conjunct $S \subseteq L$. The proof of part (b) in Section 4 uses only the colength and the gauge bound. The witness $\mathrm{allowedLoss}$ is visible only inside the proof of the theorem.

### Input 2: the seesaw identity

The seesaw identity connects the lower chain of the Poincaré series to the upper chain of the source form. Let $t$ be a linear form on the values of forms on $X_0$, and let $g$ be an archimedean point of the unitary group of $Y_0$. The Poincaré map $\mathcal{P} = \mathcal{P}_{g,t}$ sends a form $\varphi$ on $X_0$ to the form on $Y_0$ that represents the Bessel period of $\varphi$, defined by $g$ and $t$, in the Petersson inner product. For a twist $\vartheta$, the lower chain $\iota_\vartheta$ is the chain of $m$ theta lifts from $Y_0$ to $Y_m$ with the twisting character of $\vartheta$.

**Theorem (Seesaw identity).** Let $t$ and $g$ be as above. There is $c \in \mathbb{C}^\times$ such that every twist $\vartheta$ has a chain datum $\Psi$ with

$$\iota_\vartheta(\mathcal{P}\varphi) = c\cdot B_{\vartheta,\Psi}\varphi$$

for every ramified source form $\varphi$.

Lean: `New.Data.seesaw_identity` (New/UpperBound/Seesaw/SeesawIdentity.lean).

The classical seesaw identity equates two inner products for dual pairs $(G, H')$ and $(G', H)$ with $G \subseteq G'$ and $H \subseteq H'$. Here the inner product with the Poincaré series is unfolded across the chain of lifts into a sum over the cosets of an admissible lattice. [The seesaw identity, part 1](/chapter/seesaw-identity-1/) unfolds the inner product. [Part 2](/chapter/seesaw-identity-2/) cuts the sum into classes and assembles the chain datum.

The constant $c$ does not depend on $\vartheta$, but $\Psi$ does. For Theorem A the source fixes $t$ and $g$ to the Bessel form and the Bessel point of the data, and it names the constant.

**Definition (The seesaw constant).** The *seesaw constant* $c_{ss} \in \mathbb{C}^\times$ is the constant $c$ of the seesaw identity for the Bessel form and the Bessel point.

Lean: `New.Data.seesawConst` (New/Reduction/ShortAndEnough.lean).

With $z = \mathcal{P}(c_{ss}^{-1}\varphi)$ the identity has constant $1$.

**Lemma (Seesaw identity for $c_{ss}^{-1}\mathcal{P}$).** Every twist $\vartheta$ has a chain datum $\Psi$ such that $\iota_\vartheta\bigl(\mathcal{P}(c_{ss}^{-1}\varphi)\bigr) = B_{\vartheta,\Psi}\varphi$ for every ramified source form $\varphi$.

Lean: `New.Data.exists_lowerChain_poincare_eq` (New/Reduction/ShortAndEnough.lean).

**Remark (Formalization).** The proof of the seesaw identity first finds a number $c_0$ and an admissible combination with coefficient $C$ and denominator $d = R^{2m}$, where $R = M^{f n_m^2}$. Then it puts $u = \mathrm{normUnit}(c_0 C/d)$ and $c = u^{-1}$. The function `normUnit` sends a nonzero number $x$ to the unit $x^{-1}$, so that $x \cdot \mathrm{normUnit}(x) = 1$, and sends $0$ to $1$. The docstring of `New.Seesaw.IsAdmissibleCombination.normUnit_smul` says this: the factor is $d/(c_0 C)$, or $1$. So $u = d/(c_0 C)$ and $c = c_0 C/d$ when $c_0 C \neq 0$, and $c = 1$ when $c_0 C = 0$. In the second case the source notes that $u c_0$ times the seesaw datum is $0$. The chain datum $\Psi$ is built so that its glued tensor is this product, so the glued tensor is $0$, the composite lift on the right is $0$, and the identity says that the left side is $0$ too. The identity then carries no information. The type $\mathbb{C}^\times$ of $c_{ss}$ says only that the chosen number is a unit. The rescaling by $d$ is matched to condition 3 of a chain datum: $R^{2m}\cdot R^{2\varrho + 2} = M^{f n_m^2(2m + m)} = M^{3 f m n_m^2}$, as $m = 2\varrho + 2$. The constant $c_{ss}$ is chosen by `choose`. Theorem A is a pair of upper bounds, and it holds for the chosen constant, whatever it is. The nonvanishing that the argument needs comes from the determinant side, as [Theorems A, B and C](/chapter/theorems-a-b-c/#how-the-three-theorems-fit-together) lists: the injectivity of the lower chain at the level (`New.Data.injective_lift_targetLattice`), the scalars of the chains in a triangle of lifts (`New.Exchange.IsTriangle.ne_zero_of_chainCommutes`; the form for one square, `ne_zero_of_squareCommutes`, is never applied in the source), and the Hecke ratios (`New.Data.CriticalPair.ratio_ne_zero`). No step of the main inequality divides by $c_0 C/d$.

### Input 3: the archimedean size

The size of the composite lift is computed lift by lift. The theta kernel of one lift, applied to a form whose values are bounded, gives a form whose values are bounded by the size of a derivative of order $\kappa(\tau)$ at each infinite place $\tau$. This size is $s_\infty(\kappa(\tau)) = \log\kappa(\tau)! + \kappa(\tau)\log(M/\Omega)$. The main term of the size of the whole chain is the following.

**Definition (The size of the chain).** $\mathrm{chainSize} = m\bigl(\#\Phi_a\, s_\infty(a) + k\sum_{\tau\in\Phi}s_\infty(\kappa(\tau))\bigr)$.

Lean: `New.Data.chainSize` (New/UpperBound/Size/ArchimedeanSize.lean).

The restriction from $X_m$ to $Y_m$ saves $a\log N$ at each $a$-place. The saving and the main terms fit with the prime sums as follows.

**Lemma (The prime sums cancel).** $\mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal{S}}\mathrm{gain}_p\log p = m\,\#\Phi_a\, s_{\mathrm{main}} + m k\sum_{\tau\in\Phi}s_\infty(\kappa(\tau))$.

Lean: `New.Data.mainAmount_sub_add_two_mul_sum_gain` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* Substitute the lemma on the sum of the gains and the definitions of $\mathrm{mainAmount}$ and $\mathrm{rem}$. The terms $s_{\mathrm{fin}}$ cancel. $\square$

**Lemma (The level compensates the excess).** $\#\Phi_a\bigl(m(s_\infty(a) - s_{\mathrm{main}}) - a\log N\bigr) \leq 32 f a\log b$.

Lean: `New.Data.card_aPlaces_mul_excess_le` (New/UpperBound/Size/ArchimedeanSize.lean).

**Lemma (Size of the chain).** $\mathrm{chainSize} - \#\Phi_a\, a\log N \leq \mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal{S}}\mathrm{gain}_p\log p + 32 f a\log b$.

Lean: `New.Data.chainSize_sub_le` (New/UpperBound/Size/ArchimedeanSize.lean).

*Proof.* By the lemma on the cancellation, the right side minus $32 f a\log b$ is $m\#\Phi_a s_{\mathrm{main}} + m k\sum_\tau s_\infty(\kappa(\tau))$. The left side is $m\#\Phi_a s_\infty(a) + mk\sum_\tau s_\infty(\kappa(\tau)) - \#\Phi_a a\log N$. The difference is the excess of the previous lemma. $\square$

So the expression $\mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\sum_p\mathrm{gain}_p\log p$ is, up to the error, an archimedean quantity: the size of the chain less the saving of the restriction.

**Theorem (Size of the composite lift).** Let $\Psi$ be a chain datum for the trivial twist, let $\sigma$ be an automorphism of $\mathbb{C}$, let $\varphi$ be a source form, and let $B$ be real. Suppose that every value of $\sigma\circ\varphi$ has squared Weyl norm at most $e^B$. Then every value of $\sigma\circ B_{1,\Psi}\varphi$ has squared Weyl norm at most $\exp(B + \beta)$, where

$$\beta = \mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\sum_{p\in\mathcal{S}}\mathrm{gain}_p\log p + f a\log^3 b.$$

Lean: `New.Data.weylNormSq_compositeLift_le` (New/UpperBound/Size/ArchimedeanSize.lean).

The theorem holds only for the trivial twist. That is enough for part (a) of Theorem A, which measures the size by $\Theta_1$ alone. The theorem has no integrality hypothesis on $\varphi$. The proof adds the bounds of the $m$ kernels, and the lemma on the size of the chain gives the exponent. The error terms of the kernels are powers of $x$, and they and the term $32 f a\log b$ are absorbed in $f a\log^3 b$. [The archimedean size](/chapter/archimedean-size/) proves the theorem.
