---
title: The normalized map and its two chosen constants
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/UpperBound/Divisibility/LocalDivisibility.lean
  - New/UpperBound/Seesaw/SeesawIdentity.lean
decls:
  - New.Data.exists_err_gaugeLe_compositeLift
  - New.Data.divisibilityError
  - New.Data.sum_divisibilityError_mul_log_le
  - New.Data.invGainFactor
  - New.Data.log_invGainFactor_le
  - New.Data.seesaw_identity
  - New.Data.seesawConst
  - New.Data.normalizedPoincare
  - New.Data.integralRamified
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The normalized map and its two chosen constants

This section defines the maps $s\mathfrak{p}$ of Theorems A and B. The map $\mathfrak{p}$ is a Poincaré map, projected to the good part and scaled by two numbers. The first divides out the divisibility of the lifts at the small primes. The second is the constant of the seesaw identity. Both come from existence theorems by `choose`.

### The idea

Let $\varphi$ be a source form and let $z = \mathcal{P}\varphi$ be its Poincaré series. The chain of lifts of $z$ for the trivial twist is a form on a larger group. Volume 9 proves two facts about it. Its values are small at every archimedean place: a bound $\exp(\mathrm{main} - m\,\mathrm{rem} + 2\sum_p \mathrm{gain}_p \log p + \dots)$ for the squared norms. Its values are divisible at each small prime $p$ that does not split in $K$: they lie in $p^{\mathrm{gain}_p}$ times the integral forms, up to an error. So the right normalization multiplies by the product of the $p^{-\mathrm{gain}_p}$. The images stay integral, and the term $2\sum_p \mathrm{gain}_p \log p$ in the size cancels. This is the first cancellation of the argument.

### The divisibility errors

The gain $\mathrm{gain}_p$ at a prime $p$ is a weighted local prime sum, defined in [the archimedean size](/chapter/archimedean-size/). It is $0$ if $\chi_K(p) = 1$ or $p \geq x_1$. Let $\mathcal{S} = \{p < x_1 : p \text{ prime}, \chi_K(p) \neq 1\}$ be the set of small nonsplit primes. For a twist $\vartheta$ and a chain datum $\Psi$ of $\vartheta$, the *composite lift* $B_\vartheta\varphi$ of a source form $\varphi$ is the upper chain of $m$ theta lifts with the glued tensor of $\Psi$ as its Schwartz data ([the objects of the upper bound](/chapter/upper-bound-objects/)).

**Theorem (Divisibility of the composite lift).** There are real numbers $\mathrm{err}(p)$, one for each natural number $p$, with these properties.

1. $\mathrm{err}(p) \geq 0$ for every $p$.
2. If $p \neq N$, and $\chi_K(p) = 1$ or $x_1 \leq p$, then $\mathrm{err}(p) = 0$.
3. $\sum_{p \in U} \mathrm{err}(p) \log p \leq f a \log^3 b$ for every finite set $U$.
4. For every prime $p$ and every embedding $\iota_p$ of $\mathbb{C}$ in $\mathbb{C}_p$, there are a natural number $l \leq \mathrm{err}(p) \cdot D_X$ and a submodule $S$ of the integral ramified source forms, over the ring of numbers that $\iota_p$ sends to $p$-adic integers, such that $S$ has colength dividing $p^l$ in the integral ramified source forms, and such that $B_\vartheta \varphi$ has valuation at least $\mathrm{gain}_p - \mathrm{err}(p)$ at every point, for all $\varphi \in S$, all twists $\vartheta$ with $\mathrm{Nm}\,Q(\vartheta)$ prime to $p$, and all chain data $\Psi$ of $\vartheta$.

Lean: `New.Data.exists_err_gaugeLe_compositeLift` (New/UpperBound/Divisibility/LocalDivisibility.lean).

Volume 9 proves this theorem in [divisibility prime by prime](/chapter/divisibility/). The proof takes the allowed losses of [the archimedean size](/chapter/archimedean-size/) as the numbers $\mathrm{err}(p)$. They are nonzero only at the small nonsplit primes and at $N$.

**Definition (The divisibility errors).** The function $p \mapsto \mathrm{err}(p)$, from $\mathbb{N}$ to $\mathbb{R}$, is a choice of the numbers of the theorem on the divisibility of the composite lift.

Lean: `New.Data.divisibilityError` (New/Reduction/ShortAndEnough.lean).

**Lemma (The properties of the errors).** The numbers $\mathrm{err}(\ell)$ satisfy properties 1 to 3 of the theorem, and for every prime $\ell$ and $\ell$-adic place of $\mathbb{C}$ there are $j \leq \mathrm{err}(\ell) \cdot D_X$ and a module $S$ of source forms such that the integral ramified source forms are carried into $S$ by a square matrix with determinant dividing $\ell^j$, and $B_\vartheta\varphi$ has valuation at least $\mathrm{gain}_\ell - \mathrm{err}(\ell)$ for $\varphi \in S$, for the twists and chain data of property 4.

Lean: `New.Data.divisibilityError_nonneg`, `New.Data.divisibilityError_eq_zero`, `New.Data.sum_divisibilityError_mul_log_le`, `New.Data.exists_colengthDvd_gaugeLe_divisibilityError` (New/Reduction/ShortAndEnough.lean).

*Proof.* Each part is a part of the specification of the chosen function. $\square$

**Remark (Formalization).** The definition reads `D.exists_err_gaugeLe_compositeLift.choose`. In Lean, `choose` applied to a proof of $\exists\, e, P(e)$ gives some $e$ with $P(e)$, and nothing else is known about it. Here the proof of existence names a witness, the allowed losses, but the definition does not unfold to it: the later proofs use only the four properties, through the lemmas above. So $\mathrm{err}(p)$ has no formula. The choice is harmless: every statement of this chapter holds for every function with the four properties.

### The gain factor

**Definition (The gain exponents and the gain factor).** For a natural number $\ell$ let $g_\ell = \lfloor \mathrm{gain}_\ell - \mathrm{err}(\ell) \rfloor \in \mathbb{Z}$. The gain factor is the rational number

$$c_B = \prod_{\ell \in \mathcal{S} \cup \{N\}} \ell^{-g_\ell}.$$

Lean: `New.Data.gainExponent`, `New.Data.invGainFactor` (New/Reduction/ShortAndEnough.lean).

Each $\ell$ in $\mathcal{S} \cup \{N\}$ is prime, so $c_B > 0$ (`New.Data.invGainFactor_pos`). For a prime $\ell$, the $\ell$-adic absolute value of $c_B$ is $|\ell|_\ell^{-g_\ell}$. This holds also for $\ell \notin \mathcal{S} \cup \{N\}$, since then $\mathrm{gain}_\ell = \mathrm{err}(\ell) = 0$ and $g_\ell = 0$ (`New.Data.norm_invGainFactor`).

**Lemma (The logarithm of the gain factor).** We have

$$\log c_B \leq -\sum_{\ell \in \mathcal{S}} \mathrm{gain}_\ell \log \ell + f a \log^3 b + b.$$

Lean: `New.Data.log_invGainFactor_le` (New/Reduction/ShortAndEnough.lean).

*Proof.* Write $U = \mathcal{S} \cup \{N\}$. Then $\log c_B = \sum_{\ell \in U} (-g_\ell) \log \ell$. Since $\lfloor y \rfloor > y - 1$, we have $-g_\ell \leq -\mathrm{gain}_\ell + \mathrm{err}(\ell) + 1$, and $\log \ell \geq 0$. So

$$\log c_B \leq -\sum_{\ell \in U} \mathrm{gain}_\ell \log \ell + \sum_{\ell \in U} \mathrm{err}(\ell) \log \ell + \sum_{\ell \in U} \log \ell.$$

The level $N$ is at least $x_1$, so $\mathrm{gain}_N = 0$, and the first sum runs over $\mathcal{S}$ only. The second sum is at most $f a \log^3 b$ by property 3. For the third sum, each $\ell \in \mathcal{S}$ has $\log \ell \leq \ell < x_1$, and $\mathcal{S}$ has at most $\lceil x_1 \rceil$ elements. So the third sum is at most $\lceil x_1 \rceil x_1 + \log N$, and this is at most $b$ by the sizes (`New.Data.sum_log_smallNonsplitPrimes_union_le`). $\square$

The term $b$ is the cost of the integer parts. It is far below $f a \log^3 b \geq a = x b$.

### The seesaw constant

The second constant comes from the seesaw identity of Volume 9. Let $\mathcal{P}_{g,\omega}$ be the Poincaré map from forms on the space $X_0$ to forms on $Y_0$, built from a linear form $\omega$ on the values of forms on $X_0$ and an archimedean point $g$ of $U(Y_0)$. For a twist $\vartheta$, the *lower chain* $\iota_\vartheta$ is the composite of the $m$ lifts from forms on $Y_0$ to forms on $Y_m$.

**Theorem (The seesaw identity).** For every linear form $\omega$ and every archimedean point $g$ there is a number $c \in \mathbb{C}^\times$ such that every twist $\vartheta$ has a chain datum $\Psi$ with

$$\iota_\vartheta(\mathcal{P}_{g,\omega}\varphi) = c \cdot B_\vartheta\varphi$$

for every ramified source form $\varphi$, where $B_\vartheta$ is the composite lift with the datum $\Psi$.

Lean: `New.Data.seesaw_identity` (New/UpperBound/Seesaw/SeesawIdentity.lean).

Volume 9 proves it in [the seesaw identity, part 1](/chapter/seesaw-identity-1/) and [part 2](/chapter/seesaw-identity-2/). The identity is the classical seesaw principle of theta correspondences, applied $m$ times: a lift along the lower chain of a Poincaré series is a lift along the upper chain of the form itself.

**Definition (The seesaw constant).** The seesaw constant $c_{ss} \in \mathbb{C}^\times$ is a choice of the number $c$ of the seesaw identity for the linear form and the archimedean point of the Bessel data of Volume 10.

Lean: `New.Data.seesawConst` (New/Reduction/ShortAndEnough.lean).

**Remark (Formalization).** The seesaw constant is chosen by `choose`, like the numbers $\mathrm{err}(p)$. Its type is the group of units $\mathbb{C}^\times$, so it is nonzero by its type, and $c_{ss}^{-1}$ makes sense. This does not make the theta integrals behind it nonzero. In the proof of the seesaw identity the constant is $u^{-1}$ with $u = \mathrm{normUnit}(c_0 C / d)$, where $c_0$ comes from the unfolding of the lower chain, $C$ comes from the admissible combination of the seesaw datum, and $d$ is a positive integer, a power of the number of residue matrices. The function `normUnit` of Mathlib sends a nonzero element $a$ of a field to $a^{-1}$, and it sends $0$ to $1$. So if $c_0 C/d \neq 0$, then $c = c_0C/d$. If $c_0 C / d = 0$, then $u = 1$, the datum $\Psi$ has glued tensor $u c_0$ times the seesaw datum, which is $0$, and the identity holds with $c = 1$. In that case it carries no information. Theorem A does not need more. It uses the identity only to bound sizes and divisibility from above, and these bounds hold for any constant that satisfies the identity. The nonvanishing that the argument needs comes back on the determinant side, in Theorem C (Section 6).

### The normalized map

Let $\bar G$ act on the forms on $Y_0$, let $e_0$ be the central idempotent of $\mathbb{C}[\bar G]$ that projects onto the good part, and let $\mathcal{P} = \mathcal{P}_{g,\omega}$ be the Poincaré map for the Bessel data. The *good Poincaré map* of $s \in \bar G$ is $\#\bar G \cdot e_0\, s\, \mathcal{P}$, from all source forms to the target ([Theorem](/decl/New.Data.isSpread_goodPoincare/)). The factor $\#\bar G$ makes the coefficients of $\#\bar G \cdot e_0$ algebraic integers, so that the projection keeps integrality.

**Definition (The normalized Poincaré map).** For $s \in \bar G$, the map $s\mathfrak{p} : \mathrm{src} \to T$ is

$$s\mathfrak{p}(\varphi) = c_B \cdot \#\bar G \cdot e_0\, s\, \mathcal{P}(c_{ss}^{-1}\varphi).$$

Lean: `New.Data.normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

Three facts follow from the definition. First, $s\mathfrak{p}$ is the translate by $s$ of $\mathfrak{p} = 1\mathfrak{p}$, as $e_0$ is central (`New.Data.coe_normalizedPoincare`). Second, the range of $s\mathfrak{p}$ is the image of $\mathrm{src}$ under the good Poincaré map of $s$, as $c_B$ and $c_{ss}^{-1}$ are nonzero (`New.Data.range_normalizedPoincare`). Third, the positive rational factor $c_B$ multiplies each squared norm by $c_B^2$: for every $\sigma$,

$$\|\Theta_1(s\mathfrak{p}\varphi)\|_\sigma^2 = \exp(2\log c_B) \cdot \|\Theta_1(\#\bar G\, e_0\, s\,\mathcal{P}(c_{ss}^{-1}\varphi))\|_\sigma^2,$$

since $\sigma$ fixes the rational number $c_B$ (`New.Data.normSqAt_normalizedPoincare`). The seesaw identity gives, for every twist $\vartheta$, a chain datum $\Psi$ with $\iota_\vartheta(\mathcal{P}(c_{ss}^{-1}\varphi)) = B_\vartheta\varphi$ for every $\varphi \in \mathrm{src}$ (`New.Data.exists_lowerChain_poincare_eq`). This is the form in which Theorem A uses it.

**Definition (The integral source forms).** The set $\mathrm{src}_{\mathrm{int}}$ is the set of $\varphi \in \mathrm{src}$ that are integral at every $\iota$, for every prime $\ell$ and every isomorphism $\iota : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$.

Lean: `New.Data.integralRamified` (New/Reduction/ShortAndEnough.lean).

This is a set, not a subspace. Theorem A (a) says that its short elements span $\mathrm{src}$.
