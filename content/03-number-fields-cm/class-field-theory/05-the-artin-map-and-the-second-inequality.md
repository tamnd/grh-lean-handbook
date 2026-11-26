---
title: The Artin map and the second inequality
lean:
  - Lib/ClassField/Local/ArtinMap.lean
  - Lib/ClassField/Global/ArtinMap.lean
  - Lib/ClassField/HeckeL/EulerProduct.lean
  - Lib/ClassField/HeckeL/ContinuationAtOne.lean
  - Lib/ClassField/HeckeL/IdelicThetaSum.lean
  - Lib/ClassField/Global/AlbertBrauerHasseNoether.lean
decls:
  - New.artinAt
  - New.artinMap
  - New.abelianLift_artinMap_eq_finprod_of_exists
  - New.abelianLift_artinMap_eq_finprod
  - New.continuous_artinMap
  - New.artinMap_locIdele
  - New.IsPlaceOver.abelianLift_artinAt_of_inertiaGroup_le_ker
  - New.IsHeckeOfType
  - New.heckeCoeff
  - New.eulerProd
  - New.HasPrimeDensity
  - New.hasPrimeDensity_card_degree_one
  - New.IsHeckeOfType.exists_analyticAt_one_eulerProd
  - New.IsHeckeOfType.exists_hasPrimeDensity
  - New.IsHeckeOfType.eulerProd_ne_zero
  - New.exists_hasPrimeDensity_addChar_uniformizer
  - New.second_inequality
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Artin map and the second inequality

This section builds the global Artin map on the finite ideles, and then proves the second inequality by Hecke $L$-functions. The analytic input is small: a partial Hecke $L$-function of a nontrivial character, on the real line near $s = 1$.

### The global Artin map

Fix a number field $K$, embedded in $\Omega$, and a group $\Gamma$ with `IsProGalois Γ K Ω`. Write $\Gamma^{\mathrm{ab}}$ for the topological abelianisation.

**Definition (Local symbol).** For a finite place $v$ of $K$, `artinAt Γ v` is the composite of `localArtin Γ (placeOver v) v` with the map $D^{\mathrm{ab}} \to \Gamma^{\mathrm{ab}}$ induced by the inclusion of the decomposition group $D$ of `placeOver v`.
Lean: `New.artinAt` (Lib/ClassField/Local/ArtinMap.lean).

The map into $\Gamma^{\mathrm{ab}}$ does not depend on the choice of the place over $v$, since two choices are conjugate and conjugation is trivial on $\Gamma^{\mathrm{ab}}$. The source does not need this fact, because it uses only the chosen place.

**Definition (Global Artin map).** `artinMap Γ` is a homomorphism $f : (\mathbb{A}_{K,f})^\times \to \Gamma^{\mathrm{ab}}$, chosen by `Classical.epsilon`, such that for every continuous character $\chi$ of $\Gamma$ and every finite idele $a$,
$$\chi(f(a)) = \prod_{v} \chi(\operatorname{artinAt}_v(a_v)),$$
a product in $\mathbb{Q}/\mathbb{Z}$ written multiplicatively, with Mathlib's `finprod`.
Lean: `New.artinMap` (Lib/ClassField/Local/ArtinMap.lean).

**Remark (Formalization).** Mathlib's `finprod` is $1$ when the set of factors different from $1$ is infinite. So the defining property has a junk case. The next theorem removes it: for each $\chi$ and $a$, almost every factor is $1$. The docstring of `artinMap` says that its file does not prove that such an $f$ exists, and the lemma `abelianLift_artinMap_eq_finprod_of_exists` there has the existence as a hypothesis. The existence is proved in a later file, by the next theorem. Some notes on the source say that the existence is not proved. That is not correct at the pinned commit.
Lean: `New.abelianLift_artinMap_eq_finprod_of_exists` (Lib/ClassField/Local/ArtinMap.lean).

**Theorem (Product formula).** For every continuous character $\chi$ of $\Gamma$ and every finite idele $a$, $\chi(\operatorname{artinMap}(a)) = \prod_v \chi(\operatorname{artinAt}_v(a_v))$.
Lean: `New.abelianLift_artinMap_eq_finprod` (Lib/ClassField/Global/ArtinMap.lean).

*Proof.* First, the product is finite. The kernel of $\chi$ is open, so only finitely many places are ramified for $\chi$. At an unramified place where $a_v$ is a unit, the local symbol lies in the image of inertia, so $\chi$ kills it. Second, the map $s : a \mapsto (\chi \mapsto \prod_v \chi(\operatorname{artinAt}_v(a_v)))$ is a homomorphism from the ideles to the additive maps from characters to $\mathbb{Q}/\mathbb{Z}$. The duality lemma `New.QZChar.exists_hom_abelianLift_eq` gives a homomorphism $f$ with $\chi(f(a)) = s(a)(\chi)$. So the existence hypothesis holds, and the lemma with that hypothesis applies. $\square$

**Lemma (Continuity and local components).** `artinMap Γ` is continuous, and $\operatorname{artinMap}(\operatorname{locIdele}_v(x)) = \operatorname{artinAt}_v(x)$ for $x \in K_v^\times$.
Lean: `New.continuous_artinMap` (Lib/ClassField/Global/ArtinMap.lean).
Lean: `New.artinMap_locIdele` (Lib/ClassField/Global/ArtinMap.lean).

**Lemma (Unramified symbols).** Let $A$ lie over $v$, let $\chi$ vanish on the inertia group of $A$, and let $\varphi$ be a $q_v$-Frobenius at $A$. For $x \in K^\times$,
$$\chi(\operatorname{artinAt}_v(x)) = -\operatorname{ord}_v(x)\, \chi(\varphi).$$
Lean: `New.IsPlaceOver.abelianLift_artinAt_of_inertiaGroup_le_ker` (Lib/ClassField/Global/ArtinMap.lean).

The Lean statement writes the factor as `(v.valuation K x).log`, which is $-\operatorname{ord}_v(x)$ for the multiplicative valuation of Mathlib. So a uniformiser goes to $\varphi^{-1}$ on unramified characters: the geometric convention of Section 4.

**Example (The Artin map for $\mathbb{Q}(i)/\mathbb{Q}$).** Let $K = \mathbb{Q}$ and let $\chi$ be the character of order $2$ with kernel $\operatorname{Gal}(\Omega/\mathbb{Q}(i))$. For an odd prime $p$, $\chi(\varphi_p) = 0$ if $p \equiv 1 \bmod 4$ and $\tfrac12$ if $p \equiv 3 \bmod 4$. So, for the idele $\operatorname{locIdele}_p(p)$, $\chi(\operatorname{artinMap}) = -\chi(\varphi_p) = \chi(\varphi_p)$, and the sign convention is invisible for characters of order $2$.

### Hecke characters and Euler products

**Definition (Hecke character of a type).** Let $n$ give an integer $n_w$ to each infinite place $w$ of $K$, and let $\Phi_w$ be the chosen complex embedding at $w$. A homomorphism $\psi : (\mathbb{A}_{K,f})^\times \to \mathbb{C}^\times$ is *of type* $n$ if its kernel is open and
$$\psi(x) \prod_w \left(\frac{\Phi_w(x)}{|\Phi_w(x)|}\right)^{n_w} = 1 \qquad (x \in K^\times).$$
Lean: `New.IsHeckeOfType` (Lib/ClassField/HeckeL/EulerProduct.lean).

So $\psi$ is the finite part of a unitary Hecke character whose infinity component is $z \mapsto (z/|z|)^{-n_w}$ at each $w$. Characters of finite order trivial on the totally positive elements are of this kind with $n_w \in \{0, 1\}$ at real places and $0$ at complex places.

**Definition (Coefficients).** For a finite set $S$, `heckeCoeff ψ S` sends $v \notin S$ to $\psi(\operatorname{locIdele}_v(\varpi_v))$ and $v \in S$ to $0$.
Lean: `New.heckeCoeff` (Lib/ClassField/HeckeL/EulerProduct.lean).

**Definition (Euler product).** For $a : \{\text{finite places}\} \to \mathbb{C}$, `eulerProd a` is the function of real $s$ given by the limit within $(1, \infty)$ of
$$s \mapsto \exp\Big(-\sum_v \log(1 - a_v q_v^{-s})\Big).$$
Lean: `New.eulerProd` (Lib/ClassField/HeckeL/EulerProduct.lean).

**Remark (Formalization).** Three junk values hide here. First, `eulerProd` is Mathlib's `extendFrom (Ioi 1)`. At $s > 1$ with $|a_v| \leq 1$ it is the product, and at $s = 1$ it is the limit from the right if that limit exists. If the limit does not exist, the value is an arbitrary choice. For $s < 1$ the value has no meaning. Second, the sum is Mathlib's `tsum`, which is $0$ for a divergent series. For $s > 1$ the series converges absolutely, so this does not occur there. Third, `heckeCoeff` is not $0$ at a ramified place outside $S$: it is $\psi(\varpi_v)$ for the chosen uniformiser. So `eulerProd (heckeCoeff ψ S)` is the partial $L$-function only when $\psi$ is unramified outside $S$. The theorems below hold for every finite $S$. With a ramified $v \notin S$, the factor at $v$ is a finite nonzero factor, analytic near $s = 1$, so it changes neither analyticity nor vanishing.

**Definition (Prime density).** The family $a$ has *prime density* $l \in \mathbb{C}$ if, for real $s \to 1^+$,
$$\sum_{v :\, q_v \text{ prime}} a_v q_v^{-s} = -l \log(s - 1) + O(1),$$
with the series convergent for $s > 1$ near $1$.
Lean: `New.HasPrimeDensity` (Lib/ClassField/HeckeL/EulerProduct.lean).

Only the primes of degree one count. This is no loss for densities, since the primes of higher degree give a bounded sum. The constant family $c$ has density $c$, from the simple pole of the Dedekind zeta function. The source also proves the relative form.

**Lemma (Primes of degree one in an extension).** Let $L/K$ be an extension of number fields and $c \in \mathbb{C}$. The family that sends $v$ to $c$ times the number of places $w$ of $L$ over $v$ with $q_w = q_v$ has prime density $c$.
Lean: `New.hasPrimeDensity_card_degree_one` (Lib/ClassField/HeckeL/EulerProduct.lean).

### Continuation to $s = 1$

**Theorem (Continuation at one).** Let $\psi$ be of type $n$, $\psi \neq 1$, and $S$ finite. There is a function $F$, real analytic at $1$, with $F(s) = \operatorname{eulerProd}(\operatorname{heckeCoeff} \psi\, S)(s)$ for all $s > 1$ near $1$.
Lean: `New.IsHeckeOfType.exists_analyticAt_one_eulerProd` (Lib/ClassField/HeckeL/ContinuationAtOne.lean).

*Proof idea.* The source follows the finite-place half of Tate's thesis. The integral of $f \psi |\cdot|^s$ over the finite ideles, for a suitable test function $f$, is the partial $L$-function times a nonzero volume. At the infinite places the source does not use Poisson summation. It writes the integral as a sum over the principal ideles of a tent function, a theta sum, and it estimates this sum as a Riemann sum over the image of $K$ in its Minkowski space. The estimate `New.ZetaIntegral.exists_abs_sub_thetaSum_le_mul_rpow` says that the theta sum at an idele depends, up to an error $C l^\delta$, only on its module $l$. For $\psi \neq 1$ the main terms cancel over a fundamental domain, and the error gives analyticity in a neighbourhood of $1$. Over $\mathbb{Q}$ this is Müntz's formula (Titchmarsh, *The Theory of the Riemann Zeta-Function*, §2.11). $\square$

**Theorem (Density of a Hecke character).** Let $\psi$ be of type $n$, $\psi \neq 1$, and $S$ finite. Then `eulerProd (heckeCoeff ψ S)` is continuous on $[1, \infty)$, and there is $m \in \mathbb{N}$ such that `heckeCoeff ψ S` has prime density $-m$, and if $m = 0$ the Euler product has no zero on $[1, \infty)$.
Lean: `New.IsHeckeOfType.exists_hasPrimeDensity` (Lib/ClassField/HeckeL/ContinuationAtOne.lean).

*Proof.* Let $m$ be the order of vanishing of $F$ at $1$. It is finite since $F$ is nonzero for $s > 1$, where it is an exponential. Then $\log F(s) = m \log(s - 1) + O(1)$, and the logarithm of the Euler product is $\sum_v a_v q_v^{-s} + O(1)$. $\square$

**Theorem (Nonvanishing).** Let $\psi$ be of type $n$ with $\psi^2 \neq 1$, and $S$ finite. Then $\operatorname{eulerProd}(\operatorname{heckeCoeff} \psi\, S)(s) \neq 0$ for all real $s \geq 1$.
Lean: `New.IsHeckeOfType.eulerProd_ne_zero` (Lib/ClassField/HeckeL/ContinuationAtOne.lean).

*Proof.* Apply the last theorem to $\psi$ and $\psi^2$, with densities $-m_1$ and $-m_2$. The inequality $3 + 4\cos\theta + \cos 2\theta \geq 0$ gives $\operatorname{Re}(3 + 4 a_v + a_v^2) \geq 0$ for $|a_v| = 1$. So the density of $3 + 4\psi + \psi^2$ is $3 - 4m_1 - m_2 \geq 0$, and $m_1 = 0$. $\square$

**Remark (Formalization).** The textbook nonvanishing holds for every $\psi \neq 1$, at every $s$ with $\operatorname{Re} s = 1$. The source proves it only for real $s \geq 1$ and only when $\psi^2 \neq 1$. For a quadratic $\psi$ the argument with $\psi^2 = 1$ gives nothing, and the source does not prove $L(1, \psi) \neq 0$ for it. The second inequality below does not need it: it needs only that the densities are $-m$ with $m \geq 0$.

### The second inequality

**Lemma (Mean of a character of the quotient).** Let $W$ be an open subgroup of $(\mathbb{A}_{K,f})^\times$ that contains the principal idele of every totally positive $x \in K^\times$. Let $f$ be a character of $(\mathbb{A}_{K,f})^\times / W$, written additively. There is $m \in \mathbb{N}$ such that the values $f(\operatorname{locIdele}_v(\varpi_v))$ have prime density $1 - m$ if $f = 0$ and $-m$ otherwise.
Lean: `New.exists_hasPrimeDensity_addChar_uniformizer` (Lib/ClassField/Global/AlbertBrauerHasseNoether.lean).

*Proof.* The quotient is finite by Section 3. So $\psi = f$ is a character of finite order. On $K^\times$ it is trivial where no sign $\Phi_w(x)/|\Phi_w(x)|$ is $-1$. A lemma on characters (`New.exists_mul_prod_eq_one`) shows that $\psi$ is then the inverse of a product of some of the sign characters on $K^\times$. So $\psi$ is a Hecke character of a type with entries $0$ and $1$. For $f \neq 0$ the theorem on densities applies. For $f = 0$ the constant family $1$ has density $1$. $\square$

**Theorem (Second inequality).** Let $L/K$ be a Galois extension of number fields. Let $W$ be an open subgroup of $(\mathbb{A}_{K,f})^\times$ that contains the principal idele of every totally positive $x \in K^\times$ and contains $N_{L/K}(y)$ for every $y \in (\mathbb{A}_{L,f})^\times$. Then

(a) $W$ has finite index, and $[(\mathbb{A}_{K,f})^\times : W] \leq [L : K]$;

(b) for every finite idele $a$ there are infinitely many finite places $v$ with $q_v$ prime and $\operatorname{locIdele}_v(\varpi_v) / a \in W$.
Lean: `New.second_inequality` (Lib/ClassField/Global/AlbertBrauerHasseNoether.lean).

*Proof.* Let $h$ be the index, finite by Section 3. For a place $v$, let $D_v$ be the set of places $w$ of $L$ over $v$ with $q_w = q_v$. If $w \in D_v$ and $W$ contains the units at $v$, then $\varpi_v$ is $N(\varpi_w)$ up to a unit, so $\varpi_v \in W$. The Galois group permutes the places over $v$ transitively, so $\# D_v \leq [L : K]$. For almost all $v$,
$$h \cdot \# D_v \leq [L : K] \sum_f f(\varpi_v),$$
since the sum over the $h$ characters is $h$ if $\varpi_v \in W$ and $0$ otherwise. Take prime densities: the left side has density $h$, and the right side has density $[L : K] (1 - \sum_f m_f)$. Since $h \geq 1$, every $m_f = 0$, and $h \leq [L : K]$. For (b), the sum $\sum_f f(\varpi_v / a)$ has density $1$, so it is nonzero for infinitely many $v$ of prime norm, and then $\varpi_v / a \in W$. $\square$

This is the second inequality of Section 2, in the finite idele form, with the equidistribution statement (b) added. Part (b) is the source of Chebotarev in Section 7.

**Remark (Formalization).** The textbook second inequality is $[C_K : N C_L] \leq [L : K]$ for the full norm group. The source states it for every open $W$ that contains the norms and the totally positive elements, and it asks $W$ to be open. The full norm group $K^\times_+ N(\mathbb{A}_{L,f})^\times$ is open, since the norms contain the open group of local units at unramified places, but the source does not need this as a separate lemma. It applies the theorem to kernels of continuous maps, which are open by construction.
