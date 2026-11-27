---
title: The normalized map
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Spanning/SecondMoment/SpanningTheorem.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
  - New/Spanning/Unfolding/SeriesPeriod.lean
  - New/Determinant/Chain/NormOfChain.lean
decls:
  - New.Data.poincare
  - New.Data.goodProjTranslate
  - New.Data.goodPoincare
  - New.Data.Θ
  - New.Data.seesawConst
  - New.Data.scaledInclusion
  - New.Data.projectedPoincare
  - New.Data.normalizedPoincare
  - New.Data.coe_normalizedPoincare
  - New.Data.exists_lowerChain_poincare_eq
  - New.Data.normSqAt_normalizedPoincare
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The normalized map

This section builds the map $s\mathfrak{p}$ of Theorem A in four layers: the Poincaré map, the good part of a translate, the seesaw constant and the gain factor. It then proves the three properties of the map that the proofs of Sections 6 and 7 use. The first says that $s\mathfrak{p}$ is the translate by $s$ of $\mathfrak{p} = 1\mathfrak{p}$. The second is the seesaw identity with constant $1$. The third computes the effect of $c_B$ on the squared norm.

### The layers

**Definition (The Poincaré map).** $\mathcal{P}$ is the Poincaré map $\mathcal{P}_{g,t}$ of the seesaw identity at the Bessel point $g$ and the Bessel form $t$ of the data. It sends a source form to a form of principal level on $Y_0$.

Lean: `New.Data.poincare` (New/Spanning/Unfolding/SeriesPeriod.lean).

[The objects of the upper bound](/chapter/upper-bound-objects/) describes $\mathcal{P}_{g,t}\varphi$ as the form that represents the Bessel period of $\varphi$ in the Petersson inner product. For the chosen $g$ and $t$ it is a Poincaré series, which Volume 10 studies.

**Definition (The good part of a translate).** For $s \in \bar G$ and a form $z$ of principal level on $Y_0$, put $\#\bar G\,e_0\,s\,z = \#\bar G\cdot e_0\cdot(s z)$, where $\bar G$ acts on the forms of principal level and $e_0$ acts through the group algebra. The map takes values in the image of $e_0$.

Lean: `New.Data.goodProjTranslate` (New/Spanning/Unfolding/FillingAdmissible.lean).

**Definition (The good Poincaré map).** For $s \in \bar G$, the map from all source forms to $T$ is $\varphi \mapsto \#\bar G\,e_0\,s\,\mathcal{P}\varphi$.

Lean: `New.Data.goodPoincare` (New/Spanning/SecondMoment/SpanningTheorem.lean).

**Definition (The chain on target forms).** For an $m$-fold twist $\vartheta$, $\Theta_\vartheta$ is the restriction to $T$ of the lower chain $\iota_\vartheta$, followed by the passage to the forms on $Y_m$ of the level and character of $\vartheta$.

Lean: `New.Data.Θ` (New/Determinant/Chain/NormOfChain.lean).

**Definition (The seesaw constant).** $c_{ss} \in \mathbb{C}^\times$ is the constant $c$ of the seesaw identity for the Bessel form and the Bessel point.

Lean: `New.Data.seesawConst` (New/Reduction/ShortAndEnough.lean).

**Definition (The normalized map).** For $s \in \bar G$ and $\varphi \in \mathrm{src}$, put

$$s\mathfrak{p}_0\,\varphi = \#\bar G\,e_0\,s\,\mathcal{P}(c_{ss}^{-1}\varphi), \qquad s\mathfrak{p}\,\varphi = c_B\cdot s\mathfrak{p}_0\,\varphi.$$

Both are linear maps from $\mathrm{src}$ to $T$. The first is the composite of the inclusion of $\mathrm{src}$ scaled by $c_{ss}^{-1}$ and the good Poincaré map.

Lean: `New.Data.scaledInclusion`, `New.Data.projectedPoincare`, `New.Data.normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

The map $s\mathfrak{p}_0$ is the map of the projected Poincaré series. It carries all the structure. The factor $c_B$ is a positive rational number, so it changes sizes and valuations but no linear algebra.

**Remark (Formalization).** Three objects in the map are chosen by `choose`. The Bessel point and the Bessel form come from an existence theorem of Volume 10 (`New.Data.besselPoint` and `New.Data.besselForm` in SeriesPeriod.lean). The constant $c_{ss}$ is `(D.seesaw_identity D.besselForm D.besselPoint).choose`. [The three inputs](/chapter/theorem-a-plan/#the-three-inputs) explains that the proof of the seesaw identity sets $c = 1$ in a degenerate case, where the glued tensor vanishes and the identity says $0 = 0$. The type $\mathbb{C}^\times$ only says that $c_{ss}$ is a unit. Theorem A holds for the chosen constant, whatever it is. Theorem A is a pair of upper bounds, and a degenerate choice would make the images small, not large. The nonvanishing that the whole argument needs comes from Theorems B and C.

### The translates

**Lemma (Translates of the normalized map).** For $s \in \bar G$ and $\varphi \in \mathrm{src}$, as forms on $Y_0$,

$$s\mathfrak{p}\,\varphi = s\cdot\bigl(1\mathfrak{p}\,\varphi\bigr),$$

where $s$ acts by the representation of $\bar G$ on the forms of principal level.

Lean: `New.Data.coe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* The idempotent $e_0$ is central in $\mathbb{C}[\bar G]$, so its action commutes with the action of $s$. Hence $\#\bar G\,e_0\,s\,z = s\,(\#\bar G\,e_0\,z)$ for every $z$. Apply this to $z = \mathcal{P}(c_{ss}^{-1}\varphi)$ and multiply by $c_B$, which commutes with every linear map. $\square$

So the family of maps $s\mathfrak{p}$, $s \in \bar G$, is the orbit of one map under $\bar G$. Theorem A is stated for every $s$, and Theorem B chooses a set $t$ of translates.

### The seesaw identity with constant one

**Lemma (Seesaw identity for $c_{ss}^{-1}\mathcal{P}$).** Every twist $\vartheta$ has a chain datum $\Psi$ for $\vartheta$ such that

$$\iota_\vartheta\bigl(\mathcal{P}(c_{ss}^{-1}\varphi)\bigr) = B_{\vartheta,\Psi}\varphi$$

for every $\varphi \in \mathrm{src}$. Here $\iota_\vartheta$ is the lower chain for the tame character of $\vartheta$.

Lean: `New.Data.exists_lowerChain_poincare_eq` (New/Reduction/ShortAndEnough.lean).

*Proof.* The seesaw identity at the Bessel point and the Bessel form, with the chosen constant $c_{ss}$, gives a chain datum $\Psi$ for $\vartheta$ with $\iota_\vartheta(\mathcal{P}\varphi) = c_{ss}B_{\vartheta,\Psi}\varphi$ for all $\varphi \in \mathrm{src}$. The maps $\mathcal{P}$ and $\iota_\vartheta$ are linear, so $\iota_\vartheta(\mathcal{P}(c_{ss}^{-1}\varphi)) = c_{ss}^{-1}c_{ss}B_{\vartheta,\Psi}\varphi = B_{\vartheta,\Psi}\varphi$. $\square$

The chain datum depends on $\vartheta$. Part (a) uses the lemma for the trivial twist. Part (b) uses it for every $m$-fold twist $\vartheta$ of level prime to $\ell$, through its underlying twist. As the divisibility holds for every chain datum, it does not matter which chain datum the lemma gives.

### The gain factor at infinity

**Lemma (The factor $c_B$ at infinity).** For $s \in \bar G$, $\varphi \in \mathrm{src}$ and every automorphism $\sigma$ of $\mathbb{C}$,

$$\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 = \exp(2\log c_B)\,\|\Theta_1(s\mathfrak{p}_0\,\varphi)\|_\sigma^2.$$

Lean: `New.Data.normSqAt_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* The map $\Theta_1$ is linear, so $\Theta_1(s\mathfrak{p}\,\varphi) = c_B\,\Theta_1(s\mathfrak{p}_0\,\varphi)$. The squared norm $\|F\|_\sigma^2$ is a class sum of the squared Weyl norms of the vectors $\sigma(F(g))$. For a scalar $c$, $|\sigma(cv)|^2 = |\sigma(c)|^2|\sigma(v)|^2$. As $c_B$ is rational and positive, $\sigma(c_B) = c_B$ and $|c_B|^2 = \exp(2\log c_B)$. $\square$

The lemma is exact. Part (a) combines it with the bound for $\log c_B$ of Section 4.

### What the three lemmas give

The proofs in Sections 6 and 7 use the map only through three facts.

1. For each twist there is a chain datum $\Psi$ with $\iota_\vartheta z = B_{\vartheta,\Psi}\varphi$, where $z = \mathcal{P}(c_{ss}^{-1}\varphi)$. This moves every question about $\Theta_\vartheta(s\mathfrak{p}\,\varphi)$ to a question about $c_B\cdot\iota_\vartheta(\#\bar G\,e_0\,s\,z)$, and then, by the two lemmas on the good part, to a question about $c_B\,B_{\vartheta,\Psi}\varphi$.
2. At infinity, $c_B$ contributes $2\log c_B$ to the logarithm of the squared norm.
3. At $\iota$ above $\ell$, $c_B$ contributes $\|c_B\| = \ell^{g_\ell}$, by the lemma on the gain factor at a prime.

**Example (The two scalars).** Suppose $c_{ss} = 2i$ and $c_B = 1/9$. Then $s\mathfrak{p}\,\varphi = \tfrac{1}{9}\cdot\tfrac{1}{2i}\cdot\#\bar G\,e_0\,s\,\mathcal{P}\varphi$. The factor $1/(2i)$ is not real, and it is not fixed by $\sigma$. It does not enter the size bound, since it is absorbed into the seesaw identity: $\iota_1(\mathcal{P}(c_{ss}^{-1}\varphi)) = B_{1,\Psi}\varphi$ holds with no constant. The factor $1/9$ is rational, so it enters the size bound as $\exp(2\log(1/9)) = 1/81$, and it enters the valuation at $3$ as $\|1/9\| = 3^{2}$.
