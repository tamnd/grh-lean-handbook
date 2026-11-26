---
title: The general twisting theorem
lean:
  - New/Congruences/Selmer/GeneralTheorem.lean
decls:
  - New.Selmer.IsSmallTwist
  - New.Selmer.IsSmallTwist.mono
  - New.Selmer.exists_map_eq_map_pow_of_isTameGenerator
  - New.Selmer.TwistPolynomials.twist
  - New.Selmer.TwistPolynomials.twist_pow
  - New.Selmer.TwistPolynomials.twist_pow_eq_one
  - New.Selmer.TwistPolynomials.isFromU1_twist
  - New.Selmer.TwistPolynomials.exists_mem_inertiaAbove_twist_eq
  - New.Selmer.TwistPolynomials.ellVal_twist_tameGenerator_sub_one_le
  - New.Selmer.TwistPolynomials.sum_ellVal_twist_tameGenerator_sub_one_le
  - New.Selmer.TwistPolynomials.isSmallTwist_twist
  - New.Selmer.exists_rootsOfUnity_ellVal_eval_le
  - New.Selmer.exists_anticyclotomic_twist
status: drafted
drafted_by: writer@claude-opus-5-5
---

## The general twisting theorem

This section joins the twist polynomials and the roots of unity. The result is one anticyclotomic character $\psi$ whose powers $\psi, \dots, \psi^m$ have short Selmer groups for all Selmer data, small values at the elements of all Stickelberger systems, and values near $1$ at the tame generators. All results are in [GeneralTheorem.lean](lean:New/Congruences/Selmer/GeneralTheorem.lean#L1).

Fix finitely many Selmer data $T_i$ over a coefficient ring $O$ and Stickelberger systems $Y_k$, all for $S_0$ and $g_0$. The valuation is $v = \mathrm{ellVal}$ with $v(\ell) = 1$.

### Small twists

**Definition.** Let $\varepsilon \geq 0$, $Q$ a finite set of primes and $\psi : G_E \to \bar{\mathbb{Q}}_\ell^\times$. Then $\psi$ is a *small twist* (`IsSmallTwist`) if:

1. $\psi$ comes from $\mathrm{Cl}_\mathbb{Q}$ with tame level $Q$ and is trivial above $\ell$ (`IsFromU1`);
2. $\psi^{\ell^h} = 1$ for some $h$;
3. for each $v \in Q$ some $g$ in inertia above $v$ has $\psi(g) \neq 1$;
4. each $T_i$ satisfies `TwistedLengthLe Q ψ (normLength β_{T_i} + ε)`;
5. $v(\psi(\Theta_{Y_k, Q})) \leq \beta_{Y_k} + \varepsilon$ for each $k$;
6. for any places $A_w$ above $w$ and any tame generators $\gamma_w$ of inertia at $A_w$, $\sum_{w \in Q \cup \bar{Q}} v(\psi(\gamma_w) - 1) \leq \varepsilon$.

Lean: `New.Selmer.IsSmallTwist` (New/Congruences/Selmer/GeneralTheorem.lean).

**Lemma.** A small twist for $\varepsilon$ is a small twist for every $\varepsilon' \geq \varepsilon$.

Lean: `New.Selmer.IsSmallTwist.mono` (New/Congruences/Selmer/GeneralTheorem.lean).

*Proof.* Items 1 to 3 do not involve $\varepsilon$. Items 4 to 6 follow by `TwistedLengthLe.mono` and by $\varepsilon \leq \varepsilon'$. $\square$

### The twist of a set of twist polynomials

Let $X$ be twist polynomials for $s_0$, $r$ and $N$, with primes $Q$ and maps $\lambda_{\mathfrak{q}}$ to $\mathbb{Z}/\ell^N$ ([twist polynomials](/chapter/twisting-theorem/#selmer-data-on-a-line)). Let $\zeta_{\mathfrak{q}} \in \bar{\mathbb{Z}}_\ell$ with $\zeta_{\mathfrak{q}}^{\ell^N} = 1$.

**Definition.** The *twist* of $X$ at $\zeta$ is $\psi(g) = \prod_{\mathfrak{q} \in Q} \zeta_{\mathfrak{q}}^{\lambda_{\mathfrak{q}}(g)}$, with $\lambda_{\mathfrak{q}}(g)$ read in $[0, \ell^N)$.

Lean: `New.Selmer.TwistPolynomials.twist` (New/Congruences/Selmer/GeneralTheorem.lean).

**Lemma (The twist).**

1. $\psi^j$ is the twist at $(\zeta_{\mathfrak{q}}^j)$, and $\psi^{\ell^N} = 1$.
2. $\psi$ comes from $\mathrm{Cl}_\mathbb{Q}$ with tame level $Q$ and is trivial above $\ell$.
3. For $v \in Q$ and $w \in \{v, \bar{v}\}$, some $g$ in inertia above $w$ has $\psi(g) = \zeta_v$.

Lean: `New.Selmer.TwistPolynomials.twist_pow`, `New.Selmer.TwistPolynomials.twist_pow_eq_one`, `New.Selmer.TwistPolynomials.isFromU1_twist`, `New.Selmer.TwistPolynomials.exists_mem_inertiaAbove_twist_eq` (New/Congruences/Selmer/GeneralTheorem.lean).

*Proof.* (1) $\psi$ is a product of the maps $g \mapsto \zeta^{\lambda(g)}$. Each is a homomorphism because $\zeta^{\ell^N} = 1$. (2) Each $\lambda_{\mathfrak{q}}$ comes from $\mathrm{Cl}_\mathbb{Q}$ with tame level $\{\mathfrak{q}\} \subseteq Q$ by item 2 of the twist polynomials. The twist is the point character of the $\lambda_{\mathfrak{q}}$ at $\zeta$, so the first lemma of [Stickelberger systems on a line](/chapter/twisting-theorem/#stickelberger-systems-on-a-line) applies. (3) Item 2 of the twist polynomials gives $g$ in inertia above $v$ with $\lambda_v(g) = 1$. The other $\lambda_u$ are unramified at $v$, since $v$ is neither $u$ nor $\bar{u}$. So $\psi(g) = \zeta_v$. For $w = \bar{v}$, take $g' = \iota_{\mathrm{false}}(g) = (c g c^{-1})^{-1}$ for the complex conjugation $c$. It lies in inertia above $\bar{v}$. By (2), $\psi$ is anticyclotomic, so $\psi(g') = \psi(g)$. $\square$

**Lemma (Tame values).** Let $\chi$ be locally constant with $\chi^q = 1$, $A$ a place above $w$ at which $q$ is a unit, and $\gamma$ a tame generator of inertia at $A$. Then $\chi(g)$ is a power of $\chi(\gamma)$ for every $g$ in an inertia group above $w$. Consequently, let $S_0$ contain the places above $\ell$, $v \in Q$ and $w \in \{v, \bar{v}\}$. Then $v(\psi(\gamma) - 1) \leq v(\zeta_v - 1)$. If all $v(\zeta_v - 1) \leq r$, then $\sum_{w \in Q \cup \bar{Q}} v(\psi(\gamma_w) - 1) \leq s_0 r$.

Lean: `New.Selmer.exists_map_eq_map_pow_of_isTameGenerator`, `New.Selmer.TwistPolynomials.ellVal_twist_tameGenerator_sub_one_le`, `New.Selmer.TwistPolynomials.sum_ellVal_twist_tameGenerator_sub_one_le` (New/Congruences/Selmer/GeneralTheorem.lean).

*Proof.* The inertia groups above $w$ are conjugate, and $\chi$ is constant on conjugacy classes, so it suffices to treat inertia at $A$. There $\chi$ kills the elements of inertia near $1$, since it is locally constant, and its values on inertia have order dividing $q$, a unit at $A$. The structure of tame inertia (`New.IsPlaceOver.exists_eq_pow_and_apply_conj_eq_pow`, Lib/ClassField/Local/ArtinMap.lean) then gives $\chi(g) = \chi(\gamma)^a$ for some $a$.

The prime $w$ is prime to $\ell$, since $Q$ and $\bar{Q}$ are disjoint from $S_0$. Apply the first part with $q = \ell^N$: by part 3 of the last lemma, $\zeta_v = \psi(\gamma)^a$. Then $\zeta_v - 1 = (\psi(\gamma) - 1) \sum_{i < a} \psi(\gamma)^i$, and the sum is integral. So $v(\zeta_v - 1) \geq v(\psi(\gamma) - 1)$. The set $Q \cup \bar{Q}$ has at most $2 \# Q \leq s_0$ elements, and each term is at most $r$. $\square$

**Theorem (The twist is small).** Let $S_0$ contain the places above $\ell$, $\varepsilon < 1$ and $s_0 r \leq \varepsilon$. Let all $v(\zeta_v - 1) \leq r$, and at $x = (\zeta_v - 1)_v$ let $v(P_i(x)) \leq \mathrm{normLength}(\beta_{T_i}) + \varepsilon$ and $v(P_k(x)) \leq \beta_{Y_k} + \varepsilon$. Then the twist $\psi$ is a small twist for $\varepsilon$ and $Q$.

Lean: `New.Selmer.TwistPolynomials.isSmallTwist_twist` (New/Congruences/Selmer/GeneralTheorem.lean).

*Proof.* Items 1 and 2 are parts 1 and 2 of the lemma on the twist. Item 3: part 3 gives $g$ in inertia above $v$ with $\psi(g) = \zeta_v$, and $\zeta_v \neq 1$ because $v(\zeta_v - 1) \leq r$ is finite. Item 4: $v(P_i(x)) \leq \mathrm{normLength}(\beta_{T_i}) + \varepsilon < \mathrm{normLength}(\beta_{T_i}) + 1$, so item 6 of the twist polynomials gives `TwistedLengthLe` with the bound $v(P_i(x))$. Weaken it. Item 5: $\psi(\Theta_{Y_k, Q}) = P_k(x)$ by item 5 of the twist polynomials. Item 6 is the lemma on tame values with $s_0 r \leq \varepsilon$. $\square$

### All powers at once

**Lemma (Roots for all powers).** Let $s_0$, $m \geq 1$, $r > 0$, $\varepsilon > 0$ and finitely many finite bounds $\beta_i$ be given. There is $h_0$ with this property. Let $P_i$ be polynomials over $\bar{\mathbb{Z}}_\ell$ in at most $s_0$ variables, and $x_i$ points with all coordinates of valuation at least $r$ and $v(P_i(x_i)) \leq \beta_i$. There are $\zeta_u$ with $\zeta_u^{\ell^{h_0}} = 1$ and $v(\zeta_u - 1) \leq r/m$ such that $v(P_i((\zeta_u^j - 1)_u)) \leq v(P_i(x_i)) + \varepsilon$ for all $i$ and all $1 \leq j \leq m$.

Lean: `New.Selmer.exists_rootsOfUnity_ellVal_eval_le` (New/Congruences/Selmer/GeneralTheorem.lean).

*Proof.* Let $B = \sum_{i, j} \beta_i$ over $i$ and $1 \leq j \leq m$. Take $h_0$ from the theorem on roots of unity ([roots of unity](/chapter/twisting-theorem/#roots-of-unity)) for $s_0$, $r/m$, $B$ and $\varepsilon$. Given the $P_i$ and $x_i$, put $P_{i,j}(X) = P_i(((1 + X_u)^j - 1)_u)$. For each coordinate there is $x'$ with $(1 + x')^j - 1 = x_{i,u}$ and $v(x') \geq r/m$ (`New.Selmer.exists_one_add_pow_eq`, Lib/General/NumberTheory/GaussValuation.lean): the $j$ solutions have product $\pm x_{i,u}$. Then $P_{i,j}(x'_{i,j}) = P_i(x_i)$, so the sum over all $(i, j)$ is at most $B$. The theorem gives $\zeta_u$ with $v(P_{i,j}((\zeta_u - 1)_u)) \leq v(P_i(x_i)) + \varepsilon$. The left side is $v(P_i((\zeta_u^j - 1)_u))$. $\square$

**Theorem (Twisting theorem, general form).** Let $S_0$ contain the places above $\ell$, let $g_0$ lie in inertia above a place of $S_0$ prime to $\ell$, let $M$ be a torsion level for the $T_i$, and let $m \geq 1$ and $\varepsilon > 0$. There are an auxiliary set $Q$ and a character $\psi$ such that $\psi^j$ is a small twist for $\varepsilon$ and $Q$ for every $1 \leq j \leq m$.

Lean: `New.Selmer.exists_anticyclotomic_twist` (New/Congruences/Selmer/GeneralTheorem.lean).

*Proof.* If $\varepsilon \geq 1$, the case $\varepsilon = 1/2$ and the monotonicity lemma give the claim. So let $\varepsilon < 1$. The order of the choices matters: first $s_0$, then $r$, then $h_0$, and last $N$.

The theorem on twist polynomials gives $s_0 \geq 1$. Choose a rational $r > 0$ with $s_0 r \leq \varepsilon/2$. Then $s_0 r < 1$ and $r < 1$. Put $\beta = \mathrm{normLength}(\beta_{T_i})$ for the data and $\beta = \beta_{Y_k}$ for the systems; these are finite. The lemma on roots for all powers, with the bounds $\beta + 1$ and the loss $\varepsilon/2$, gives $h_0$. Choose $N \geq h_0$ such that twist polynomials $X$ exist for $s_0$, $r$ and $N$.

The points of $X$ have $v(P(x)) \leq \beta + s_0 r \leq \beta + 1$, and $\# Q \leq s_0$. The lemma gives $\zeta_v$ with $\zeta_v^{\ell^{h_0}} = 1$, hence $\zeta_v^{\ell^N} = 1$, with $v(\zeta_v - 1) \leq r/m$ and

$$v(P((\zeta_v^j - 1)_v)) \leq \beta + s_0 r + \varepsilon/2 \leq \beta + \varepsilon \quad (1 \leq j \leq m).$$

Let $\psi$ be the twist of $X$ at $\zeta$. Fix $j$. Since $r < 1$ and $v(\zeta_v - 1) \leq r/m$, $v(\zeta_v^j - 1) \leq r$ (`New.Selmer.ellVal_pow_sub_one_le`, Lib/General/NumberTheory/GaussValuation.lean). By part 1 of the lemma on the twist, $\psi^j$ is the twist at $(\zeta_v^j)$. The theorem that the twist is small applies with $s_0 r \leq \varepsilon$. $\square$

**Remark (Formalization).** The roots $\zeta_v$ have order dividing $\ell^{h_0}$, and $h_0$ is chosen before $N$. This is why `exists_twistPolynomials` gives twist polynomials for all large $N$ and not for one $N$. The theorem does not bound $\# Q$ in terms of $\varepsilon$; it only uses $2 \# Q \leq s_0$.
