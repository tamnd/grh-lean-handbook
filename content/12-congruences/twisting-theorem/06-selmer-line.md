---
title: Selmer data on a line
lean:
  - New/Congruences/Selmer/Line.lean
decls:
  - New.Selmer.exists_smul_eq_zero_of_mem_selmerModule
  - New.Selmer.length_selmerModule_divisibleQuot_le
  - New.Selmer.SelmerDatum.twistedSelmer
  - New.Selmer.SelmerDatum.divisibleSelmer
  - New.Selmer.SelmerDatum.divisibleLength
  - New.Selmer.SelmerDatum.TwistedLengthLe
  - New.Selmer.SelmerDatum.TwistedLengthLe.mono
  - New.Selmer.tieRelations_union
  - New.Selmer.BoundsSelmer
  - New.Selmer.restrictToLine
  - New.Selmer.eval₂_restrictToLine
  - New.Selmer.gaussVal_tiePolynomial_le
  - New.Selmer.coe_twistRep_pointChar
  - New.Selmer.SelmerDatum.reduceModPow_eq_one
  - New.Selmer.SelmerDatum.length_tiedSelmer_erase_le
  - New.Selmer.SelmerDatum.exists_boundsSelmer_and_eval_dvd
  - New.Selmer.SelmerDatum.divisibleLength_pointChar_le
  - New.Selmer.SelmerDatum.exists_boundsSelmer_ellVal_eval_le
  - New.Selmer.SelmerDatum.twistedLengthLe_pointChar
  - New.Selmer.SelmerDatum.eventually_reduceModPow_idOrConjInv_eq
  - New.Selmer.IsTorsionLevel
  - New.Selmer.TwistPolynomials
  - New.Selmer.nonempty_twistPolynomials_of_isTiedPrimes
  - New.Selmer.exists_twistPolynomials
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Selmer data on a line

The last section gave each Stickelberger system a polynomial and a point near $0$ at which the polynomial is small. This section does the same for Selmer data. It then puts the data and the systems together on one set of auxiliary primes. The result, `exists_twistPolynomials`, is the input of the general twisting theorem in the section after next. All results are in [Line.lean](lean:New/Congruences/Selmer/Line.lean#L1).

The background comes from two chapters.

- Selmer data $T$ with the number $\beta_T = \mathrm{glob}(T) + \mathrm{places}(T) + \mathrm{first}(T)$ and the tied Selmer groups: [Selmer data, tied Selmer groups and Sah's lemma](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma).
- The point modules $\mathrm{Sel}(x)$ of the twists $\psi_x(g) = \prod_j (1 + x_j)^{h_j(g)}$ and a polynomial $P$ with $v(P(x_0)) = \mathrm{len}\, \mathrm{Sel}(x_0)$ and $v(P(x)) \geq \mathrm{len}\, \mathrm{Sel}(x)$ everywhere (`New.Selmer.exists_sharp_polynomial`): [one system for all twists](/chapter/tied-selmer-groups/#one-system-for-all-twists).
- The line $X_{P_0} = Y$, $X_v = s_v Y$ (`New.Selmer.lineDirection`), the tie polynomial $P^1$, the cost of the ties and the release of the first prime: [untied classes](/chapter/tied-selmer-groups/#untied-classes).
- The descent to tied primes with a first prime near $g_0$ (`New.Selmer.exists_isTiedPrimes_card_le_and_length_le`): [the descent](/chapter/tied-selmer-groups/#the-descent).
- Coefficient rings, $\mathrm{normLength}$ (a length scaled so that $O/\ell$ has length $1$) and the geometric sum bound `New.Selmer.pow_dvd_geom_sum`: [coefficient rings](/chapter/fitting-ideals/#coefficient-rings).
- Relative lengths and $\mathrm{relLength}(A, B) + \mathrm{len}(A \cap B) = \mathrm{len}\, A$: [discrete valuation rings and relative lengths](/chapter/fitting-ideals/#discrete-valuation-rings-and-relative-lengths).

Valuations are $v = \mathrm{ellVal}$ with $v(\ell) = 1$, unless a ring is named.

### From a finite level to divisible coefficients

**Lemma (Levels).** Let $O$ be a discrete valuation ring, $\rho$ a matrix valued map on $G_E$, $S$ a set of finite places and $L$ a set of relations.

1. Each member $z$ of the Selmer module with coefficients in $\mathrm{Frac}(O)/O$ has some $a \neq 0$ with $a z = 0$.
2. Let $a \neq 0$. If $\mathrm{len}\, \mathrm{Sel}(O/a) < v_O(a)$, then $\mathrm{len}\, \mathrm{Sel}(\mathrm{Frac}(O)/O) \leq \mathrm{len}\, \mathrm{Sel}(O/a)$.

Lean: `New.Selmer.exists_smul_eq_zero_of_mem_selmerModule`, `New.Selmer.length_selmerModule_divisibleQuot_le` (New/Congruences/Selmer/Line.lean).

*Proof.* (1) A member $z$ is locally constant on the compact group $G_E$, so it takes finitely many values. Each coordinate $u$ of a value has a denominator $d(u) \neq 0$ with $d(u) u = 0$. The product $a$ of all these denominators is not $0$ and kills $z$.

(2) The $a$-torsion of $\mathrm{Sel}(\mathrm{Frac}(O)/O)$ is isomorphic to $\mathrm{Sel}(O/a)$ (`New.Selmer.length_torsionBy_selmerModule_divisibleQuot`, Lib/GaloisRep/Main/DivisibleSelmerModules.lean). Suppose that this torsion is not the whole module. The module is torsion by (1), so its $a$-torsion has length at least $v_O(a)$ (`New.Selmer.addVal_le_length_torsionBy`, [block determinants](/chapter/fitting-ideals/#block-determinants)). This contradicts the hypothesis. So the torsion is the whole module, and the two lengths are equal. $\square$

### Twisted Selmer groups

**Definition.** Let $T$ be a Selmer datum over $O$ with places $S$, let $Q$ be a finite set of primes, let $e : O \to O'$ and let $\psi : G_E \to O'^\times$. The group $\mathrm{Sel}_Q(T\psi) \bmod a$ (`twistedSelmer`) is the Selmer module of the twist of $T$ by $\psi$ through $e$, unramified outside $S \cup Q \cup \bar{Q}$, with the relations of $T$ mapped by $e$, and with values in $O'/a$. For a discrete valuation ring $O'$ the group `divisibleSelmer` is the same module with values in $\mathrm{Frac}(O')/O'$, and `divisibleLength` is its length over $O'$. For a coefficient ring $O$ and $\psi$ with values in $\bar{\mathbb{Q}}_\ell$, $T$ satisfies `TwistedLengthLe Q ψ b` if for all large coefficient rings $O' \supseteq O$ there is $\psi'$ with values in $O'$, equal to $\psi$ in $\bar{\mathbb{Q}}_\ell$, such that $\mathrm{normLength}_{O'}(\mathrm{divisibleLength}) \leq b$.

Lean: `New.Selmer.SelmerDatum.twistedSelmer`, `New.Selmer.SelmerDatum.divisibleSelmer`, `New.Selmer.SelmerDatum.divisibleLength`, `New.Selmer.SelmerDatum.TwistedLengthLe` (New/Congruences/Selmer/Line.lean).

**Remark (Formalization).** The relations of $T$ include vanishing at the element $\gamma_*$ of $T$. So the members are cocycles, not classes. If $\psi(\gamma_*) = 1$, each class has exactly one cocycle that vanishes at $\gamma_*$, so the two counts agree. `TwistedLengthLe` asks the bound for all large $O'$ and not for one ring. So the definition does not fix one ring $O'$ in advance.

**Lemma.** If $T$ satisfies `TwistedLengthLe Q ψ b` and $b \leq b'$, then it satisfies `TwistedLengthLe Q ψ b'`.

Lean: `New.Selmer.SelmerDatum.TwistedLengthLe.mono` (New/Congruences/Selmer/Line.lean).

*Proof.* Keep the same rings, characters and bounds, and compose with $b \leq b'$. $\square$

### Bounds at all points, and the line

**Definition.** Let $h_j : G_E \to \mathbb{Z}/q$ for $j \in \sigma$. A polynomial $P$ in the variables $X_j$ over $O$ *bounds the Selmer module* (`BoundsSelmer`) if $\mathrm{len}_{O'}\, \mathrm{Sel}(x) \leq v_{O'}(P(x))$ for every discrete valuation ring $O'$ of characteristic $0$, every $e : O \to O'$ and every point $x \in O'^\sigma$. Here $\mathrm{Sel}(x)$ is the point module modulo $\ell^M$ of the twist by $\psi_x$. The restriction of $P$ to the line with direction $a$ is $P(a_j Y)_j \in O[Y]$ (`restrictToLine`).

Lean: `New.Selmer.BoundsSelmer`, `New.Selmer.restrictToLine` (New/Congruences/Selmer/Line.lean).

The bound holds at all points, not only at points where $\psi_x$ is a character.

**Lemma.** Let $d$ give each prime $w$ a Frobenius element $\varphi_w$, a tame generator $\gamma_w$, a character to $\mathbb{Z}/q$ and slopes.

1. $(\mathrm{restrictToLine}\ a\ P)(y) = P((e(a_j) y)_j)$, with coefficients mapped by $e$.
2. The ties at the primes of $I \cup I'$ are the ties at $I$ together with the ties at $I'$.
3. Let $\zeta_j^q = 1$. The twist of $\rho$ by $g \mapsto \prod_j \zeta_j^{h_j(g)}$ (`pointChar`) is the twist at the point $x = (\zeta_j - 1)_j$.
4. If $g$ lies in an inertia group above a place outside $S_0$, then $\rho_T(g) \equiv 1$ modulo $\ell^M$.

Lean: `New.Selmer.eval₂_restrictToLine`, `New.Selmer.tieRelations_union`, `New.Selmer.coe_twistRep_pointChar`, `New.Selmer.SelmerDatum.reduceModPow_eq_one` (New/Congruences/Selmer/Line.lean).

*Proof.* (1) Induction on $P$: both sides are ring maps in $P$ and agree on constants and variables. (2) Unfold the set of ties; a union of ranges over $I \cup I'$ is the union of the ranges. (3) $\zeta_j = 1 + (\zeta_j - 1)$, so both twists have the same value at each $g$. (4) $T$ is unramified outside its places, and these lie in $S_0$. $\square$

**Lemma (Gauss valuation of the tie polynomial).** Let $P^1 = \prod_{v \in I} \prod_b \det((1 + Y)\rho(\iota_b(\varphi_v)) - 1)$, where $\iota_{\mathrm{true}}(g) = g$ and $\iota_{\mathrm{false}}(g) = g^{-c}$. Let $f : O \to \bar{\mathbb{Z}}_\ell$ and let $2 n \# I \leq s_0$ for the rank $n$ of $\rho$. Then $v_r(f(P^1)) \leq s_0 r$.

Lean: `New.Selmer.gaussVal_tiePolynomial_le` (New/Congruences/Selmer/Line.lean).

*Proof.* The coefficient of $Y^n$ in $\det((1 + Y)A - 1)$ is $\det A$. For $A = \rho(g)$ this is a unit, since $g$ is invertible. A polynomial with a unit coefficient in degree $n$ has $v_r \leq nr$. The Gauss valuation is additive on products, and there are $2\# I$ factors. So $v_r(f(P^1)) \leq 2 \# I \cdot nr \leq s_0 r$. $\square$

### The polynomial of one datum

Fix tied primes $(P_0, J, d)$ for the condition $V$ and the set $W$ (`IsTiedPrimes`), the index $i$ of $T$, and $M < N$. Let $s_v$ be the slope of $T$ at $v$.

**Theorem (Release of the first prime for a datum).** Let the elements with $V_i$ act trivially on $T$ modulo $\ell^M$, let $\rho_T(\iota_b(\varphi_{P_0})) \equiv \rho_T(\iota_b(g_0))$ modulo $\ell^M$ for both $b$, and let the Selmer group modulo $\ell^M$ tied at all of $J$ have length at most $\mathrm{glob}(T) + \mathrm{places}(T)$. Then the group tied at $J \setminus \{P_0\}$ has length at most $\beta_T$.

Lean: `New.Selmer.SelmerDatum.length_tiedSelmer_erase_le` (New/Congruences/Selmer/Line.lean).

*Proof.* Let $Z$ be the group tied at $J$ and $Z_0$ the group tied at $J \setminus \{P_0\}$. By part 2 of the lemma above, the ties at $J$ are those at $J \setminus \{P_0\}$ and at $\{P_0\}$. So $Z = Z_0 \cap \mathrm{tie}(\{P_0\})$. The release of the first prime gives $\mathrm{relLength}(Z_0, Z) \leq \sum_b v(\det(\rho(\iota_b(g_0)) - 1)) = \mathrm{first}(T)$. Then $\mathrm{len}\, Z_0 = \mathrm{relLength}(Z_0, Z) + \mathrm{len}\, Z \leq \mathrm{first}(T) + \mathrm{glob}(T) + \mathrm{places}(T) = \beta_T$. $\square$

**Theorem (Division on the line).** Let $N \neq 0$, $r \leq 1$ and $M \leq Nr$. Let the elements with $V_i$ act trivially on $T$ modulo $\ell^M$, and let the group tied at $J \setminus \{P_0\}$ have length at most $\beta_T$. There is $P^0 \in O[Y]$ with $v_O(P^0(0)) \leq \beta_T$ such that the following holds. Let $O'$ be a discrete valuation ring of characteristic $0$, $e : O \to O'$, and $f : O' \to \bar{\mathbb{Z}}_\ell$ with $f(z) \mid f(z') \Rightarrow z \mid z'$. Let $y \in O'$ with $v(f(y)) \geq r$ and $a = \mathrm{lineDirection}$. Then some $P$ bounds the Selmer module of $T$ without ties for the characters of $d$, and $P((f e(a_v) f(y))_v)$ divides $f(P^0(y)) \cdot f(P^1(y))$ in $\bar{\mathbb{Z}}_\ell$. Here $P^1$ is the tie polynomial of $J \setminus \{P_0\}$.

Lean: `New.Selmer.SelmerDatum.exists_boundsSelmer_and_eval_dvd` (New/Congruences/Selmer/Line.lean).

*Proof.* Let $L_0$ be the relations of $T$ together with the ties at $J \setminus \{P_0\}$. The sharp polynomial theorem gives $G$ that bounds the module with $L_0$ and is sharp at the point $0$. Put $P^0 = \mathrm{restrictToLine}\ a\ G$. Its constant term is $G(0)$, and at $0$ the point module is the tied group. So $v_O(P^0(0)) = \mathrm{len}$ of the tied group $\leq \beta_T$.

Now fix $O'$, $e$, $f$ and $y$, and put $x = (e(a_v) y)_v$. Write $\mathrm{Sel}(L)$ for the point module at $x$ with relations $L$. The sharp polynomial theorem gives $P$ that bounds the module without ties and is sharp at $x$: $v(P(x)) = \mathrm{len}\, \mathrm{Sel}(L_T)$.

The cost of the ties needs hypothesis (G): if $y \mid \alpha - 1$ then $\ell^M \mid \sum_{j < \ell^N} \alpha^j$. This holds: $v(f(\alpha - 1)) \geq v(f(y)) \geq r$, and the geometric sum bound applies because $r \leq 1$ and $M \leq Nr$. The cost of the ties then gives $\mathrm{relLength}(\mathrm{Sel}(L_T), \mathrm{Sel}(L_0)) \leq v(P^1(y))$. So

$$v(P(x)) = \mathrm{relLength}(\mathrm{Sel}(L_T), \mathrm{Sel}(L_0)) + \mathrm{len}(\mathrm{Sel}(L_T) \cap \mathrm{Sel}(L_0)) \leq v(P^1(y)) + v(G(x)).$$

By part 1 of the lemma above, $G(x) = P^0(y)$. So $P(x)$ divides $P^0(y) P^1(y)$ in $O'$. Apply $f$. $\square$

**Lemma.** Let $P$ bound the Selmer module of $T$ for $h_v : G_E \to \mathbb{Z}/q$ with places $S \cup J \cup \bar{J}$. Let $\zeta_v \in O'$ with $\zeta_v^q = 1$, $x = (\zeta_v - 1)_v$ and $\psi = \prod_v \zeta_v^{h_v}$. If $v_{O'}(P(x)) < v_{O'}(\ell^M)$, then $\mathrm{divisibleLength}\ J\ e\ \psi \leq v_{O'}(P(x))$.

Lean: `New.Selmer.SelmerDatum.divisibleLength_pointChar_le` (New/Congruences/Selmer/Line.lean).

*Proof.* By part 3 of the lemma above, $\mathrm{Sel}(x) = \mathrm{Sel}_J(T\psi) \bmod \ell^M$. So its length is at most $v_{O'}(P(x)) < v_{O'}(\ell^M)$. The lemma on levels with $a = \ell^M$ gives the bound for divisible coefficients. $\square$

**Theorem (The polynomial of a datum).** Let $O$ be a coefficient ring, $N \neq 0$, $2 n \# J \leq s_0$, $r \leq 1$ and $M \leq Nr$. Let the elements with $V_i$ act trivially on $T$ modulo $\ell^M$, and let the group tied at $J \setminus \{P_0\}$ have length at most $\beta_T$. There are $P$ over $O$ and $x_0 \in \bar{\mathbb{Z}}_\ell^J$ with $v(x_{0,v}) \geq r$ for all $v$, $v(P(x_0)) \leq \mathrm{normLength}(\beta_T) + s_0 r$, and $P$ bounds the Selmer module of $T$ for the characters of $d$.

Lean: `New.Selmer.SelmerDatum.exists_boundsSelmer_ellVal_eval_le` (New/Congruences/Selmer/Line.lean).

*Proof.* Take $P^0$ from the last theorem, and put $p_0 = P^0$ and $p_1 = P^1$ with coefficients in $\bar{\mathbb{Z}}_\ell$. Then $v(p_0(0)) = \mathrm{normLength}(v_O(P^0(0))) \leq \mathrm{normLength}(\beta_T)$, so $v_r(p_0) \leq \mathrm{normLength}(\beta_T)$. The Gauss valuation lemma gives $v_r(p_1) \leq s_0 r$. Choose $y$ with $v(y) \geq r$ at which both $p_0$ and $p_1$ take their Gauss valuations (`New.Selmer.exists_forall_ellVal_eval_eq_gaussVal`, Lib/General/NumberTheory/GaussValuation.lean). Take a coefficient ring $O' \supseteq O$ that contains $y$, and apply the last theorem with $O'$, the inclusion $e$ and $f = $ the inclusion into $\bar{\mathbb{Z}}_\ell$. Put $x_0 = (a_v y)_v$. Each coordinate has $v(x_{0,v}) \geq v(y) \geq r$. Then

$$v(P(x_0)) \leq v(p_0(y)) + v(p_1(y)) = v_r(p_0) + v_r(p_1) \leq \mathrm{normLength}(\beta_T) + s_0 r. \ \square$$

**Lemma.** Let $P$ bound the Selmer module of $T$, let $\zeta_v \in \bar{\mathbb{Z}}_\ell$ with $\zeta_v^q = 1$ and $x = (\zeta_v - 1)_v$. If $v(P(x)) < M$, then $T$ satisfies `TwistedLengthLe J ψ (v(P(x)))` for $\psi = \prod_v \zeta_v^{h_v}$.

Lean: `New.Selmer.SelmerDatum.twistedLengthLe_pointChar` (New/Congruences/Selmer/Line.lean).

*Proof.* For all large $O'$ the ring contains $O$ and all $\zeta_v$ (`New.CoeffRing.eventually_exists_toIntQpBar_eq`). In $O'$ the normalised valuation of $P(x)$ is $v(P(x))$ and that of $\ell^M$ is $M$. So $v_{O'}(P(x)) < v_{O'}(\ell^M)$, and the last lemma bounds the length. Normalise. $\square$

### All data and all systems at once

**Lemma.** For $g$ near $g_0$, $\rho_T(\iota_b(g)) \equiv \rho_T(\iota_b(g_0))$ modulo $\ell^M$ for each $b$.

Lean: `New.Selmer.SelmerDatum.eventually_reduceModPow_idOrConjInv_eq` (New/Congruences/Selmer/Line.lean).

*Proof.* $\rho_T \bmod \ell^M$ is locally constant, and $\iota_b$ is continuous. $\square$

**Definition.** Let $T_i$ be finitely many Selmer data over $O$. The exponent $M$ is a *torsion level* (`IsTorsionLevel`) if $\mathrm{normLength}(\beta_{T_i}) + 1 < M$ and $2\, \mathrm{rank}(T_i)\, v_O(\ell^M) + 1 < \# k_O$ for all $i$. For Stickelberger systems $Y_k$, $s_0$, $r$ and $N$, a set of *twist polynomials* (`TwistPolynomials`) consists of:

1. an auxiliary set $Q$ with $2\# Q \leq s_0$;
2. for each $\mathfrak{q} \in Q$ a map $\lambda_{\mathfrak{q}} : G_E \to \mathbb{Z}/\ell^N$ that comes from $\mathrm{Cl}_\mathbb{Q}$ with tame level $\mathfrak{q}$ (`IsFromU1`) and has $\lambda_{\mathfrak{q}}(g) = 1$ for some $g$ in inertia at $\mathfrak{q}$;
3. polynomials $P_i$ and $P_k$ over $\bar{\mathbb{Z}}_\ell$ in the variables $X_{\mathfrak{q}}$, and points $x_i$ and $x_k$ with coordinates of valuation at least $r$;
4. $v(P_i(x_i)) \leq \mathrm{normLength}(\beta_{T_i}) + s_0 r$ and $v(P_k(x_k)) \leq \beta_{Y_k} + s_0 r$;
5. for $\zeta_{\mathfrak{q}}^{\ell^N} = 1$, $\psi = \prod \zeta_{\mathfrak{q}}^{\lambda_{\mathfrak{q}}}$ and $x = (\zeta_{\mathfrak{q}} - 1)$: $\psi(\Theta_{Y_k, Q}) = P_k(x)$;
6. for the same $\psi$ and $x$: if $v(P_i(x)) < \mathrm{normLength}(\beta_{T_i}) + 1$, then $T_i$ satisfies `TwistedLengthLe Q ψ (v(P_i(x)))`.

Lean: `New.Selmer.IsTorsionLevel`, `New.Selmer.TwistPolynomials` (New/Congruences/Selmer/Line.lean).

**Theorem.** Let $(P_0, J, d)$ be tied primes for $V_i = \{g : \rho_{T_i}(g) \equiv 1 \bmod \ell^M\}$. Let each group tied at $J$ have length at most $\mathrm{glob}(T_i) + \mathrm{places}(T_i)$. Let $\rho_{T_i}(\iota_b(\varphi_{P_0})) \equiv \rho_{T_i}(\iota_b(g_0))$ modulo $\ell^M$, and $v(\vartheta_k(\varphi_{P_0}) - \vartheta_k(g_0)) \geq M'$ for the characters $\vartheta_k$ of the $Y_k$. Let $\mathrm{normLength}(\beta_{T_i}) + 1 < M$ and $\beta_{Y_k} + 1 < M'$. Let $c \geq 1$ bound the ranks of the $T_i$ and the numbers of exponents of the $Y_k$. Let $s_0 \geq 1$, $2c\# J \leq s_0$, $s_0 r < 1$, $M < N$, $M \leq Nr$ and $M' \leq Nr$. Then twist polynomials exist for $s_0$, $r$ and $N$.

Lean: `New.Selmer.nonempty_twistPolynomials_of_isTiedPrimes` (New/Congruences/Selmer/Line.lean).

*Proof.* Take $Q = J$ and $\lambda_v$ the character of $d(v)$. Then $r \leq 1$, since $s_0 \geq 1$ and $s_0 r < 1$. For each $T_i$, the release of the first prime for a datum bounds the group tied at $J \setminus \{P_0\}$ by $\beta_{T_i}$. The polynomial of a datum then gives $P_i$, $x_i$ and the bound in item 4, with $2\,\mathrm{rank}(T_i)\, \# J \leq 2c\# J \leq s_0$. For each $Y_k$, the point theorem of [the last section](/chapter/twisting-theorem/#stickelberger-systems-on-a-line) gives $x_k$ for $P_k = \mathrm{groupRingEval}(\mathrm{universalChar}, \Theta_{Y_k, J})$. Item 5 is the evaluation lemma for the universal character. For item 2, the tame generator $\gamma_v$ lies in inertia at $v$ and has $\lambda_v(\gamma_v) = 1$, and $\lambda_v$ comes from $\mathrm{Cl}_\mathbb{Q}$ by the auxiliary prime data. For item 6, $v(P_i(x)) < \mathrm{normLength}(\beta_{T_i}) + 1 < M$, and the last lemma of the previous part applies. $\square$

**Theorem (Twist polynomials).** Let $T_i$ and $Y_k$ be finitely many, let $g_0$ lie in inertia above a place of $S_0$ prime to $\ell$, and let $M$ be a torsion level. There is $s_0 \geq 1$ such that for every $r > 0$ with $s_0 r < 1$, twist polynomials exist for $s_0$, $r$ and all large $N$.

Lean: `New.Selmer.exists_twistPolynomials` (New/Congruences/Selmer/Line.lean).

*Proof.* Choose $c \geq 1$ that bounds all ranks and all numbers of exponents, and $M'$ with $\beta_{Y_k} + 1 < M'$ for all $k$. This is possible because $\beta_{Y_k} \neq \infty$. By the last lemma and the continuity of each $\vartheta_k$, there is a neighbourhood $W$ of $g_0$ such that for $g \in W$ and all $i$, $k$, $b$: $\rho_{T_i}(\iota_b(g)) \equiv \rho_{T_i}(\iota_b(g_0))$ modulo $\ell^M$ and $v(\vartheta_k(g) - \vartheta_k(g_0)) \geq M'$. The descent gives $s$ such that for every $N > M$ there are tied primes $(P_0, J, d)$ with $\# J \leq s$, $\varphi_{P_0} \in W$ and the tied groups bounded by $\mathrm{glob} + \mathrm{places}$. Its hypothesis on the residue field is the second part of the torsion level. Put $s_0 = 2c(1 + s)$. Then $s_0 \geq 1$ and $2c\# J \leq s_0$. Fix $r$. For $N$ large, $N > M$, $M \leq Nr$ and $M' \leq Nr$. The last theorem applies. $\square$

**Remark (Formalization).** The summand $1$ in $s_0 = 2c(1 + s)$ only makes $s_0$ positive. The polynomials $P_k$ of the systems are the values of the universal character, so item 5 holds at every root of unity. The polynomials $P_i$ of the data are chosen by `choose`, and only items 4 and 6 are used.
