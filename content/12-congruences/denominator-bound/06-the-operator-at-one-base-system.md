---
title: The operator at one base system
lean:
  - New/Congruences/FirstOrder/DenominatorBound.lean
decls:
  - New.Selmer.IsWeakLift
  - New.Selmer.IsNonzeroIn
  - New.Selmer.IsLiftWithTwistedLattice
  - New.Selmer.liftValuationBound
  - New.Selmer.invAvatar_eq_one_of_mem_inertiaAbove
  - New.Selmer.exists_eventually_hasRootChain_mostFrobeniiAt
  - New.Selmer.exists_taylorWilesPlaces_hasRootChain
  - New.Selmer.norm_charpoly_coeff_le_one_of_continuous
  - New.Selmer.exists_det_one_sub_ne_zero
  - New.Selmer.exists_prod_sub_det_one_sub_eq_zero
  - New.Selmer.exists_dvd_prime_pow_succ
  - New.Selmer.normalizingAvatar_tameGenerator
  - New.Selmer.exists_isCommonRibetElement_ellVal_le
  - New.Selmer.exists_ellVal_le_and_diagOp_mem_ellIntegralForms
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The operator at one base system

This section runs Ribet's method once. The input is one system $x_0$ that lifts a main summand. The output is a level $L$ of auxiliary places and a function $s$ on the systems of level $L$ such that $N^2 s(x_0)$ has valuation at most $\mathrm{liftValuationBound}$, and the diagonal operator $\mathrm{diagOp}(s)$ makes integral the forms that are supported on lifts and agree with an integral form off the weak lifts.

Fix a descent pair $O$ of ranks $\#r < \#n$, a twist $\vartheta$ with modulus $\vartheta.Q$ and $\ell$-adic character $\vartheta^{-1}_\ell$ = `ϑ.invAvatar`, and base data $B$ ([the base level](/chapter/main-summands/#the-auxiliary-places-and-the-base-level)). A *system* is an isotypic space $x$ of forms, with Galois representation $x.\mathrm{galRep}$ and normalised representation $N_x$ = `normalisedRep O x.galRep` ([avatars](/chapter/main-summands/)).

### The definitions

**Definition (Weak lift).** A system $x$ is a *weak lift* if $\det(1 - N_x(g)) = 0$ for every $g \in G$, that is, the characteristic polynomial of every $N_x(g)$ has the root $1$.

Lean: `New.Selmer.IsWeakLift` (New/Congruences/FirstOrder/DenominatorBound.lean).

A true lift has $N_x = \vartheta^{-1}_\ell R \oplus \bigoplus_{e < t'} \chi^e$, and $\chi^0 = 1$ gives the root $1$. A weak lift need not be a lift. The method treats weak lifts that are not lifts as *false lifts*.

**Definition (Nonzero in a system).** A form $v$ is *nonzero in* $x$ if its algebraic form `v.toSmoothForm` lies in $x$ and is not $0$.

Lean: `New.Selmer.IsNonzeroIn` (New/Congruences/FirstOrder/DenominatorBound.lean).

**Definition (Lift with a twisted lattice).** For a bound $\mathrm{sel}$ and systems $x_0, x$, the system $x$ *lifts with a twisted lattice* if there are jumps $\mathrm{wt}$ and a representation $R$ of rank $\#r$ such that: $R$ is a main summand with $t'$ characters; the trace of $N_x$ is $\vartheta^{-1}_\ell \operatorname{tr} R + \sum_{e < t'} \chi^e$ (`New.Selmer.HasLiftTrace`); $\vartheta^{-1}_\ell R$ has a twisted lattice on which some $\gamma$ acts by a scalar $y$; and, if $x = x_0$, the divisible Selmer length of the twisted row is at most $\mathrm{sel}$ (`New.Selmer.HasDivisibleSelmerLengthLe`).

Lean: `New.Selmer.IsLiftWithTwistedLattice` (New/Congruences/FirstOrder/DenominatorBound.lean).

**Definition (The lift bound).** $\mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel}) = \mathrm{sel} + 2t'\,\mathrm{ram} + \#r\, \mathrm{loc}_\ell + e_\ell$ in $[0, \infty]$, with $t' = $ `O.rankDiff`.

Lean: `New.Selmer.liftValuationBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

### Auxiliary places

**Lemma (The twist is unramified above $p_0 p_1$).** If $\vartheta$ is an auxiliary twist with cost $\mathrm{ram}$ and $\gamma$ lies in inertia above $S_M$, then $\vartheta^{-1}_\ell(\gamma) = 1$.

Lean: `New.Selmer.invAvatar_eq_one_of_mem_inertiaAbove` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Let $\gamma$ lie in the inertia group at a place $v \in S_M$. The place $v$ is bad, since it lies above $p_0 p_1$. An auxiliary set avoids the bad places, and so do the conjugates of its places. So $v$ is neither in $\vartheta.Q$ nor the conjugate of a place in $\vartheta.Q$. A character from $U(1)$ with modulus $\vartheta.Q$ (`New.IsFromU1`) is trivial on the inertia above every place outside $\vartheta.Q$ and its conjugates. So $\vartheta^{-1}_\ell(\gamma) = 1$. $\square$

**Lemma (Root chains at most Frobenius elements).** Let $\vartheta$ be an auxiliary twist and $B$ base data whose systems of base level have integral characteristic polynomials. Let $R$ be a main summand with $t'$ characters. For every $\nu$ and $g$ there is $\delta$ with $\mathrm{cyc}(\delta) = 1$ such that, for most Frobenius data $y$ at $\delta^{\ell^\nu} g$ (the filter `mostFrobeniiAt`):

- (a) the place of $y$ is not bad and is off the base level;
- (b) if $x$ is a weak lift of base level and $\operatorname{charpoly} N_x(\mathrm{Frob}_y)$ is congruent coefficientwise, modulo the maximal ideal, to $S \cdot \prod_{i < t'} (X - \chi(\mathrm{Frob}_y)^i)$ for some $S$ with $\|S(1)\| \geq 1$, then the Hecke polynomial of $x$ at the place has a root chain $\prod_{i<t'}(X - q^i)$ times a divisor of an integral $e$ with $e(1) = 1$, after rescaling by the normalizing character ([root chains](/chapter/first-order-deformations/#root-chains-of-weak-lifts));
- (c) $\|\operatorname{charpoly}(\vartheta^{-1}_\ell R)(\mathrm{Frob}_y)(1)\| \geq 1$.

Lean: `New.Selmer.exists_eventually_hasRootChain_mostFrobeniiAt` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* A main summand has an inertial element $\gamma$ above $S_M \setminus S_\ell$ (the field `New.Selmer.IsMainSummandLike.exists_scalar_inertia`) that acts on $R$ by a scalar $y$ with $\|(y^{\ell^a})^j - 1\| = 1$ for $1 \leq j \leq 4\#r + 2$ By the previous lemma and since $\mathrm{cyc}$ is unramified there, $\gamma$ is killed by the twist and by $\mathrm{cyc}$. A power $\delta = \gamma^i$ moves the eigenvalues of the twist away from $1$, which gives (c) for most Frobenius elements ([the norm lemma](/decl/New.Selmer.exists_eventually_one_le_norm_eval_charpoly/)). Part (a) holds for most Frobenius elements since the bad places and the base level are finite. Part (b) concerns finitely many systems; for each, [the root chain theorem](/decl/New.Selmer.eventually_exists_hasRootChain/) gives the chain for most Frobenius elements. $\square$

**Theorem (Taylor-Wiles places with root chains).** Let $c$ be a lift setting for $O$ and $\vartheta$, $\vartheta$ an auxiliary twist with cost $\mathrm{ram}$, and $B$ base data with integral characteristic polynomials at base level. Let $x_0$ have $\operatorname{tr} N_{x_0} = \vartheta^{-1}_\ell \operatorname{tr} R + \sum_{e<t'} \chi^e$ for a main summand $R$. Let $g_1$ generate $G$ modulo $\ker \mathrm{cyc}$, with $\mathrm{cyc}(g_1)^a - 1 \mid \ell^h$ for $0 < a < t$, and $\ell \leq h_{\mathrm{gap}}^2$ or $h = 0$. Then there are a finite linear order $J$ and a monotone map $\mathrm{exponent}$ from $J$ to $\{0 < e < t'\}$ such that for each $\nu > 0$ some Taylor-Wiles places $Q$ of level $\ell^\nu$ indexed by $J$ satisfy:

- (a) they form a triangle of primes for $g_1^{-1}$ with separation $h_{\mathrm{gap}} h$ and total $h_{\mathrm{gap}}^{22} h$;
- (b) they are not bad and are off the base level;
- (c) there are $e_j \in \overline{\mathbb{Z}}_\ell[X]$ with $e_j(1) = 1$ such that every weak lift $x$ of base level congruent to $x_0$ has at the place $j$ a root chain of length $t'$ with cofactor dividing $e_j$.

Lean: `New.Selmer.exists_taylorWilesPlaces_hasRootChain` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Let $W$ be the set of Frobenius data that satisfy (a), (b), (c) of the previous lemma. The previous lemma says $W$ is in the filter at $\delta^{\ell^\nu} g$ for every $g$. The theorem [on triangles of primes](/decl/New.Selmer.exists_isPrimeTriangle/) builds a triangle inside $W$. It needs that the cyclotomic conductor plus $t'$ is less than $h_{\mathrm{gap}}$, and $f \geq 4$, which hold by the sizes of the data ($f \geq m^{22} \geq 4$).

The characteristic polynomials of $N_{x_0}$ equal those of $\vartheta^{-1}_\ell R$ times the chain $\prod_{i<t'}(X - \chi^i)$, since the traces of all powers agree. A system $x$ congruent to $x_0$ has characteristic polynomials congruent to the same product. So (b) applies with $S$ the polynomial of the twist, whose value at $1$ has norm at least $1$ by (c). It gives a cofactor $e_{j,x}$ for each of the finitely many such $x$. Put $e_j = \prod_x e_{j,x}$. Then $e_j(1) = 1$, and each cofactor divides $e_j$. $\square$

### Small lemmas

**Lemma.** Let $\rho : G \to \mathrm{GL}_n(\overline{\mathbb{Q}}_\ell)$ be continuous with $G$ compact. Then every coefficient of $\operatorname{charpoly} \rho(g)$ has norm at most $1$.

Lean: `New.Selmer.norm_charpoly_coeff_le_one_of_continuous` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* $\rho$ has a lattice over some coefficient ring ([lattices](/chapter/attached-representations/)). The characteristic polynomial of a matrix over $O$ has coefficients in $O$. $\square$

**Lemma.** Let the $u_x(g)$ have integral characteristic polynomials, and for each $x$ let some $u_x(g)$ not have the eigenvalue $1$. Then there are $\mathrm{elt}(x) \in G$ and nonzero $\mathrm{value}(x) \in \overline{\mathbb{Z}}_\ell$ with $\mathrm{value}(x) = \det(1 - u_x(\mathrm{elt}(x)))$.

Lean: `New.Selmer.exists_det_one_sub_ne_zero` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* $\det(1 - M) = \operatorname{charpoly}(M)(1)$, which is integral and nonzero for the chosen $g$. $\square$

**Lemma.** Let $Y$ be finite and the $u_x(g)$ have integral characteristic polynomials. There are finitely many $\mathrm{elt}(k)$ and nonzero $\mathrm{value}(k)$ such that $\prod_k (\mathrm{value}(k) - \det(1 - u_x(\mathrm{elt}(k)))) = 0$ for every $x$ such that some $u_x(g)$ does not have the eigenvalue $1$.

Lean: `New.Selmer.exists_prod_sub_det_one_sub_eq_zero` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Index $k$ by the $x$ with this property and apply the previous lemma. The factor at $k = x$ vanishes at $x$. $\square$

**Lemma.** A nonzero $b \in \overline{\mathbb{Z}}_\ell$ divides $\ell^{\nu + 1}$ for some $\nu$.

Lean: `New.Selmer.exists_dvd_prime_pow_succ` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* $\mathrm{ellVal}(b) < \infty$, so some $\nu \in \mathbb{N}$ exceeds it. Then $\ell^{\nu+1}/b$ has positive valuation and is integral. $\square$

**Lemma.** The normalizing character of $O$ is $1$ at the tame generator of a place prime to $\ell$.

Lean: `New.Selmer.normalizingAvatar_tameGenerator` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* The normalizing character is unramified away from $\ell$ ([avatars](/chapter/main-summands/)), and the tame generator lies in inertia. $\square$

### Ribet's element at one system

**Theorem (A common Ribet element with the lift bound).** Let $c$ be a lift setting for $O$ and $\vartheta$, with $\vartheta$ an auxiliary twist of cost $\mathrm{ram}$. Let $h \leq v_\ell(N)$, and let the places $w_j$ with tame generators $\tau_j$ and Frobenius elements $\varphi_j$ form a triangle of primes with separation $h_{\mathrm{gap}} h$ and total $h_{\mathrm{gap}}^{22} h$. Let $\mathrm{sys} : Y \to$ systems, $Y$ finite, with every $N_{\mathrm{sys}(x)}$ of the type with jumps $\mathrm{wt}$ and level $\vartheta.Q \cup \bar{\vartheta.Q} \cup w(J) \cup \overline{w(J)}$, and $(N(g) - \vartheta^{-1}_\ell(g))(N(g) - 1) = 0$ on inertia above $\vartheta.Q \cup \bar{\vartheta.Q}$. Let every system in $\mathcal{X}$ lift with a twisted lattice for $x_0 \in \mathrm{sys}^{-1}(\mathcal{X})$ and $\mathrm{sel} \neq \infty$. Let $\mathcal{J}$ be a trace ideal for the $N_{\mathrm{sys}(x)}$, $\ell^\nu$, $\tau$, $\varphi$ and polynomials $e_j$ with $e_j(1) = 1$. Then there is $d \in \overline{\mathbb{Q}}_\ell$ such that $d$ is a common Ribet element for $\mathcal{J}$ and the functions $x \mapsto \det(1 - N_{\mathrm{sys}(x)}(g))$ at $x_0$ (`New.Selmer.IsCommonRibetElement`), and
$$\mathrm{ellVal}(N^2 d) \leq \mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel}).$$

Lean: `New.Selmer.exists_isCommonRibetElement_ellVal_le` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* Choose for each lift the data of the definition. [Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations) (`New.Selmer.ribet_columns`) gives $d$ with $\mathrm{ellVal}(d) + 2 v_\ell(N) \leq \mathrm{liftValuationBound}$. Since $\mathrm{ellVal}(N^2 d) \leq \mathrm{ellVal}(N^2) + \mathrm{ellVal}(d) = 2 v_\ell(N) + \mathrm{ellVal}(d)$, the bound follows. $\square$

**Theorem (The operator at one base system).** Let $c$ be a lift setting for $O$ and $\vartheta$, with $\vartheta$ an auxiliary twist of cost $\mathrm{ram}$. Let every system in $\mathcal{X}$ lift with a twisted lattice for $x_0$, with $\mathrm{sel} \neq \infty$. Let $B$ be base data such that at every level made of places that are not bad, every system has $N_x$ of the type with jumps $\mathrm{wt}$ and satisfies the quadratic relation on inertia above $\vartheta.Q \cup \bar{\vartheta.Q}$. Let $x_0 \in \mathcal{X}$ be a system of base level. Then there are a finite level $L$ and $s$ on the systems of level $L$ such that:

- (a) $\mathrm{ellVal}(N^2 s(x)) \leq \mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel})$ for each $x$ above $x_0$;
- (b) let $l, y$ be forms of base level with $N l$ integral, let $y$ be killed by every $\mathrm{diagOp}(s_1)$ with $s_1 = 0$ on $\mathcal{X}$, and let $\mathrm{diagOp}(s_1)\, l = \mathrm{diagOp}(s_1)\, y$ for every $s_1$ that vanishes at the base systems that are not weak lifts. Then $N \cdot N \cdot \mathrm{diagOp}(s)\, y$ is integral.

Lean: `New.Selmer.exists_ellVal_le_and_diagOp_mem_ellIntegralForms` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* The characteristic polynomials of all $N_x$ are integral, by the first small lemma, since each $N_x$ is continuous.

*Step 1: the false lifts.* Apply the third small lemma to the systems of base level. This gives $\mathrm{elt}(k)$ and $\mathrm{value}(k) \neq 0$ such that $\delta_0 = \prod_k (\mathrm{value}(k) - \det(1 - N_x(\mathrm{elt}(k))))$ vanishes at every base system that is not a weak lift. Let $n_0 = \prod_k \mathrm{value}(k) \neq 0$.

*Step 2: the places.* Take $h$ and $g_1$ from [the cyclotomic generator](/chapter/denominator-bound/#tame-places-and-the-cyclotomic-generator). Put $\mathrm{bound} = 2\,(\#n)!\,(n_0 N^2)^{\#J + 1}$, nonzero, and take $\nu$ with $\mathrm{bound} \mid \ell^{\nu + 1}$ by the fourth small lemma. The theorem on Taylor-Wiles places at level $\nu + 1$ gives $J$, the triangle and the cofactors $e_j$.

*Step 3: clearing.* Apply [the clearing theorem](/decl/New.Patching.BaseLevel.exists_diagOp_mem_ellIntegralForms/) with the functions $\delta_g(x) = \det(1 - N_x(g))$, the product $\delta_0$ and $m = N^2$. Hypothesis 1 is part (c) of the places, since a base system with $\delta_0(x) \neq 0$ is a weak lift. Hypothesis 2 is the choice of $\nu$. Hypothesis 3 is the previous theorem: every trace ideal has a common Ribet element $d$ with $\mathrm{ellVal}(N^2 d) \leq \mathrm{liftValuationBound}$. The normalizing character is $1$ at the tame generators by the last small lemma. The theorem returns $s$ with (a) and (b). $\square$
