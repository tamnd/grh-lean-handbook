---
title: Gauge bounds for chains
lean:
  - New/UpperBound/Divisibility/ChainValuation.lean
decls:
  - New.Data.natCast_notMem_and_star_notMem_piNPlaces_of_ne
  - New.Data.mem_integralAfter_of_mem_admissibleTranslations
  - New.Data.projOn_translateDatum
  - New.Data.exists_supported_translateDatum_eq
  - New.Data.IsWeakChainDatum.translateDatum_mem_standardData
  - New.Data.gaugeLe_chainCombination
  - New.Data.IsWeakChainDatum.gaugeLe_chain
  - New.Data.norm_star_piMBar_le_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Gauge bounds for chains

This section turns the plain sum of Section 5 into a $p$-adic bound. Each kernel product is bounded by the product of the gauge factors of its kernels. The gauge is ultrametric, so the whole sum has the same bound. The section first collects the facts on the translated data that the bound needs at a prime $p$: they are standard data at $p$, so the bounds of [theta kernels and gauges](/chapter/theta-kernels-gauges/) apply to them.

Throughout, $p$ is a prime with a fixed embedding $\iota_p : \mathbb C \to \mathbb C_p$. The data fix the integer $\bar\pi_M$ of $K$ of norm $M = p_0 p_1$. Its image in $E$ is the conjugate of $\pi_M$. A finite place $w$ of $E$ is *chosen* if $\pi_M \in w$. The integer $\pi$ of $E$ has $\pi\bar\pi = N$, and $\Pi_N$ is the set of primes of $E$ that divide $\pi$.

### Translations and their integrality

A tuple of translations is a family $x = (x_j)_{j \in \mathbb N}$, where $x_j$ is a finite adelic matrix with rows indexed by $X_{j+1}$ and columns by $X_j$. For a natural number $q$, the tuple $x$ is *admissible for $q$* if, for all $j$, all entries $i$ and all places $w$ with $q \notin w$,

$$v_w\big(\bar\pi_M\, x_j(i)\big) \le 1.$$

It is *supported on $q$* if $x_j(i)_w = 0$ at every place $w$ with $q \notin w$. These two sets are `New.Data.admissibleTranslations` and `New.Data.supportedTranslations` of [columns and the composite lift](/chapter/upper-bound-objects/#columns-and-the-composite-lift). For $\delta \in \mathcal O_K$ and a set $S$ of finite places, $\mathrm{Int}(\delta, S)$ is the group of vectors $y$ with $v_w(\delta y_i) \le 1$ for all $i$ and all $w \in S$ ([Definition](/decl/New.Parameters.integralAfter/)).

**Lemma.** Let $p \ne N$, and let $w$ be a place of $E$ above $p$. Then $N \notin w$, and $\bar w \notin \Pi_N$.

Lean: `New.Data.natCast_notMem_and_star_notMem_piNPlaces_of_ne` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* If $N \in w$, then $w$ lies above both primes $p$ and $N$, so $p = N$. If $\bar w \in \Pi_N$, then $\pi \in \bar w$, so $N = \pi\bar\pi \in \bar w$. As $N$ is fixed by conjugation, $N \in w$, which is excluded. $\square$

**Lemma.** Let $x$ be admissible for $q$. Let $S$ be a set of places such that, for each $w \in S$, $q \notin w$, and $\delta = \bar\pi_M$ or $\bar w$ is not chosen. Then $x_j \in \mathrm{Int}(\delta, S)$ for every $j$.

Lean: `New.Data.mem_integralAfter_of_mem_admissibleTranslations` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* Let $w \in S$ and let $i$ be an entry. Since $q \notin w$, $v_w(\bar\pi_M x_j(i)) \le 1$. If $\delta = \bar\pi_M$, this is the claim. Otherwise $\bar w$ is not chosen, so $\pi_M \notin \bar w$, and $\bar\pi_M \notin w$. So $v_w(\bar\pi_M) = 1$ and $v_w(x_j(i)) \le 1$. Since $\delta$ is integral, $v_w(\delta x_j(i)) \le v_w(x_j(i)) \le 1$. $\square$

### The translated data under projections

The datum of $x$ at $j$ is $v_{x,j} = \varrho_f(x_j)\,\theta^\circ_j$, the integral vacuum $\theta^\circ_j$ of $\mathrm{Hom}(X_j, X_{j+1})$ moved by the finite Heisenberg operator of $x_j$ ([Definition](/decl/New.Data.translateDatum/)). For a set $S$ of finite places, $P^S$ is the mean, over integral vectors $y$, of the Heisenberg operators at the part of $y$ above $S \cup \bar S$ (`New.Space.projOn`). If $P^S f = f$, then $P^S \varrho_f(y) f$ is $\varrho_f(y) f$ when $y$ is integral at every place of $S \cup \bar S$, and $0$ otherwise (`New.Space.projOn_finHeisenbergOp`).

**Lemma.** Let $x_j$ be integral at the places of $S \cup \bar S$, that is, $x_j \in \mathrm{Int}(1, S \cup \bar S)$. Then $P^S v_{x,j} = v_{x,j}$.

Lean: `New.Data.projOn_translateDatum` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* The integral vacuum is a scalar multiple of the vacuum, and $P^S$ fixes the vacuum. Apply the projection rule with $f$ the vacuum and $y = x_j$. Since $x_j$ is integral at $S \cup \bar S$, the indicator is $1$. $\square$

**Lemma.** Let $x$ be admissible for $q$. Then some $x'$, admissible for $q$ and supported on $Mq$, has the same data: $v_{x,j} = v_{x',j}$ for all $j$.

Lean: `New.Data.exists_supported_translateDatum_eq` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* Let $S$ be the set of places $w$ with $Mq \in w$, and let $e_S$ be the idempotent finite adele that is $1$ at $S$ and $0$ elsewhere. Put $x'_j = e_S x_j$.

*Step 1: $x'$ is admissible and supported.* At $w \in S$, $x'_j = x_j$ there, so the bound holds. At $w \notin S$, $x'_j$ is $0$ there. So $x'$ is admissible, and it is supported on $Mq$.

*Step 2: the other part is integral.* Let $w \notin S$. Then $q \notin w$ and $M \notin w$. As $M = \pi_M\bar\pi_M$, also $\pi_M \notin \bar w$, so $\bar w$ is not chosen. The lemma above, with $\delta = 1$, shows that $e_{S^c}x_j$ is integral at every place. So $e_{S^c}x_j$ lies in the standard lattice, and it fixes the vacuum ($\varrho_f(y)\,\mathrm{vac} = \mathrm{vac}$ for $y$ in the standard lattice, `New.Space.finHeisenbergOp_vacElem`).

*Step 3: the two parts.* The set $S$ is stable under conjugation, since $Mq$ is a rational integer. So $\overline{e_{S^c}}\,e_S = 0$. The composition rule $\varrho_f(a)\varrho_f(b) = \chi(\bar b \cdot a)\varrho_f(a + b)$, with $\chi$ a character and $\bar b\cdot a$ a product with the trace-one adele, gives

$$\varrho_f(e_S x_j)\,\varrho_f(e_{S^c}x_j)\,\mathrm{vac} = \varrho_f(x_j)\,\mathrm{vac},$$

with character value $1$, since the cross term vanishes. The left side is $\varrho_f(e_S x_j)\mathrm{vac}$ by Step 2. Multiply by the scale of the integral vacuum. $\square$

**Lemma.** Let $\Psi$ be a weak chain datum for the twist $\vartheta$, with $q = \mathrm{N}Q$ the product of the norms of the places of the twist. Let $p \ne N$ be prime to $q$. Let $x \in \mathrm{supp}\,\Psi$ and $j \in \mathbb N$. Let $\delta \in \mathcal O_K$ with $\delta = \bar\pi_M$ or $p \nmid M$. Then $v_{x,j}$ is standard data at $p$ for $\delta$: it lies in the $\mathcal O_\iota$-span of the vectors $\varrho_f(y)\theta^\circ_j$, $y \in \mathrm{Int}(\delta, \{w : p \in w\})$.

Lean: `New.Data.IsWeakChainDatum.translateDatum_mem_standardData` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* It suffices that $x_j \in \mathrm{Int}(\delta, \{w : p \in w\})$, since then $v_{x,j}$ is one of the spanning vectors. The support of a weak chain datum consists of tuples admissible for $qN$. Apply the lemma on admissible tuples, with $S$ the set of places above $p$. Let $w \mid p$. Then $q \notin w$, since $p$ is prime to $q$, and $N \notin w$ by the first lemma. So $qN \notin w$. If $\delta \ne \bar\pi_M$, then $p \nmid M$. If $\bar w$ were chosen, then $\pi_M \in \bar w$, so $M = \pi_M\bar\pi_M \in \bar w$, and $p \mid M$. So $\bar w$ is not chosen. $\square$

**Lemma.** $|\iota_p(\overline{\bar\pi_M})| \le 1$.

Lean: `New.Data.norm_star_piMBar_le_one` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* The number is an algebraic integer, and every embedding of an algebraic integer into $\mathbb C_p$ has absolute value at most $1$. $\square$

### The gauge of a chain combination

The gauge $\|\xi\|_g$ of a vector at a finite point is ultrametric: $\|\sum_a \xi_a\|_g \le C$ if every $\|\xi_a\|_g \le C$ and $C \ge 0$ (`New.weylGauge_sum_le`). It is homogeneous: $\|c\xi\|_g = |\iota_p c|\,\|\xi\|_g$ (`New.weylGauge_smul`). For base points $d \in G_j$, $d' \in G_{j+1}$ and $c \in \mathbb R$, the datum $\Phi$ *raises gauges by $c$ from $d$ to $d'$* if, for all $g$, $h$ and $\xi$,

$$\big\|J(\omega(g, h)\Phi)\,\xi\big\|_{hd'} \le \max(c, 0)\,\|\xi\|_{gd}$$

([Definition](/decl/New.Kernel.raises/)). The theta kernels of [theta kernels and gauges](/chapter/theta-kernels-gauges/) give data that raise gauges by explicit powers of $p$.

**Theorem (Gauge of a chain combination).** Let $\Phi$ be data such that the family $(\Psi(x)\cdot\mathrm{id}, \Phi_x)_{x \in \mathrm{supp}\,\Psi}$ is jointly invariant at stage $m$ for the lift kernels $k_j$ of $\vartheta$. Suppose:

1. $|\iota_p\Psi(x)| \le 1$ for every $x$;
2. $d_j \in G_j$ are base points and $r_j \in \mathbb R$ are numbers such that, for $x \in \mathrm{supp}\,\Psi$ and $j < m$, $\Phi_{x,j}$ raises gauges by $p^{r_j}$ from $d_j$ to $d_{j+1}$;
3. $\varphi$ is a source form with $\mathrm{GaugeLe}(d_0, 1, \varphi)$.

Then $\mathrm{GaugeLe}\big(d_m,\ p^{\sum_{j<m} r_j},\ \mathrm{CC}(\vartheta, \Psi, \Phi, m)\varphi\big)$.

Lean: `New.Data.gaugeLe_chainCombination` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* Let $h \in G_m$. Choose points $g$ with $g_m = h$. By the last theorem of Section 5,

$$\big(\mathrm{CC}\,\varphi\big)(h) = \sum_c \sum_{x \in \mathrm{supp}\,\Psi} \Psi(x)\,\mathrm{KP}(\Phi_x, \varphi, \mathrm{cp}(c, g), m).$$

By the ultrametric bound, used twice, it suffices to bound each term at $h d_m$ by $C = p^{\sum r_j} \ge 0$. Apply the lemma on sizes of kernel products of Section 5, with $\mathrm{size}_j(g, v) = \|v\|_{g d_j}$, factors $\max(p^{r_j}, 0) = p^{r_j}$ and $B = 1$. The step hypothesis is condition 2, and the base is condition 3. The class points have $\mathrm{cp}(c, g)_m = g_m = h$. So

$$\|\mathrm{KP}(\Phi_x, \varphi, \mathrm{cp}(c,g), m)\|_{hd_m} \le \prod_{j<m} p^{r_j} = p^{\sum_{j<m} r_j}.$$

By homogeneity and condition 1, the term with $\Psi(x)$ has gauge at most $|\iota_p\Psi(x)|\,p^{\sum r_j} \le p^{\sum r_j}$. $\square$

**Remark.** No denominator appears. This is the reason for the free levels. If the levels were not free, the class sum would have weights $1/\#\mathrm{Aut}$, and the ultrametric bound would lose the valuation of these weights.

The next result applies the theorem to the translated data changed by operators $t_j$. In [divisibility prime by prime](/chapter/divisibility/), the $t_j$ are operators of the Weil representation at $p$, and the factors $p^{r_j}$ come from [theta kernels and gauges](/chapter/theta-kernels-gauges/).

**Theorem (Gauge of a weak chain).** Let $\Psi$ be a weak chain datum for $\vartheta$, and let $p$ be prime to $q = \mathrm{N}Q$. Let $t_j$ be complex linear operators on the finite part of the Weil representation of $\mathrm{Hom}(X_j, X_{j+1})$. Suppose:

1. for $x \in \mathrm{supp}\,\Psi$, $a \in K_j$ and $b \in K_{j+1}$, $\omega(a, b)\,t_j(v_{x,j}) = t_j(\omega(a,b)\,v_{x,j})$;
2. for $x \in \mathrm{supp}\,\Psi$ and $j < m$, $t_j(v_{x,j})$ raises gauges by $p^{r_j}$ from $d_j$ to $d_{j+1}$;
3. $\varphi$ is a source form with $\mathrm{GaugeLe}(d_0, 1, \varphi)$.

Then the chain combination of $\Psi$ with the data $t_j(v_{x,j})$ sends $\varphi$ to a form with $\mathrm{GaugeLe}(d_m, p^{\sum_{j<m} r_j}, \cdot)$.

Lean: `New.Data.IsWeakChainDatum.gaugeLe_chain` (New/UpperBound/Divisibility/ChainValuation.lean).

*Proof.* *Joint invariance of the new data.* Let $a$ be a tuple with $a_j \in K_j$ and $a_j = 1$ for $j \ge m$, and let $\beta$ be a linear map from the tensor product to $V_m$. Apply the joint invariance of $\Psi$ with the translated data to the map $\beta \circ (t_{m-1} \otimes \dots \otimes t_0)$. By condition 1, $t_j$ commutes with the move $\omega(a_j, a_{j+1})$ on $v_{x,j}$. So the family $(\Psi(x)\cdot\mathrm{id}, (t_j v_{x,j})_j)$ is jointly invariant.

*Integrality of the coefficients.* A weak chain datum has $\Psi(x)$ integral away from $q$: $|\iota\Psi(x)| \le 1$ for every prime $l$ prime to $q$ and every ring map $\iota : \mathbb C \to \mathbb C_l$. Take $l = p$ and $\iota = \iota_p$.

Now apply the theorem above. $\square$

**Remark (Formalization).** The operators $t_j$ are only complex linear. Condition 1 is asked only on the data $v_{x,j}$ for $x$ in the support, and only for $a \in K_j$, $b \in K_{j+1}$, which is what the proof uses. The numbers $r_j$ are real, and $p^{r_j}$ is the real power. The factor in `raises` is $\max(c, 0)$, so that $0$ raises gauges by every $c$ and the set of such data is closed under sums; here $c = p^{r_j} > 0$, and the maximum is $c$.
