---
title: The global sieve
lean:
  - New/Spanning/MainTerm/GlobalSieve.lean
decls:
  - New.Filling.IsGlobalSieveSystem
  - New.Filling.BoundsDecay
  - New.Filling.scaledEntry
  - New.Filling.scaledHead
  - New.Filling.poissonConst
  - New.Filling.entryDensity
  - New.Filling.densitySum
  - New.Filling.densitySum_succ_le
  - New.Filling.re_le_of_last_entries_ne
  - New.Filling.re_sum_sum_le_densitySum_add
  - New.Filling.densitySum_succ_le_mul_densitySum_add
  - New.Filling.densitySum_le
  - New.Filling.decayConst
  - New.Filling.boundsDecay_prod
  - New.Filling.globalWeight
  - New.Filling.sq_sum_globalWeight_le
  - New.Filling.sieve
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The global sieve

This section proves the sieve: for a sieve system over the infinite places and $T$, the sum of the top forms over heads of units of $E$ is at most the product of the constants of Poisson summation times the mass, plus a small error. The entries are removed one at a time, from the last to the first. Each removal is one application of one-sided Poisson summation.

### The setting

The scales are those of [the data and its sizes](/chapter/data-and-sizes/): $\kappa_v = \operatorname{Re}(M\Phi_v\varpi/(2\pi i))$, with $1 \leq |\kappa_v| \leq b^{23}$ for admissible data, and the entry $a$ is scaled at $v$ by $s_{v,a} = \kappa_v^{2(\varrho - a)}/N$. The integer exponent $\varrho - a$ is a truncated difference, so $s_{v,a} = 1/N$ for $a \geq \varrho$.

**Definition (Global sieve system).** A *global sieve system* of length $n$ is a sieve system on $\mathbb C^f \times \mathcal L_T$ with the entry map $x \mapsto \operatorname{unitOrOne}$ in each component, the map $\iota$ that is $w \mapsto w^{-1}$ at each infinite place and $w \mapsto M^{-1}w^{-1}$ at $T$, and the twist $\chi$ of [Section 3](/chapter/main-term/#frequencies-and-poisson-summation).

Lean: `New.Filling.IsGlobalSieveSystem` (New/Spanning/MainTerm/GlobalSieve.lean).

**Definition (Bounded decay).** A decay $\beta$ is *summed to at most $\varepsilon$* if for every entry $a$, every $c \in \mathbb C^f$ with $|c_v|^{-1} \leq |\kappa_v|/M$, and every finite set $X$ of nonzero elements of $E$ integral off $T$,
$$\sum_{y \in X}\beta\bigl(\operatorname{pt}_{(c_v/s_{v,a})_v}(y)\bigr) \leq \varepsilon.$$

Lean: `New.Filling.BoundsDecay` (New/Spanning/MainTerm/GlobalSieve.lean).

Two choices of $c$ occur. Poisson summation uses $c_v = 2\pi i/\Phi_v\varpi$, for which $|c_v|^{-1} = |\kappa_v|/M$. Two heads with different entries use $c_v = M$, for which $|c_v|^{-1} = 1/M \leq |\kappa_v|/M$ because $|\kappa_v| \geq 1$.

**Definition (Scaled heads and densities).** Let $A$ be a finite set of units of $E$. The entry $a$ of $t \in E^\times$ is $\operatorname{pt}_{s_{\cdot,a}}(t)$. For $p : \{0, \dots, i-1\} \to A$ and $t \in E^\times$, the scaled head $h(p, t)$ has the entries $p_0, \dots, p_{i-1}$, then $t$, then $1, 1, \dots$, each scaled at its position. The constant of Poisson summation at $a$ is $c_a = \operatorname{vol}\hat{\mathcal O}/\prod_v s_{v,a}^2$. The entry density at $x$ is
$$\rho_i(x) = \sum_{p, q : \{0..i-1\} \to A} J_{i+1}\bigl(h(p,1)[i \mapsto x], h(q,1)[i \mapsto x]\bigr),$$
and the density sums are $D_0 = \operatorname{Re} J_0(h(\emptyset, 1), h(\emptyset, 1))$ and $D_{i+1} = \sum_{t \in A}\operatorname{Re}\rho_i(\operatorname{pt}_{s_{\cdot,i}}(t))$.

Lean: `New.Filling.scaledEntry`, `New.Filling.scaledHead`, `New.Filling.poissonConst`, `New.Filling.entryDensity`, `New.Filling.densitySum` (New/Spanning/MainTerm/GlobalSieve.lean).

At $x = \operatorname{pt}(t)$, $\rho_i$ is the sum over the heads $h(p, t)$, $h(q, t)$ with the common entry $t$ at $i$. By [nonnegativity](/chapter/main-term/#sieve-systems), $\rho_i(x) \geq 0$ for every $x$.

### One entry fewer

**Lemma (Poisson in one entry).** Let $S$ be admissible, let $J$ be a global sieve system of length $n$ with weights $\Lambda$ and decay $\beta$ summed to at most $\varepsilon$, let the elements of $A$ be integral off $T$, and let $i \leq n$. Then
$$D_{i+1} \leq c_i\Bigl(\varepsilon\Bigl(\sum_p \Lambda_i(h(p,1))\Bigr)^2 + \operatorname{Re}\sum_{p,q} J_i(h(p,1), h(q,1))\Bigr).$$

Lean: `New.Filling.densitySum_succ_le` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* Apply [one-sided Poisson summation at $T$](/chapter/main-term/#frequencies-and-poisson-summation) to $F = \operatorname{Re}\rho_i$, with the scales $r_v = s_{v,i}$ and the set $V = A$. The function $F$ is nonnegative and integrable by the summed recursion. It is lower semicontinuous at each point $\operatorname{pt}(t)$, $t \in A$: that point is a unit, $\operatorname{unitOrOne}$ is continuous at units, and the lemma on lower semicontinuity of [Section 2](/chapter/main-term/#sieve-systems) applies. Since $\rho_i$ is real, $\int\chi(\xi x)F(x)\, dx$ is the twisted integral of the summed recursion, of modulus at most $\beta(\xi)(\sum_p\Lambda_i(h(p,1)))^2$. Take $M = (\sum_p \Lambda_i)^2$. The frequencies of Poisson summation are at the scales $2\pi i/(\Phi_v\varpi\, s_{v,i})$, which is the case $c_v = 2\pi i/\Phi_v\varpi$ of bounded decay. Finally $\int F = \operatorname{Re}\sum_{p,q}J_i$ by the summed recursion. $\square$

**Lemma (Different entries).** Let $\Lambda \geq 0$, let $1/M$ and the inverses of the elements of $A$ be integral off $T$, and let $i < n$. For $t \neq s$ in $A$ and any $p, q$,
$$\operatorname{Re} J_{i+1}(h(p, t), h(q, s)) \leq \varepsilon\,\Lambda_{i+1}(h(p,t))\,\Lambda_{i+1}(h(q,s)).$$

Lean: `New.Filling.re_le_of_last_entries_ne` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* Let $y = M^{-1}(t^{-1} - s^{-1})$. Then $y \neq 0$, and $y$ is integral off $T$. The frequency $\iota(h(p,t)_i) - \iota(h(q,s)_i)$ is $\Phi_v(t^{-1} - s^{-1})/s_{v,i} = (M/s_{v,i})\Phi_v y$ at $v$ and $y$ at $T$, that is $\xi = \operatorname{pt}_{(M/s_{v,i})_v}(y)$, a unit. Condition 6 of a sieve system gives $|J_{i+1}| \leq \beta(\xi)\Lambda\Lambda$. Bounded decay with $c_v = M$ and $X = \{y\}$ gives $\beta(\xi) \leq \varepsilon$. The real part is at most the modulus, and $\Lambda \geq 0$. $\square$

**Lemma (Equal last entries).** Under the same hypotheses, with $\varepsilon \geq 0$ and $i \leq n$,
$$\operatorname{Re}\sum_{p,q}J_i(h(p,1), h(q,1)) \leq D_i + \varepsilon\Bigl(\sum_p\Lambda_i(h(p,1))\Bigr)^2.$$

Lean: `New.Filling.re_sum_sum_le_densitySum_add` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* For $i = 0$ there is one pair of empty heads, the left side is $D_0$, and $\varepsilon(\cdot)^2 \geq 0$. For $i = j + 1$, write a head of length $j + 1$ as its first $j$ entries and its last entry $t$. The pairs with the same last entry give $\sum_t \operatorname{Re}\rho_j(\operatorname{pt}(t)) = D_{j+1}$. Each pair with different last entries gives at most $\varepsilon\Lambda\Lambda$ by the previous lemma, since $j < n$. These pairs form a part of all pairs, and the terms $\varepsilon\Lambda\Lambda$ are $\geq 0$, so their sum is at most $\varepsilon(\sum_p\Lambda_i)^2$. $\square$

**Lemma (One step).** If also the elements of $A$ are integral off $T$, then for $i \leq n$
$$D_{i+1} \leq c_i\Bigl(D_i + 2\varepsilon\Bigl(\sum_p\Lambda_i(h(p,1))\Bigr)^2\Bigr).$$

Lean: `New.Filling.densitySum_succ_le_mul_densitySum_add` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* Combine the last two lemmas; $c_i \geq 0$. $\square$

**Theorem (All entries removed).** Let $J$ be a global sieve system with $|J_0| \leq E_0$, let $\Gamma$ satisfy $(\sum_p\Lambda_i(h(p,1)))^2 \leq \Gamma\prod_{a<i}c_a$ for all $i \leq n$, and let $i \leq n + 1$. Then
$$D_i \leq \prod_{a < i}c_a\,(E_0 + 2i\Gamma\varepsilon).$$

Lean: `New.Filling.densitySum_le` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* By induction on $i$. $D_0 \leq |J_0| \leq E_0$. If the claim holds for $i \leq n$, the step gives $D_{i+1} \leq c_i(\prod_{a<i}c_a(E_0 + 2i\Gamma\varepsilon) + 2\varepsilon\Gamma\prod_{a<i}c_a) = \prod_{a \leq i}c_a(E_0 + 2(i+1)\Gamma\varepsilon)$. $\square$

### The constants

The decay of the product system is $\beta(\xi) = \prod_v \Theta\, b^{2000n^9}\ell_{k-n^7}(|\xi_v|^{-1}) \cdot \beta_T(\xi_T)$, where $\Theta$ is the scaled volume ratio of the shape. Put
$$\operatorname{decayConst} = \prod_v \Theta\Bigl(\frac{|\kappa_v|^{2\varrho+1}}{MN}\Bigr)^{k - n^7}.$$

Lean: `New.Filling.decayConst` (New/Spanning/MainTerm/GlobalSieve.lean).

**Lemma (The decay is summed).** For admissible $S$, this $\beta$ is summed to at most $\varepsilon = \operatorname{decayConst}\cdot b^{2002n^9f}$.

Lean: `New.Filling.boundsDecay_prod` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* Fix $a$, $c$ and $X$. Put $x_v = \kappa_v^{2\varrho+1}/(MN)$ and $B = (b^{23})^{2\varrho+1}$. Since $s_{v,a} \leq |\kappa_v|^{2\varrho}/N$ and $|c_v|^{-1} \leq |\kappa_v|/M$, the frequency scale satisfies $|c_v/s_{v,a}|^{-1} \leq |x_v|$; and $|x_v| \leq |\kappa_v|^{2\varrho+1} \leq B$. The [sum of the decays](/chapter/main-term/#frequencies-and-poisson-summation) with $k - n^7$ in place of $k$ bounds the sum of the variable factors by $\prod_v|x_v|^{k-n^7}(bB^2)^3$. Here $(bB^2)^3 = b^{3 + 138(2\varrho+1)} \leq b^{n^9}$, since $\varrho \geq 10^5$. The constant factors are $\prod_v\Theta b^{2000n^9}$ and $b^{n^9f}$ from $\beta_T$. The product is $\operatorname{decayConst}\cdot b^{(2000 + 1 + 1)n^9f}$. $\square$

**Definition (Global weight).** For a head $p$ of length $i$, let $\delta_l$ be the product of its first $l+1$ entries. The weight is $\prod_v\Lambda_{b^{60n^2}, n^6}(i, p^{(v)})$ times the finite head weight $\prod_{l<i}[\mathcal O : \delta_l\mathcal O]^{n^6/2}$, which is $0$ unless every $\delta_l$ lies in $\mathcal O$.

Lean: `New.Filling.globalWeight` (New/Spanning/MainTerm/GlobalSieve.lean).

**Lemma (Sum of the weights).** For admissible $S$, $A$ integral off $T$ and $i \leq \varrho$,
$$\Bigl(\sum_p \operatorname{globalWeight}_i(h(p,1))\Bigr)^2 \leq b^{400n^9f}\prod_{a<i}c_a.$$

Lean: `New.Filling.sq_sum_globalWeight_le` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* A head with nonzero weight has partial products $\delta$ that are integral at $T$, hence algebraic integers, with $|s\Phi_v\delta| \leq b^{60n^2}$ for the products $s$ of the scales. The products determine the head. Counting algebraic integers in a box, at most $(1 + 2b^{120n^2})^{2if}$ heads have nonzero weight. Each nonzero weight is at most $b^{120n^8fi}$. So the sum is at most $b^{130n^9f}$. The product of the first $i$ constants is at least $b^{-100n^2f}$, since $s_{v,a} \leq b^{46\varrho}$ and $\operatorname{vol}\hat{\mathcal O} = (2/\operatorname{rd})^f$. Hence the square is at most $b^{260n^9f}\cdot b^{100n^2f}\prod c_a \leq b^{400n^9f}\prod c_a$. $\square$

### The sieve

**Theorem (The sieve).** Let $S$ be admissible. Let $A$ be a finite set of units of $E$ with $t$ and $t^{-1}$ integral off $T$ for $t \in A$, let $1/M$ be integral off $T$, and let $U \subseteq A$. Let $J_T$ be a sieve system on $\mathcal L_T$ of length $\varrho$ with $\operatorname{unitOrOne}$, $\iota(w) = M^{-1}w^{-1}$, the character $\psi_T$, a bound $E_T$, the weights $\prod_{l<i}[\mathcal O:\delta_l\mathcal O]^{n^6/2}$ and the decay $\beta_T$. Let $\operatorname{bandLimit}_v$ be the forms of the Bessel system at $v$. Then
$$\begin{aligned} &\operatorname{Re}\sum_{t \in U}\sum_{p, q : \{0..\varrho-1\} \to A}\prod_v \operatorname{bandLimit}_{v,n}(x_v(p,t), x_v(q,t))\cdot J_{T,n}(y(p,t), y(q,t)) \\ &\qquad\leq \prod_{i<n}c_i\Bigl(\prod_v\frac{1 + b^{-10}}{\deg_v}E_T + b^{2403n^9f}\operatorname{decayConst}\Bigr).\end{aligned}$$
Here $x_v(p,t)_a = \operatorname{unitOrOne}(s_{v,a}\Phi_v(\text{entry } a))$ and $y(p,t)$ is the image at $T$ of the head $p_0, \dots, p_{\varrho-1}, t, 1, 1, \dots$.

Lean: `New.Filling.sieve` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* The Bessel system at $v$ is a sieve system on $\mathbb C$ with the bound $(1 + b^{-10})/\deg_v$, the weights $\Lambda_{b^{60n^2}, n^6}$ and the decay $\Theta b^{2000n^9}\ell_{k-n^7}(|\xi|^{-1})$ ([Bessel functions at a real place](/chapter/bessel-real-place/)). By the [product of sieve systems](/chapter/main-term/#sieve-systems), the products $J$ of these forms and $J_T$ form a global sieve system with the bound $E_0 = \prod_v(1+b^{-10})/\deg_v\cdot E_T$, the global weights, and the decay of the lemma on summed decay. The left side is $\sum_{t\in U}\operatorname{Re}\rho_\varrho(\operatorname{pt}(t))$, and each term is $\geq 0$, so it is at most $D_n$. Apply the theorem on all entries removed with $i = n$, $\varepsilon = \operatorname{decayConst}\cdot b^{2002n^9f}$ and $\Gamma = b^{400n^9f}$. Finally $2n \leq k \leq b \leq b^{n^9f}$, so $2n\Gamma\varepsilon \leq b^{2403n^9f}\operatorname{decayConst}$. $\square$

**Remark (Formalization).** The sizes $\varrho \geq 10^5$, $k \leq b$ and $1000 \leq b$ come from the admissibility of $S$. The sieve uses the bound $10^5 \leq \varrho$ of `New.Filling` (finding F-090 of [the register](/chapter/register-of-findings/#hypotheses-and-sizes)). The exponent $k - n^7$ and the positions $\varrho - a$ are truncated differences of natural numbers. The first is a true difference since $n^7 < k$. The second is $0$ for $a \geq \varrho$, which is the intended scale $1/N$ of the last entry.
