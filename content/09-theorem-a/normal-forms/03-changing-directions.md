---
title: Changing the directions
lean:
  - New/Derivatives/Divisibility/NullFrames.lean
decls:
  - New.exists_det_dvd_and_dvd_mulVec
  - New.exists_det_dvd_prod_and_dvd_mulVec
  - New.dvd_sum_pow_mul_of_root_dvd
  - New.deductionTerm
  - New.IsExemptPair
  - New.CongruenceChoice
  - New.exists_congruenceChoice_cost_eq_and_covers
  - New.norm_rpow_sum_cost_eq_prod_congruenceModulus
  - New.newDirection
  - New.exists_newDirection_dvd
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Changing the directions

The normal form makes a series integral in degree $B$ as soon as $\pi_p$ divides the couplings $\Gamma_e$ with $e \le \log_p B$, after the substitution. For the substitution $z(s)$ of Section 2 the coupling $\Gamma_e = \sum_{\tau, b, a} z_{\tau,b,a}^{p^e} z_{\tau',b,a}$, with $\tau'$ the partner of $\tau$, is a combination of the products $s^{p^e} s'$ of new variables. Modulo $p$, its coefficients are the *pairings*

$$\langle \beta, \beta' \rangle_e = \sum_{a \in n} \beta_a^{p^e}\, \beta'_a$$

of a new direction $\beta$ at $\tau$ with a new direction $\beta'$ at $\tau'$, times the row factors. This section chooses the matrices $g_{\tau,h}$ so that $\pi_p$ divides all pairings that matter, and bounds the valuations of their determinants. The source calls the file *null frames*: the new directions at a place and at its partner become orthogonal modulo $\pi_p$ for the pairing $\langle\cdot,\cdot\rangle_e$.

Throughout, $\pi \in \mathcal{O}$ divides $p$. Later $\pi = \pi_p$.

### Elimination

The first two lemmas are linear algebra over the valuation ring $\mathcal{O}$. They meet congruences on the rows of a matrix at the price of the product of the moduli.

**Lemma (One step of elimination).** Let $a \in \mathcal{O}^m$ and $\alpha \in \mathcal{O}$. There is an $m \times m$ matrix $u$ over $\mathcal{O}$ with $\det u \mid \alpha$ and $\alpha \mid (u a)_k$ for every $k$.

Lean: `New.exists_det_dvd_and_dvd_mulVec` (New/Derivatives/Divisibility/NullFrames.lean).

*Proof.* If $m = 0$ take $u = 1$. Otherwise choose $k_0$ such that $a_{k_0}$ has the least valuation. Then $a_k = a_{k_0} c_k$ with $c_k \in \mathcal{O}$ for all $k$. Let $u$ be the identity matrix with column $k_0$ replaced by the vector $b$ with $b_{k_0} = \alpha$ and $b_k = -c_k$ for $k \ne k_0$. Then $\det u = \alpha$. The row $k_0$ of $ua$ is $\alpha a_{k_0}$, and for $k \ne k_0$ the row $k$ is $-c_k a_{k_0} + a_k = 0$. $\square$

**Lemma (Elimination for several forms).** Let $t$ be a finite set of indices, $A_i \in \mathcal{O}^m$ and $\alpha_i \in \mathcal{O}$ for $i \in t$. There is an $m \times m$ matrix $g$ over $\mathcal{O}$ with $\det g \mid \prod_{i \in t} \alpha_i$ and $\alpha_i \mid (g A_i)_k$ for all $i \in t$ and all $k$.

Lean: `New.exists_det_dvd_prod_and_dvd_mulVec` (New/Derivatives/Divisibility/NullFrames.lean).

*Proof.* Induction on $t$, starting with $g = 1$. Given $g$ for $t$, apply the previous lemma to $gA_i$ and $\alpha_i$ for a new index $i$, and replace $g$ by $ug$. The determinant is multiplied by $\det u \mid \alpha_i$. The rows of $ug$ are integral combinations of the rows of $g$, so the old congruences still hold. $\square$

So a row $k$ of $g$ is a vector $g_k \in \mathcal{O}^m$ with $\alpha_i \mid g_k \cdot A_i$: each form $A_i$ gives one congruence on every row, at the cost of $\alpha_i$ in the determinant.

### The Frobenius step

A congruence for the pairing is not linear in $\beta$, because $\beta$ appears with the exponent $p^e$. The next lemma linearizes it with $p^e$-th roots. The ring $\mathcal{O}$ is integrally closed in the algebraically closed field $\mathbb{C}_p$, so every element of $\mathcal{O}$ has a $p^e$-th root in $\mathcal{O}$.

**Lemma (Frobenius step).** Let $O$ be a commutative ring, $\pi \mid p$ in $O$, $e \ge 0$, and let $x \mapsto \sqrt[p^e]{x}$ be a map with $(\sqrt[p^e]{x})^{p^e} = x$. If $\sqrt[p^e]{\pi}$ divides $\sum_a \sqrt[p^e]{y'_a}\, \beta_a$, then $\pi$ divides $\sum_a \beta_a^{p^e} y'_a$.

Lean: `New.dvd_sum_pow_mul_of_root_dvd` (New/Derivatives/Divisibility/NullFrames.lean).

*Proof.* Raise the divisibility to the power $p^e$: $\pi$ divides $(\sum_a \sqrt[p^e]{y'_a}\beta_a)^{p^e}$. The $p^e$-th power is additive modulo $p$ (`New.dvd_sum_pow_sub_sum`, in [Fitting ideals, lengths and coefficient rings](/chapter/fitting-ideals/)), and $\pi \mid p$, so $\pi$ divides the difference between this power and $\sum_a y'_a \beta_a^{p^e}$. $\square$

So a congruence on the pairing with a fixed vector $y'$ at the partner is a linear congruence on $\beta$, modulo $\sqrt[p^e]{\pi}$, whose valuation is $v(\pi)/p^e$. A congruence on the pairing with a fixed vector $y$ at the source, $\sum_a y_a^{p^e} \beta'_a$, is already linear in $\beta'$, modulo $\pi$.

### Exempt pairs and the deduction term

Fix a set of *marked* places; in the plain count it is empty. Fix a place $\sigma$, the *source*, a partner $\sigma'$ and an exponent $e$. The heights are counted only below $N$.

**Definition (Exempt pair).** The pair of a height $h$ at $\sigma$ and a height $h'$ at $\sigma'$ is *exempt* if $h = 1$, and either $\sigma$ is marked, or $h' = 1$ and $\sigma'$ is marked.

Lean: `New.IsExemptPair` (New/Derivatives/Divisibility/NullFrames.lean).

The charges of Section 4 pay for the exempt pairs, so no congruence is needed for them.

**Definition (Deduction term).** Let $t_\sigma$ be the number of columns of height one at $\sigma$ ($0$ if $\sigma$ is marked), $r_\sigma$ the number of columns of the other heights below $N$, and $B_\sigma$ the number of boxes in these. The *deduction term* is

$$\mathrm{ded}_e(\sigma, \sigma') = \min\Big(\frac{t_\sigma}{p^e},\ r_{\sigma'} + t_{\sigma'}\Big) + \frac{r_\sigma}{p^e} + \min\Big(\frac{B_\sigma}{p^e},\ B_{\sigma'}\Big).$$

Lean: `New.deductionTerm` (New/Derivatives/Divisibility/NullFrames.lean).

The term is a number of congruences, each counted with its valuation in units of $v(\pi)$: a congruence at the source costs $1/p^e$ and a congruence at the partner costs $1$.

### A choice of congruences

For the source $\sigma$ and the partner $\sigma'$ there are four kinds of congruence on the rows of the matrices $g_{\sigma,h}$ and $g_{\sigma',h'}$.

1. *Entries at the source*: all $h$ entries of each row of $g_{\sigma,h}$ are divisible by $\sqrt[p^e]{\pi}$.
2. *Pairing at the source*: each new direction $\beta$ of height $h$ at $\sigma$ satisfies $\sqrt[p^e]{\pi} \mid \sum_a \sqrt[p^e]{y_{\sigma',a,0}}\, \beta_a$, with the first given direction $y_{\sigma',\cdot,0}$ at the partner.
3. *Entries at the partner*: all $h'$ entries of each row of $g_{\sigma',h'}$ are divisible by $\pi$.
4. *Pairing at the partner*: each new direction $\beta'$ of height $h'$ at $\sigma'$ satisfies $\pi \mid \sum_a y_{\sigma,a,0}^{p^e}\, \beta'_a$.

A *choice of congruences* says, for each height, which of the four kinds are imposed (`New.CongruenceChoice`). Its *cost* is

$$\sum_{h<N}\Big(\frac{\mathrm{sc}(h)\,\kappa_\sigma(h)}{p^e} + \mathrm{pc}(h)\,\kappa_{\sigma'}(h)\Big),$$

where $\mathrm{sc}(h)$ is the number of congruences on one row of height $h$ at the source ($1$ for the pairing, $h$ for the entries) and $\mathrm{pc}(h)$ the same at the partner. The choice *covers* a pair $(h, h')$ if the entries of one of the two rows are imposed, or the pairing at the partner is imposed and $h = 1$, or the pairing at the source is imposed and $h' = 1$.

Why does a covered pair have a pairing divisible by $\pi$? A new direction of height one is a multiple of the first given direction, since $g_{\tau,1}$ is $1 \times 1$. So if $h = 1$ and the pairing at the partner is imposed, $\langle \beta, \beta' \rangle_e = g^{p^e} \sum_a y_{\sigma,a,0}^{p^e} \beta'_a$ is divisible by $\pi$. If $h' = 1$ and the pairing at the source is imposed, the Frobenius step gives $\pi \mid \sum_a \beta_a^{p^e} y_{\sigma',a,0}$, and $\langle\beta,\beta'\rangle_e$ is a multiple of it. If the entries at the partner are imposed, $\pi \mid \beta'$. If the entries at the source are imposed, $\sqrt[p^e]{\pi} \mid \beta$ and so $\pi \mid \beta^{p^e}$.

**Lemma (A choice of cost equal to the deduction term).** For every source $\sigma$, partner $\sigma'$ and exponent $e$ there is a choice of congruences whose cost is $\mathrm{ded}_e(\sigma,\sigma')$ and which covers every pair $(h, h')$ that is not exempt.

Lean: `New.exists_congruenceChoice_cost_eq_and_covers` (New/Derivatives/Divisibility/NullFrames.lean).

*Proof.* Let $\mathrm{A}$ be the statement $t_\sigma/p^e \le r_{\sigma'} + t_{\sigma'}$ and $\mathrm{L}$ the statement $B_\sigma/p^e \le B_{\sigma'}$. Impose:

- the pairing at the source for every height $h \ne 1$; this costs $r_\sigma/p^e$;
- the entries at the source for $h = 1$ if $\sigma$ is not marked and $\mathrm{A}$ holds, which costs $t_\sigma/p^e$; and for $h \ne 1$ if $\mathrm{L}$ holds, which costs $B_\sigma/p^e$;
- the entries at the partner for $h' \ne 1$ if $\mathrm{L}$ fails, which costs $B_{\sigma'}$;
- the pairing at the partner for every $h'$ if $\mathrm{A}$ fails, except $h' = 1$ when $\sigma'$ is marked; this costs $r_{\sigma'} + t_{\sigma'}$.

The cost is the sum of the two minima and $r_\sigma/p^e$, which is the deduction term. Now let $(h, h')$ be a pair that is not exempt. If $h \ne 1$ and $h' = 1$, the pairing at the source covers it. If $h \ne 1$ and $h' \ne 1$, the entries at the source cover it if $\mathrm{L}$ holds and the entries at the partner if not. If $h = 1$, then $\sigma$ is not marked, and $h' \ne 1$ or $\sigma'$ is not marked. If $\mathrm{A}$ holds the entries at the source cover it; if not, the pairing at the partner is imposed at $h'$ and $h = 1$. $\square$

The choice takes the cheaper side twice. Columns of height one are cheap at the source, because a congruence there has valuation $v(\pi)/p^e$, but the pairing at the partner covers them for all heights $h'$ at once. Columns of height $h \ne 1$ need a congruence against every height at the partner, so the source pays one pairing for $h' = 1$ and then the cheaper of the two sides for the entries.

### The new directions

**Definition (New direction).** For matrices $g_{\tau,h}$ of size $h \times h$ and given directions $y_{\tau,\cdot,k'}$, the new direction $k$ of height $h$ at $\tau$ is

$$\beta_{\tau,h,k} = \sum_{k'<h} (g_{\tau,h})_{k,k'}\, y_{\tau,\cdot,k'}.$$

Lean: `New.newDirection` (New/Derivatives/Divisibility/NullFrames.lean).

**Theorem (Changing the directions).** Let $\pi \in \mathcal{O}$ divide $p$. Let $\mathrm{pr}_e$ be a map on places for each $e$, $S$ a finite set of exponents, $N \ge 0$, $\kappa$ the numbers of columns, a set of marked places, and $y$ integral directions. There are integral matrices $g_{\tau,h}$ with these two properties.

1. For $e \in S$, every place $\tau$, heights $h$, $h'$ and directions $k < h$, $k' < h'$ such that the pair $(h, h')$ is not exempt for $\tau$ and $\mathrm{pr}_e\tau$, the element $\pi$ divides $\langle \beta_{\tau,h,k},\ \beta_{\mathrm{pr}_e\tau,h',k'} \rangle_e$.
2. The determinants satisfy
$$\|\pi\|^{\sum_{e \in S}\sum_\tau \mathrm{ded}_e(\tau, \mathrm{pr}_e\tau)} \le \prod_\tau \prod_{h<N} \|\det g_{\tau,h}\|^{\kappa_\tau(h)}.$$

In valuations, property 2 says $\sum_{\tau,h<N} \kappa_\tau(h)\, v(\det g_{\tau,h}) \le v(\pi) \sum_{e\in S}\sum_\tau \mathrm{ded}_e(\tau, \mathrm{pr}_e\tau)$.

Lean: `New.exists_newDirection_dvd` (New/Derivatives/Divisibility/NullFrames.lean).

*Proof.* Choose a $p^e$-th root $\sqrt[p^e]{\pi}$ in $\mathcal{O}$ for each $e$. For each $e \in S$ and each place $\sigma$, take the choice of congruences of the previous lemma for the source $\sigma$ and the partner $\mathrm{pr}_e\sigma$.

The congruences on the rows of one matrix $g_{\tau,h}$ come from all pairs $(e, \sigma)$ with $\tau = \sigma$ (as a source) or $\tau = \mathrm{pr}_e\sigma$ (as a partner). Each one is a linear form on the rows, because the forms depend only on the given directions $y$:

- the pairing at the source is the form $k' \mapsto \sum_a \sqrt[p^e]{y_{\mathrm{pr}_e\sigma,a,0}}\; y_{\tau,a,k'}$, modulo $\sqrt[p^e]{\pi}$;
- the pairing at the partner is the form $k' \mapsto \sum_a y_{\sigma,a,0}^{p^e}\; y_{\tau,a,k'}$, modulo $\pi$;
- an entry is the coordinate form at $k'$, modulo $\sqrt[p^e]{\pi}$ at the source and $\pi$ at the partner.

The value of a form with coefficients $\sum_a x_a y_{\tau,a,k'}$ on a row $g_k$ is $\sum_a x_a \beta_{\tau,h,k,a}$ (`New.dotProduct_sum_mul`), so a congruence on the rows is the congruence on the new directions that the choice asks for. Apply elimination for several forms to each $(\tau, h)$. This gives $g_{\tau,h}$ whose determinant divides the product of the moduli of all congruences imposed on its rows.

Property 1 is the case analysis above: a pair that is not exempt is covered, and each of the four ways of covering makes the pairing divisible by $\pi$.

For property 2, the norm of the product of the moduli, taken over all $(\tau, h)$ with the power $\kappa_\tau(h)$, is $\|\pi\|$ to the power $\sum_{e,\sigma}\mathrm{cost}$, since a modulus $\sqrt[p^e]{\pi}$ has norm $\|\pi\|^{1/p^e}$ (`New.norm_rpow_sum_cost_eq_prod_congruenceModulus`). The cost of each choice is the deduction term. A divisor has a norm at least that of the multiple, so $\|\det g_{\tau,h}\|$ is at least the norm of the product of its moduli. $\square$

**Remark (Formalization).** The matrices $g_{\tau,h}$ and the roots of $\pi$ are chosen objects, made with `choose`; the theorem asserts only their existence. The pairing at the source and at the partner always uses the first given direction $y_{\cdot,\cdot,0}$, which is the only direction of height one. The theorem is stated for every finite set $S$ of exponents and every family of maps $\mathrm{pr}_e$; the partners and the set $S$ of the count are fixed only in Section 4.

**Example.** Take one source $\sigma$, not marked, with $t_\sigma$ columns of height one and nothing else, and a partner $\sigma' \ne \sigma$ with nothing. Then $\mathrm{ded}_e(\sigma,\sigma') = \min(t_\sigma/p^e, 0) = 0$. Indeed, $\mathrm{A}$ fails, and the pairing at the partner is imposed, but the partner has no columns, so the congruence costs nothing. The pairings that matter are those of a new direction at $\sigma$ with directions at $\sigma'$, and there are none. In the other direction, with source $\sigma'$ and partner $\sigma$, the source has no columns and the term is $\min(0, t_\sigma) + 0 + \min(0, 0) = 0$. So such a diagram has deduction zero, and Section 4 shows that each of its boxes gains the full $\gamma_p$.
