---
title: Main summands from eigensystems
lean:
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
  - New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean
decls:
  - New.Selmer.HasLiftTrace
  - New.Selmer.IsMainSummand
  - New.Selmer.isMainSummandWeights_descentPair
  - New.Selmer.isMainSummandWeights_mainPair
  - New.Selmer.map_jumps_sub_eq_map_targetParameter
  - New.Selmer.IsRepOfType.isMainSummandLike_twistByChar
  - New.Selmer.eventually_trace_frob_eq_of_hasLiftHeckePolynomial
  - New.Selmer.exists_isMainSummand_of_isRepOfType
  - New.Data.isEigenform_of_hasHeckePolyAt
  - New.Selmer.exists_isMainSummand_descentPair
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Main summands from eigensystems

This section proves the main theorem of the chapter. A lift $y$ of a Hecke eigensystem $b$ to a descent pair $V$ is an eigenform whose Hecke polynomials are those of the theta lift of $b$ ([single theta lifts](/chapter/single-theta-lifts/)).

### Main summands

**Definition (Lift trace).** Let $\psi$ be a character, $R$ of rank $\#m$, $t \in \mathbb{N}$, and $u$ of rank $\#n$. Then $u$ has the *lift trace* of $(\psi, R, t)$ if $\mathrm{tr}\,u(g) = \psi(g)\,\mathrm{tr}\,R(g) + \sum_{e < t} \varepsilon^{-1}(g)^e$ for all $g$.

Lean: `New.Selmer.HasLiftTrace` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Definition (Main summand).** Let $O$ be a descent pair and $b$ a Hecke eigensystem. A representation $T$ of rank $\#r$ is a *main summand for $O$ and $b$* if:

1. $T$ is like a main summand with twist $1 - O.\mathrm{rankDiff}$ and some jumps;
2. for every tame character $\vartheta$, every descent pair $V$ with $V.\chi_{U(1)} = O.\chi_{U(1)}\vartheta$, every lift $y$ of $b$ to $V$ that is an eigenform with Hecke polynomials $H$, and every $S$ attached to $H$, the normalized representation $\chi_V \otimes S$ has the lift trace of $(\vartheta^{-1}, T, V.\mathrm{rankDiff})$.

Lean: `New.Selmer.IsMainSummand` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Remark (Formalization).** Clause 2 quantifies over all lifts, so it is empty when no lift exists. The jumps in clause 1 are given by an existential.

### The weights

**Theorem (Weights of the descent pairs).** Let $1 \leq j \leq m$. At $\sigma$ over $v$, take the $D.r$ jumps $D.t/2 - \epsilon_\sigma(\lambda_q + w_j)$, $q < D.r$. They are main summand weights for $(D.r, D.t)$.

Lean: `New.Selmer.isMainSummandWeights_descentPair` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* The rank bound and $t \leq D.t$ hold. For $q + 1 < D.k$ the jump is high: $|\epsilon_\sigma u + w_j| \leq D.t$. For $D.k \leq q + 1 \leq D.r$ the jump is low: $D.\mathrm{gap}/4 \leq |u| \leq 2m\,D.\mathrm{gap}$. Both follow from the size bounds on the target parameters. If $2m\,D.\mathrm{gap} \leq B$ and $B + D.t < w_j$, then exactly the $m$ low jumps have $|u| \leq B$, by the lemma that high jumps are large. This gives the count of small jumps, since $D.k \leq D.r$. Since $\epsilon_{\bar\sigma} = -\epsilon_\sigma$, the jumps at $\sigma$ and $\bar\sigma$ for one $q$ add up to $2\lfloor D.t/2 \rfloor \geq 0$. So at most one of them is negative. $\square$

**Theorem (Weights of the main pairs).** Let $p$ be a main pair for $j$ with $p.z$ and negative weight $c$. The single jumps $p.z - 1 - \epsilon_\sigma c_v$ are main summand weights for $(1, 2p.z - 1)$.

Lean: `New.Selmer.isMainSummandWeights_mainPair` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* Here $D.m < z \leq D.r$, so $2z - 1 \leq D.t = 5D.r$. The bound $w_j + D.r - D.t \leq c \leq w_j$ puts $\epsilon_\sigma u + w_j$ within $D.t$ of $0$. There is one jump at each embedding, so the counts are at most $1$. $\square$

**Lemma.** Let $(d, \kappa)$ be a weight whose doubled Harish-Chandra parameter is twice the target parameter. Then its jumps at $\sigma$, lowered by $(D.r - D.t)/2 + \epsilon_\sigma w$, are the numbers $D.t/2 - \epsilon_\sigma(\lambda_q + w)$, $q < D.r$.

Lean: `New.Selmer.map_jumps_sub_eq_map_targetParameter` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* The $q$-th jump is the $q$-th Harish-Chandra parameter plus a constant. Write $2\lambda_q = 2(\kappa_v + \sum_{q < h < D.r} d_v(h)) + D.r - 1 - 2q$ and compare both sides, with $D.t = 5D.r$ and $D.r$ odd. $\square$

### The trace identity

**Lemma (The twist is like a main summand).** Let $(O, c)$ be a lift setting for the trivial twist, $R$ of type $(O, c)$ with twist $1 - \#r$, jumps $J$ and empty level, and $\#r - O.\mathrm{rankDiff} = 2a$. If the jumps $J$ lowered by $a - \epsilon_\sigma O.\mathrm{weight}_v$ are main summand weights, then $\theta \otimes R$ is like a main summand with these jumps, where $\theta$ is the avatar of $x \mapsto \mu^{-1}(x/\bar x)|x|^a$ for the character $\mu$ of $O$.

Lean: `New.Selmer.IsRepOfType.isMainSummandLike_twistByChar` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* The theorem on the twist by an avatar of [lift settings and representations of a type](/chapter/main-summands/#lift-settings-and-representations-of-a-type) makes $\theta \otimes R$ of type $(O, c')$ with twist $1 - O.\mathrm{rankDiff}$ and the lowered jumps. Since $\mu$ has tame part $O.\mathrm{tamePart}$, the labels $c'$ are the scaled type polynomials. Apply the theorem that representations of a type are like main summands. $\square$

**Lemma (Traces at Frobenius).** In the setting of the lemma before, let $V$ have character $\mu\vartheta$, and let $y$ be a lift of $b$ to $V$ with Hecke polynomials $H$. For most Frobenius elements $g$ at $w$, minus the coefficient of $X^{\#n - 1}$ in $H_w$, times $\chi_V(g)$, is $\theta_0(g)\theta(g)b(w, 1) + \sum_{e < \#n - \#r} \varepsilon^{-1}(g)^e$, where $\theta_0$ is the avatar of $\vartheta^{-1}(x/\bar x)$.

Lean: `New.Selmer.eventually_trace_frob_eq_of_hasLiftHeckePolynomial` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* The Hecke polynomial of a lift at a split place $w$ is the Hecke polynomial of $b$ with roots scaled by the character, times the product of the $X - q^{e}$ for the string ([split places](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials)). The coefficient of $X^{\#n - 1}$ is minus the sum of the roots. Each avatar is $\iota$ of its Hecke character at a Frobenius, and $\chi_V(g)$ cancels the weight of the character of $V$. $\square$

**Theorem (Main summands from a representation of a type).** Let $(O, c)$ be a lift setting for the trivial twist and $R$ of type $(O, c)$ with twist $1 - \#r$, jumps $J$ and empty level. Suppose that $\mathrm{tr}\,R(g)$ is the limit of $\iota(b(w, 1))$ along most Frobenius elements tending to $g$, and that $J$ lowered by $(\#r - O.\mathrm{rankDiff})/2 - \epsilon_\sigma O.\mathrm{weight}_v$ are main summand weights. Then some $T$ is a main summand for $O$ and $b$.

Lean: `New.Selmer.exists_isMainSummand_of_isRepOfType` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* Both $\#r$ and $O.\mathrm{rankDiff}$ are odd, so $\#r - O.\mathrm{rankDiff} = 2a$. Let $T = \theta \otimes R$. Clause 1 is the lemma on the twist. For clause 2, let $S$ be attached to $H$ and fix $g$. Along most Frobenius elements tending to $g$, three limits hold: $-\chi_V\,\iota(H_w)_{\#n - 1} \to -\chi_V(g)\,\mathrm{charpoly}(S g)_{\#n - 1}$, by the definition of attached and continuity of $\chi_V$; $\theta_0\theta\,\iota(b(w, 1)) \to \theta_0(g)\theta(g)\,\mathrm{tr}\,R(g)$; and the string tends to its value at $g$. The lemma on traces at Frobenius says the two sides agree eventually, so the limits agree. Since $\#r < \#n$, minus the coefficient of $X^{\#n - 1}$ of the characteristic polynomial is the trace. With $\theta_0$ the inverse avatar of $\vartheta$, this is the lift trace. $\square$

### The main theorem

**Lemma.** A nonzero function with Hecke polynomial $Q_w$ at every split place off the chosen places and their conjugates is an eigenform for $Q$.

Lean: `New.Data.isEigenform_of_hasHeckePolyAt` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* An eigenform needs the Hecke polynomial at almost every place of prime norm. A place of prime norm is split, and only finitely many places are chosen or conjugate to a chosen place. $\square$

**Theorem (Main summands of the lifts).** Let $p$ occur in a nonzero good form on $W_m$: the good forms and the $p$-eigenpart meet in a nonzero space. Let $1 \leq j \leq m$, and let $O$ be the $j$-th descent pair of the trivial twist. Then some $T$ of rank $D.r$ is a main summand for $O$ and $(w, i) \mapsto p(w, i)$.

Lean: `New.Selmer.exists_isMainSummand_descentPair` (New/Congruences/GaloisRepresentations/RowsFromEigensystems.lean).

*Proof.* Take $z \neq 0$ good with eigensystem $p$. Take a weight $(d, \kappa)$ whose Harish-Chandra parameter is the doubled target parameter, and let $L$ send a form to its algebraic form of this weight. *A label.* The idempotent $e_0$ fixes $z$ and is the sum of the tuple idempotents over the good tuple families. So some good $c$ has $e_c z \neq 0$. By the theorem on lift settings of the lifts, $(O, c)$ is a lift setting. *An eigenform.* $L$ commutes with the Hecke operators, and they act on $z$ by the scalars $p$. By the lemma before, $Lz$ is an eigenform with the Hecke polynomials of $p$. *A representation.* The spherical compatibility for the standard space gives $R$ attached to $Lz$ ([building the representations](/chapter/building-representations/)). *Its type.* At a chosen place, $\mathrm{GL}_r$ of the integers acts on $Lz$ through the principal action, a parahoric type with one block. Since $e_c z \neq 0$, the label idempotent of $c_i$ does not kill this action, so $Lz$ has the product label of $c_i$. The theorem on representations of a type from labels makes $R$ of type $(O, c)$ with twist $1 - D.r$, the jumps of $(d, \kappa)$ and empty level. *The trace.* The trace of $R(g)$ and $p(w, 1)$ are minus the coefficients of $X^{D.r - 1}$, so the attached limit gives the trace hypothesis. *The weights.* $O.\mathrm{weight} = -w_j$ and $O.\mathrm{rankDiff} = D.t$. By the lemma on jumps, the lowered jumps are those of the theorem on weights of the descent pairs. Apply the theorem on main summands from a representation of a type. $\square$
