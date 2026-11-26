---
title: What the chapter proves
lean:
  - New/Congruences/FitTwistsExist.lean
  - New/Determinant/Twist/FitTwists.lean
  - New/OneLift/TestedForms.lean
  - New/Reduction/Lattices/Heights.lean
decls:
  - New.Data.IsRegularFamily
  - New.Data.HasSmallRatios
  - New.Data.IsDenominatorBound
  - New.Data.HasDenominatorsLe
  - New.Data.ClearsProjection
  - New.Selmer.DenominatorLe
  - New.Data.IsNegligible
  - New.Data.denominatorBudget
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is the last chapter of the volume. It assembles the existence of regular families from the results of chapters 2 to 11. It states the theorem as Lean states it, and it gives the whole proof. Each input is stated exactly as the source proves it, with a link to the section that proves it. The chapter tracks every constant. Section 8 maps the proof to the declarations of the source, and Section 9 compares the plan of the volume with the source.

[Regular families: the plan](/chapter/regular-families-plan/) gives the motivation, a model case and the chain of the proof. This chapter does not repeat the motivation or the model case. It gives in full the steps that the plan states, in the order of the source, and it shows how each input enters. All of these steps are in one file, [New/Congruences/FitTwistsExist.lean](lean:New/Congruences/FitTwistsExist.lean#L1), with 535 lines. The source claims the theorem. Lean accepts it, if the reported checks hold. This chapter does not claim that the proof is correct.

### The notation

Fix parameters $P$ and admissible data $D$ for $P$. The letters are those of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes).

1. $x$, $x_1$ and $b$ are the three scales, with $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$. The number $\log b$ is `D.logB`.
2. $m$ is the number of lifts, $r$ is a rank, $k = r + 1 - m$ and $t = 5r$.
3. $f$ is the number of infinite places of the CM field $E$, and $a = x b$.
4. $\mathrm{err}_0 = D.\mathtt{errorUnit} = f a \log^3 b$.
5. $\kappa = (\ell, \iota)$ runs over the pairs of a prime $\ell$ and a ring isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$ (`New.PrimePadicIso`).
6. $N_g$ = `D.chosenGroupOrder` is the order of the product of the groups $\mathrm{GL}_{rt}$ over the residue fields at the chosen places above $p_0$ and $p_1$.
7. $h_{\mathrm{std}}$ is the number of classes `StdClasses` of $U(1)$ at the level `D.chosenLevel`.
8. $v_\ell$ is the $\ell$-adic valuation of a natural number (`padicValNat`). It is $0$ at $0$.
9. $\vartheta$ is a twist, and for an $m$-fold twist $\tau$ and $1 \leq j \leq m$, $\tau^j$ is the twist `τ.powTwist j`. It has the same modulus $Q$ as $\tau$.
10. $W_j$ is the space of rank $r$ of the $j$-th lift, and $Z_{\vartheta, j}$ is the space of lifts, the range of `D.goodLift ϑ j`.

### The definitions in the statement

The statement uses six definitions of `New/Determinant/Twist/FitTwists.lean` and one of `New/OneLift/TestedForms.lean`. [Regular families of twists](/chapter/twists-critical-pairs/#regular-families-of-twists) in Volume 11 and [denominators and regular families](/chapter/regular-families-plan/#denominators-and-regular-families) give them with the motivation. They are recalled here, since the proof follows their fields.

**Definition (Denominator of a projection).** Let $O$ be a descent pair with row type $r$, $e_0$ an element of the group algebra of the chosen group, $Z$ a subspace of the forms on $O$ and $\beta \in \mathbb{R}$. The projection to $Z$ has *denominator at most $\exp\beta$ per dimension and row at $\iota$* if there is an operator $\Lambda$ on $Z$ such that:

1. $\exp(-\dim Z \cdot \#r \cdot \beta) \leq \|\iota(\det \Lambda)\|$;
2. for every form $y$ that is integral at $\iota$ and orthogonal to the false lifts for $e_0$ and $Z^\perp$, the form $\Lambda(\mathrm{pr}_Z\, y)$ is integral at $\iota$, and $\|\iota\langle y', \Lambda(\mathrm{pr}_Z\, y)\rangle\| \leq 1$ for every form $y'$ that is integral at every place above $\ell$.

Lean: `New.Selmer.DenominatorLe` (New/OneLift/TestedForms.lean).

**Definition (Clearing the projection).** For a twist $\vartheta$, an index $j$ and $\beta \in \mathbb{R}$, the projection to $Z_{\vartheta, j}$ is *cleared at $\beta$* if some operator $\Lambda$ on $Z_{\vartheta, j}$ has $\exp(-\dim Z_{\vartheta,j} \cdot r \cdot \beta) \leq \|\iota(\det\Lambda)\|$, and $\Lambda(\mathrm{pr}\, y)$ is integral at $\iota$ for every form $y$ that is integral at $\iota$ and orthogonal to the false lifts for $e_0$.

Lean: `New.Data.ClearsProjection` (New/Determinant/Twist/FitTwists.lean).

The two definitions differ in two points. `ClearsProjection` has the rank $r = D.r$ where `DenominatorLe` has the size $\#r$ of the row type. It also drops the bound on inner products. Section 4 proves that the first gives the second.

**Definition (Small denominators).** A twist $\vartheta$ has *denominators at most $\beta$ for $j$ at $\iota$* if:

1. the projection to $Z_{\vartheta, j}$ is cleared at $\beta$;
2. for every main pair $p = (\nu, z)$ for $j$ and all test forms $\Xi$, $\Xi'$ on the descent pair of the lift of $\nu\vartheta$ from $U(1)$ to $U(2z)$, the inner product of the projections of $\Xi$ and $\Xi'$ to the line of the lifted form `trivialLift` has norm at most $\exp\beta$ at $\iota$.

Lean: `New.Data.HasDenominatorsLe` (New/Determinant/Twist/FitTwists.lean).

**Definition (The budget).** The budget is $\mathrm{denominatorBudget} = \mathrm{err}_0/(m k) = f a \log^3 b/(m k)$.

Lean: `New.Data.denominatorBudget` (New/Determinant/Twist/FitTwists.lean).

**Definition (Denominator bound).** For a family $\theta$ of $m$-fold twists and $1 \leq j \leq m$, a function $\gamma : \mathbb{N} \to \mathbb{R}$ is a *denominator bound for $\theta$ at $j$* if:

1. $\sum_{\ell \in T} \gamma_\ell \leq \mathrm{denominatorBudget}$ for every finite set $T$ of primes;
2. for every $\kappa = (\ell, \iota)$, the twist $\theta(\kappa)^j$ has denominators at most $\gamma_\ell$ for $j$ at $\iota$.

Lean: `New.Data.IsDenominatorBound` (New/Determinant/Twist/FitTwists.lean).

**Definition (Negligible numbers).** For $C \in \mathbb{N}$, numbers $e_\ell$ are *negligible with the exponent $C$* if $e_\ell \geq 0$ for every $\ell$, and $\sum_{\ell \in T} e_\ell \log \ell \leq x^C$ for every finite set $T$ of primes.

Lean: `New.Data.IsNegligible` (New/Determinant/Twist/FitTwists.lean).

**Definition (Small ratios).** A family $\theta$ of $m$-fold twists *has small ratios* if:

1. for every $\kappa = (\ell, \iota)$, $\ell$ is prime to the norm $\mathrm{Nm}\,Q$ of the modulus of $\theta(\kappa)$ (`normQ`);
2. for every $1 \leq j \leq m$, every ramified critical pair $p$ and every sign $s \in \{\pm 1\}$, the family $\kappa \mapsto p.\mathrm{ratio}(\theta(\kappa)^j, s)^{-1}$ has height at most $x_1$.

Lean: `New.Data.HasSmallRatios` (New/Determinant/Twist/FitTwists.lean).

The height of a family is that of [heights over the isomorphisms with the l-adic numbers](/chapter/twisted-lattices/#heights-over-the-isomorphisms-with-the-l-adic-numbers) (`New.HeightLe`).

**Definition (Regular families).** A family $\theta$ of $m$-fold twists is *regular* if it has small ratios and, for every $1 \leq j \leq m$, some $\gamma$ is a denominator bound for $\theta$ at $j$.

Lean: `New.Data.IsRegularFamily` (New/Determinant/Twist/FitTwists.lean).

### The statement

**Theorem (Twists with few congruences).** For all data $D$ there is a regular family $\theta$ of $m$-fold twists, one twist $\theta(\kappa)$ for each pair $\kappa = (\ell, \iota)$.

Lean: `New.exists_isRegularFamily` (New/Congruences/FitTwistsExist.lean).

Section 7 proves the theorem. The proof gives explicit constants. For $\kappa = (\ell, \iota)$ the inverse ratios have $\|\iota(p.\mathrm{ratio}(\theta(\kappa)^j, s)^{-1})\| \leq \exp(e'_\ell \log \ell)$, with the twist error
$$e'_\ell = (4f + 3)\, r\, v_\ell(N_g) + 2^{-\ell}.$$
The denominator bound is the same at every $j$:
$$\gamma_\ell = \beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell, \qquad \beta_\ell = \mathrm{clearingBound}(\ell).$$
Section 6 gives $\beta_\ell$ and the sums of these numbers over the primes.

**Remark (Formalization).** The family $\theta$ comes from the tactic `choose`. The source proves for each $\kappa$ that a twist exists, and it does not construct one. So $\theta(\kappa)$ is not a definite twist, and no property of $\theta$ holds beyond the fields of `IsRegularFamily`. In particular, the source does not say that $\theta(\kappa)$ depends only on $\ell$, although the bounds depend only on $\ell$.

**Remark (Formalization).** The numbers $\gamma_\ell$ are not $0$ for primes that divide nothing of the data. The twist error has the term $2^{-\ell} > 0$, and so $\beta_\ell \geq (1 + 2t) 2^{-\ell} > 0$. The local loss and $v_\ell(N_g)$ are $0$ for most primes.

### Where the theorem is used

The theorem is the only result of Volume 12 that the proof of Theorem C needs. [The four inputs](/chapter/theorem-c-plan/#the-four-inputs) of Volume 11 states it as input 4. In the source it has one use, at [line 144](lean:New/Determinant/Twist/LongForms.lean#L144) of `New/Determinant/Twist/LongForms.lean`, in `exists_hasSmallRatios_heightLe_liftDeterminant_div` ([the proof of Theorem C](/chapter/proof-of-theorem-c/)). Two results of Volume 11 take a regular family as a hypothesis, and each reads one clause of `HasDenominatorsLe`. The height of the lift determinant, `New.Data.heightLe_liftDeterminant_ratio` (New/OneLift/LiftVolumeHeight.lean), reads clause 1 at [line 753](lean:New/OneLift/LiftVolumeHeight.lean#L753). The height of the inverse ratios of main pairs, `New.Data.heightLe_inv_ratio` (New/OneLift/HeckeValues/TwistedValueHeights.lean), reads clause 2 at [line 915](lean:New/OneLift/HeckeValues/TwistedValueHeights.lean#L915).

### The plan of the chapter

1. Section 2 states the inputs from other chapters, each exactly as proved.
2. Section 3 finds the main summands: one for each eigensystem of the good forms on $W_m$ and each $j$, and one of rank one for each main pair.
3. Section 4 applies Ribet's method, in the form of the bound for denominators, to the space of lifts and to the line of a main pair.
4. Section 5 joins the steps at one prime $\ell$. The twisting theorem gives one twist for all the main summands.
5. Section 6 proves the sums over the primes. Every constant appears there.
6. Section 7 proves the theorem.
7. Section 8 maps the proof, Section 9 checks the plan, and Section 10 has exercises and notes.
