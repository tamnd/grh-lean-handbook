---
title: The proof of the theorem
lean:
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.exists_isRegularFamily
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The proof of the theorem

This section proves the theorem of Section 1. The work is done in Sections 5 and 6. Section 5 gives a twist at each pair $\kappa = (\ell, \iota)$, with bounds that depend only on $\ell$. Section 6 sums the bounds over the primes. The proof joins the two.

**Theorem (Twists with few congruences).** For all data $D$ there is a family $\theta$ of $m$-fold twists, indexed by the pairs $\kappa = (\ell, \iota)$ of a prime $\ell$ and a ring isomorphism $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$, such that $\theta$ is a regular family (`D.IsRegularFamily θ`).

Lean: `New.exists_isRegularFamily` (New/Congruences/FitTwistsExist.lean).

*Proof.* A pair $\kappa$ is a structure `PrimePadicIso` with two fields: $\kappa.1$, a prime in `Nat.Primes`, and $\kappa.2$, the isomorphism. Write $\ell = \kappa.1$ and $\iota = \kappa.2$.

*Step 1. A twist at each pair.* Fix $\kappa$. The prime $\ell$ gives the instance `ThePrime ℓ`, from the fact that $\ell$ is prime. The isomorphism gives the instance `⟨κ.2⟩ : PadicIso ℓ`, with $\iota_\ell = \iota$. The theorem on a twist at one prime (Section 5) gives an $m$-fold twist $\tau$ with three properties:

1. $\gcd(\ell, \tau.\mathrm{normQ}) = 1$;
2. $\|\iota(p.\mathrm{ratio}(\tau^j, s)^{-1})\| \leq \exp(e'_\ell \log \ell)$ for all $1 \leq j \leq m$, ramified critical pairs $p$ and signs $s$;
3. $D.\mathtt{HasDenominatorsLe}\ \iota\ \tau^j\ j\ \gamma_\ell$ for all $1 \leq j \leq m$, with $\gamma_\ell = \beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell$.

The tactic `choose` turns this into a function $\theta : \mathrm{PrimePadicIso} \to D.\mathrm{MFoldTwist}$ and the three properties at each $\kappa$. Name them $h_{\mathrm{coprime}}$, $h_{\mathrm{ratio}}$ and $h_{\mathrm{den}}$.

*Step 2. The sum of the twist errors.* For every finite set $T$ of primes,
$$\sum_{\ell \in T} e'_\ell \log \ell \leq x^{999} \leq x_1.$$
The first step is the lemma on the twist error (Section 6). The second is `le_of_hasLogBound`. In terms of the scales, it holds since $x^{10^6} \leq x_1$.

*Step 3. Small ratios.* The two fields of `HasSmallRatios` are these.

1. `coprime`: this is $h_{\mathrm{coprime}}$.
2. `height_le`: fix $1 \leq j \leq m$, a ramified critical pair $p$ and a sign $s$. The family is $\kappa \mapsto p.\mathrm{ratio}(\theta(\kappa)^j, s)^{-1}$. Apply the lemma on heights from local bounds (Section 2) with $e_\ell = e'_\ell \log \ell$ and $c = x_1$. Its first hypothesis is Step 2. Its second is $h_{\mathrm{ratio}}(\kappa)$ at $j$, $p$, $s$. So the family has height at most $x_1$.

*Step 4. Denominator bounds.* Fix $1 \leq j \leq m$. Take $\gamma = (\ell \mapsto \gamma_\ell)$. The two fields of `IsDenominatorBound` are these.

1. `sum_le`: for every finite set $T$ of primes, $\sum_{\ell \in T} \gamma_\ell \leq \mathrm{denominatorBudget}$. This is the theorem on the sum of the denominator bounds (Section 6).
2. `hasDenominatorsLe`: for every $\kappa$, the twist $\theta(\kappa)^j$ has denominators at most $\gamma_\ell$ for $j$ at $\iota$. This is $h_{\mathrm{den}}(\kappa)$ at $j$.

So $\gamma$ is a denominator bound for $\theta$ at $j$, and $\theta$ is a regular family. $\square$

### All the constants

The proof gives these numbers. They are the same at every $j$, and they depend only on $D$ and $\ell$.

| Quantity | Bound at $\ell$ | Sum over the primes |
|---|---|---|
| inverse ratios | $\exp(e'_\ell \log \ell)$, $e'_\ell = (4f + 3) r\, v_\ell(N_g) + 2^{-\ell}$ | $\leq (4f + 3) r \log N_g + 2 \leq x^{999} \leq x_1$ |
| clearing (clause 1) | $\exp(-\dim Z \cdot r \cdot \gamma_\ell) \leq \lVert\iota \det\Lambda\rVert$ | |
| line of a main pair (clause 2) | $\exp \gamma_\ell$ | |
| $\gamma_\ell$ | $\beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell$ | $\leq 4 \cdot 10^6 e^{180} f \frac{m}{k} b \log b + (1 + 2t) x^{999} + x^{4000} + \log N_g + x^{30}$ |
| | | $\leq \mathrm{denominatorBudget} = f a \log^3 b/(mk)$ |

The clearing bound is $\beta_\ell = 4f\,\mathrm{defectBound}(\ell) + (1 + 2t) e'_\ell + e_\ell + v_\ell(N_g)$, with the terms of Section 6.

### What the proof does not give

The theorem gives the existence of $\theta$. It gives no more than the fields of `IsRegularFamily`.

1. The twist $\theta(\kappa)$ may depend on $\iota$, not only on $\ell$. The proof of Theorem C does not need more.
2. There is no bound on the size of the modulus $Q$ of $\theta(\kappa)$. The statement asks only that $\ell$ is prime to $\mathrm{Nm}\,Q$.
3. The family $\theta$ is not one twist for all primes. Each $\kappa$ has its own twist. This is why the heights are of families indexed by $\kappa$.

**Remark (Formalization).** The instance `ThePrime κ.1` is made with `have : ThePrime κ.1 := ⟨⟩`. The anonymous constructor finds the field `Fact (κ.1 : ℕ).Prime` from the instance for `Nat.Primes`. The instance `PadicIso` is passed explicitly as `⟨κ.2⟩`, so the $\iota_\ell$ of Section 5 is $\kappa.2$ by definition. Then $\|\iota_\ell(\cdot)\|$ in Section 5 and $\|\kappa.2(\cdot)\|$ here are the same term.

**Remark (Formalization).** The real number $x_1$ = `D.x₁` and the sum in Step 2 are compared by `le_of_hasLogBound`, with $x^{999}$ on the left. This is the only place where the scale $x_1$ enters the chapter. The budget uses $a$ and $\log b$, not $x_1$.
