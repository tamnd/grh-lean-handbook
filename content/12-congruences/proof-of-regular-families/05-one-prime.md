---
title: A twist for one prime
lean:
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.Selmer.exists_mFoldTwist_selmerLengthLe_inv_ratio_le
  - New.Selmer.exists_mFoldTwist_hasDenominatorsLe
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A twist for one prime

This section joins the steps at one prime $\ell$. The twisting theorem is applied once, to the finite list of main summands of Section 3. It gives one $m$-fold twist $\tau$ such that every power $\tau^j$ has an auxiliary modulus, short Selmer groups for all the main summands, and small inverse ratios. Section 4 then turns the short Selmer groups into the two clauses of `HasDenominatorsLe`.

Fix $\ell$ with `ThePrime ℓ` and $\iota$ = `ι : PadicIso ℓ`. As before, $e'_\ell$ = `twistError ℓ D` and $\beta_\ell$ = `clearingBound D ℓ`.

### The twisting theorem for two families

The twisting theorem of Section 2 takes one family $(R_i)_{i \in I}$ whose row types may depend on $i$. The proof has two families with two row types: $D.\mathrm{RowIndex}$ for the lifts and `Unit` for the main pairs. This lemma joins them.

**Lemma (The twisting theorem for two families).** Let $A$ and $B$ be finite types. Let $R_a$ for $a \in A$ be representations with the row type $D.\mathrm{RowIndex}$, and $R'_b$ for $b \in B$ representations with the row type `Unit`. Suppose that each of them is like a main summand (`IsMainSummandLike D t J`) for some $t$ and $J$. Then there is an $m$-fold twist $\tau$ such that for every $1 \leq j \leq m$ the power $\vartheta = \tau^j$ has four properties:

1. `IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar` $e'_\ell$;
2. for every $a \in A$ there are $\gamma$, $\zeta$ with `HasDivisibleSelmerLengthLe ϑ.invAvatar (R a) ϑ.Q γ ζ` $e'_\ell$;
3. the same for every $R'_b$, $b \in B$;
4. for every ramified critical pair $p$ and every sign $s \in \mathbb{Z}^\times$,
$$\|\iota_\ell(p.\mathrm{ratio}(\vartheta, s)^{-1})\| \leq \exp(e'_\ell \log \ell).$$

Lean: `New.Selmer.exists_mFoldTwist_selmerLengthLe_inv_ratio_le` (New/Congruences/FitTwistsExist.lean).

*Proof.* Let $I = A \oplus B$. For $i \in I$ let the row type be
$$r_i = \mathrm{SummandCoordIndex}\ D.\mathrm{RowIndex}\ (i.\mathrm{getRight?}.\mathrm{map}\ 0),$$
with $t = 1$. For $i = \mathrm{inl}\,a$, `getRight?` is `none`, and the type is $D.\mathrm{RowIndex}$. For $i = \mathrm{inr}\,b$ it is `some 0`, and the type is `Unit`. So the family $S$ with $S_{\mathrm{inl}\,a} = R_a$ and $S_{\mathrm{inr}\,b} = R'_b$ is well typed, and the index type $I$ is finite. The hypothesis on $S$ follows from the two hypotheses by `Sum.forall`.

The twisting theorem applied to $S$ gives $\tau$. For $1 \leq j \leq m$ it gives the three properties of $\vartheta = \tau^j$. Property 1 is the first of them. Properties 2 and 3 are the second, at $\mathrm{inl}\,a$ and at $\mathrm{inr}\,b$. For property 4, the third property of the twisting theorem says that $\mathrm{ellVal}(\iota_\ell(p.\mathrm{ratio}(\vartheta, s))) \leq e'_\ell$. The lemma from a valuation to a norm (Section 2), with $x = p.\mathrm{ratio}(\vartheta, s)$ and $c = e'_\ell$, gives the bound. $\square$

**Remark (Formalization).** The index type `SummandCoordIndex` is defined in `New/Congruences/LocalLoss/Basic.lean` (line 443) for the local loss, where it names the coordinates of the summands of a representation. Here it serves only to give a family with the two row types. The choice $t = 1$ makes `Option (Fin 1)` have the one value `some 0` besides `none`.

### The twist at one prime

**Theorem (A twist with few congruences at one prime).** There is an $m$-fold twist $\tau$ with three properties.

1. $\ell$ is prime to $\tau.\mathrm{normQ} = \prod_{w \in Q} q_w$.
2. For every $1 \leq j \leq m$, every ramified critical pair $p$ and every sign $s$,
$$\|\iota_\ell(p.\mathrm{ratio}(\tau^j, s)^{-1})\| \leq \exp(e'_\ell \log \ell).$$
3. For every $1 \leq j \leq m$, $D.\mathtt{HasDenominatorsLe}\ \iota_\ell\ \tau^j\ j\ \gamma_\ell$, with
$$\gamma_\ell = \beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell,$$
where $h_{\mathrm{std}}$ = `Nat.card (StdClasses (n := Unit) D.chosenLevel)`.

Lean: `New.Selmer.exists_mFoldTwist_hasDenominatorsLe` (New/Congruences/FitTwistsExist.lean).

So $\exp\gamma_\ell = \ell^{\beta_\ell} \cdot \ell^{v_\ell(h_{\mathrm{std}})}$. The second factor is the $\ell$-part of the number of classes.

*Proof.* The proof has six steps.

*Step 1. The eigensystems.* Let
$$\mathcal{S} = \{q : \mathrm{FinPlace}(E) \times \mathbb{N} \to \mathbb{C} \mid \mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q \neq 0\}.$$
The good forms on $W_m$ are a subspace of the forms of principal level. So $\mathcal{S}$ is finite by the lemma on finitely many eigensystems (Section 2).

*Step 2. The main summands.* Let $A = \{1, \dots, m\} \times \mathcal{S}$. For $a = (j, q) \in A$ the theorem on main summands of the lifts (Section 2) gives $R_a$ with the row type $D.\mathrm{RowIndex}$, a main summand for $D.\mathrm{descentPair}(1, j)$ and $(w, i) \mapsto q(w, i)$. Let $B$ be the subtype of pairs $(p, j)$ with $p$ a main pair for $j$. For $b \in B$ the lemma on the main summands of the main pairs (Section 3) gives $R'_b$ of rank one, a main summand for $O_p(1)$ and $1$. The types $A$ and $B$ are finite: $\mathcal{S}$ by Step 1, the lift indices since they lie in $\{1, \dots, m\}$, and the critical pairs by `New.Data.finite_criticalPair`. Both families come from `choose`.

The first field of `IsMainSummand` says that each $R_a$ and each $R'_b$ is like a main summand, with $t$ the rank difference of its pair and some jumps. This is the hypothesis of the lemma on two families.

*Step 3. The twist.* The lemma on two families gives $\tau$ and, for each $j$, the four properties of $\tau^j$. Name them $h_{\mathrm{aux}}(j)$, $h_{\mathrm{sel}}(j)$, $h'_{\mathrm{sel}}(j)$ and $h_{\mathrm{ratio}}(j)$. Property 2 of the theorem is $h_{\mathrm{ratio}}$.

*Step 4. Coprimality.* Take $j = 1$, which is a lift index since $1 \leq m$ (`nat_le_of_hasLogBound`). The first part of $h_{\mathrm{aux}}(1)$ says that $(\tau^1).Q$ is auxiliary for the bad places. The power of a tame character keeps the set $Q$ (`TameChar.pow`), so $(\tau^1).Q = \tau.Q$. By the lemma on the modulus and the bad places (Section 2), $\ell$ is prime to $\prod_{w \in \tau.Q} q_w = \tau.\mathrm{normQ}$. This is property 1.

*Step 5. The space of lifts.* Fix $j$. Apply the lemma on the denominator for the space of lifts (Section 4) to $\vartheta = \tau^j$, with $h_{\mathrm{aux}}(j)$. For $q$ with $\mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q \neq 0$, the hypothesis on $q$ is met by $R_{(j, q)}$, its main summand property, and $h_{\mathrm{sel}}(j)$ at $(j, q)$. So
$$\mathtt{DenominatorLe}\ \iota_\ell\ (D.\mathrm{descentPair}(\tau^j, j))\ e_0\ Z_{\tau^j, j}\ (\beta_\ell \log \ell).$$
Here the index $a = (j, q)$ uses the same $j$ as the power $\tau^j$. The main summand of $(j, q)$ is for the $j$-th descent pair, and the lemma needs exactly that.

The lemma on clearing from a denominator bound (Section 4), with $\beta = \beta_\ell \log \ell \leq \beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell = \gamma_\ell$, gives clause 1 of `HasDenominatorsLe`. The inequality holds since $v_\ell(h_{\mathrm{std}}) \geq 0$ and $\log \ell \geq 0$ (`positivity`).

*Step 6. The main pairs.* First, the stabilizers are trivial. The lemma on trivial stabilizers (Section 2), with $K$ = `D.chosenLevel` and the index type `Unit`, needs $\#\mathrm{Unit} = 1 \leq 2 n_m$. This holds by `Fintype.card_unit` and `nat_le_of_hasLogBound`. So $\mathrm{classAut}(g) = \bot$ for every $g$.

Now fix $j$, a main pair $p$ for $j$ and test forms $\Xi$, $\Xi'$. Apply the lemma on the denominator for the line of a main pair (Section 4) with $\vartheta = \tau^j$, $h_{\mathrm{aux}}(j)$, $R = R'_{(p, j)}$, its main summand property and $h'_{\mathrm{sel}}(j)$ at $(p, j)$. It gives
$$\mathtt{DenominatorLe}\ \iota_\ell\ O_p(\tau^j)\ e_{X-1}\ (\mathbb{C}\varphi)\ (\beta_\ell \log \ell).$$
The projection bound (Section 2), with the trivial stabilizers, gives
$$\|\iota_\ell\langle \mathrm{pr}\,\Xi, \mathrm{pr}\,\Xi' \rangle\| \leq \exp\big(\beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell\big) = \exp \gamma_\ell .$$
The chosen level of the lift data is `D.chosenLevel`, so the number of classes is $h_{\mathrm{std}}$. This is clause 2 of `HasDenominatorsLe`. $\square$

### What the proof of the theorem shows

The two clauses of `HasDenominatorsLe` have different sources of loss.

1. Clause 1 loses only $\beta_\ell \log \ell$ per dimension and unit of rank. The term $v_\ell(h_{\mathrm{std}}) \log \ell$ is slack. It is there because the definition has one number for both clauses.
2. Clause 2 loses $\beta_\ell \log \ell$ from the bound for denominators, and $v_\ell(h_{\mathrm{std}}) \log \ell$ from the projection bound. The second loss comes from the volume of the classes of $U(1)$. It is not an error of Ribet's method.

The twist $\tau$ depends on $\ell$ and $\iota$. The main summands are $\ell$-adic and depend on $\ell$ and $\iota$, and the twisting theorem uses $\ell$. The constants $e'_\ell$, $\beta_\ell$ and $\gamma_\ell$ depend only on $\ell$ and $D$.

**Remark (Formalization).** The source uses `choose` three times in this proof: for $R$, for $R'$ and for the four properties of $\tau^j$. No choice matters, since the statement only asks for the existence of $\tau$. The eigensystems in $\mathcal{S}$ are functions to $\mathbb{C}$, and $\mathcal{S}$ is a set coerced to a type. Its finiteness is a local instance (`have : Finite systems`), which the twisting theorem finds by instance search.
