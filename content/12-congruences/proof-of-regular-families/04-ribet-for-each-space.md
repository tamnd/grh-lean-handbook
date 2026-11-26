---
title: Ribet's method for each space
lean:
  - New/Congruences/FitTwistsExist.lean
decls:
  - New.Selmer.DenominatorLe.clearsProjection
  - New.Selmer.denominatorLe_range_goodLift
  - New.Selmer.denominatorLe_span_trivialLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Ribet's method for each space

The bound for denominators of Section 2 applies to a space $Z$ that is spanned by its lift generators. This section applies it to two spaces. The first is the space of lifts $Z_{\vartheta, j}$, with the idempotent $e_0$ of the good forms. The second is the line of the lifted form `trivialLift` of a main pair, with the idempotent of the labels $X - 1$. In both cases the hypotheses are the same: an auxiliary twist and short Selmer groups of the main summands of Section 3. The section also proves that a denominator bound in the form `DenominatorLe` gives the first clause of `HasDenominatorsLe`.

Fix $\ell$ with `ThePrime ℓ` and $\iota$ = `ι : PadicIso ℓ`. Write $\iota_\ell$ = `ι.ιℓ`, $e'_\ell$ = `twistError ℓ D` and $\beta_\ell$ = `clearingBound D ℓ`.

### The hypothesis on the twist

Both lemmas assume `IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar (twistError ℓ D)`. This is the first of the three properties that the twisting theorem gives for each power of the twist (Section 2). It has three parts (`New/Congruences/FirstOrder/EvenClasses.lean`, line 130).

1. The set $\vartheta.Q$ is auxiliary for the bad places $\ell \cdot (M N)$ (`IsAuxiliary`). Its places have prime norm, they and their conjugates are off the bad places, and their conjugates are off $Q$.
2. The inverse avatar of $\vartheta$ comes from the norm-one torus with modulus $Q$, and no place of $Q$ lies above $\ell$ (`IsFromU1`).
3. For some family of tame generators $\sigma_P$ at the places $P$ of $Q$, the sum of the $\ell$-adic valuations of $\psi(\sigma_P) - 1$ is at most $e'_\ell$, where $\psi$ is the inverse avatar.

Section 5 uses part 1 for the coprimality of $\ell$ and $\mathrm{Nm}\,Q$.

### The space of lifts

**Lemma (Denominator for the space of lifts).** Let $\vartheta$ be a twist with `IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar` $e'_\ell$, and let $1 \leq j \leq m$. Suppose that for every system $q$ with $\mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q \neq 0$ there are a representation $R$ with the row type $D.\mathrm{RowIndex}$ and $\gamma$, $\zeta$ such that:

1. $R$ is a main summand for $D.\mathrm{descentPair}(1, j)$ and $(w, i) \mapsto q(w, i)$;
2. `HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ ζ` $e'_\ell$.

Then `DenominatorLe` $\iota_\ell$ $(D.\mathrm{descentPair}(\vartheta, j))$ $e_0$ $Z_{\vartheta, j}$ $(\beta_\ell \log \ell)$.

Lean: `New.Selmer.denominatorLe_range_goodLift` (New/Congruences/FitTwistsExist.lean).

In words: some operator $\Lambda$ on $Z_{\vartheta, j}$ with $\|\iota_\ell \det\Lambda\| \geq \ell^{-\dim Z \cdot r \cdot \beta_\ell}$ clears the denominators of the projection to $Z_{\vartheta, j}$ on integral forms that are orthogonal to the false lifts for $e_0$.

*Proof.* Let $O = D.\mathrm{descentPair}(\vartheta, j)$ and $V = D.\mathrm{descentPair}(1, j)$. First, the characters of $U(1)$ of the two pairs have
$$O.\mathrm{u1Char} = V.\mathrm{u1Char} \cdot \vartheta.\mathrm{toAutChar}.$$
The character of the $j$-th descent pair of $\vartheta$ is the lift character of $j$ times $\vartheta.\mathrm{toAutChar}$. For the trivial twist, $\mathrm{toAutChar}$ is the trivial character, by the lemma on the trivial twist (Section 2). So the identity is a computation with `simp`.

Apply the bound for denominators (Section 2) with $O$, the idempotent $E = e_0$ and the space $Z = Z_{\vartheta,j}$. It needs that $Z$ lies in the span of its lift generators for $\vartheta$, $e_0$ and $e'_\ell$. By the splitting theorem (Section 3), $Z$ lies in the span of its split forms. So by the monotony of the span it is enough to show that each split form is a lift generator.

Let $y$ be split. So $y \in Z$, and there is a tuple $c$ as in property 1 of a split form, and there is a system $q$ with $\mathcal{G}(W_m) \cap \mathcal{A}(W_m)_q \neq 0$ such that $y$ has the Hecke polynomials of the lift of $(w, i) \mapsto q(w, i)$. The hypothesis on $q$ gives $R$, $\gamma$ and $\zeta$. Now the fields of a lift generator are these.

1. `mem`: $y \in Z$.
2. `exists_type`: the tuple $c$, with the three facts of property 1.
3. `exists_hasLiftHeckePolynomial`: the values $(w, i) \mapsto q(w, i)$, the Hecke polynomials of $y$, the representation $R$ and the pair $V$, the main summand property of $R$, the identity of the characters and the Selmer bound.

So $y$ is a lift generator, and the bound for denominators gives the claim. $\square$

The pair $V$ of the main summand is the untwisted pair, not $O$. This is why the main summands of Section 3 do not depend on the twist. The twist enters only through the character identity and through the twisted Selmer group.

### The line of a main pair

Let $p = (\nu, z)$ be a main pair for $j$, and let $Y_\vartheta$ = `p.lValueData hp.hasLiftRank ϑ` be the data of the theta lift of $\nu\vartheta$ from $U(1)$ to $U(2z)$. Write $O_p(\vartheta)$ for its descent pair and $\varphi_\vartheta$ = `Y_ϑ.trivialLift` for the lifted form. Let $e_{X-1}$ be the idempotent `tupleIdem Unit` of the labels $X - 1$ at all chosen places of $O_p(\vartheta)$.

**Lemma (Denominator for the line of a main pair).** Let $\vartheta$ be a twist with `IsAuxTwist (badPlaces D ℓ) ϑ.Q ϑ.invAvatar` $e'_\ell$, and let $p$ be a main pair for $j$. Let $R$ be a representation of rank one that is a main summand for $O_p(1)$ and the system $1$, and suppose that `HasDivisibleSelmerLengthLe ϑ.invAvatar R ϑ.Q γ ζ` $e'_\ell$ for some $\gamma$, $\zeta$. Then
$$\mathtt{DenominatorLe}\ \iota_\ell\ O_p(\vartheta)\ e_{X-1}\ (\mathbb{C}\varphi_\vartheta)\ (\beta_\ell \log \ell).$$

Lean: `New.Selmer.denominatorLe_span_trivialLift` (New/Congruences/FitTwistsExist.lean).

The line has dimension at most one and the row type `Unit` has one element. So the determinant bound reads $\|\iota_\ell \det \Lambda\| \geq \ell^{-\beta_\ell}$ if $\varphi_\vartheta \neq 0$.

*Proof.* As in the first lemma, the characters have
$$O_p(\vartheta).\mathrm{u1Char} = O_p(1).\mathrm{u1Char} \cdot \vartheta.\mathrm{toAutChar}.$$
The character of $O_p(\vartheta)$ is $\nu\vartheta$ written as an automorphic character, and $\vartheta = 1$ gives $\nu$. This is again `simp` with the lemma on the trivial twist.

Apply the bound for denominators with $O_p(\vartheta)$, $E = e_{X-1}$ and $Z = \mathbb{C}\varphi_\vartheta$. The span of the singleton $\{\varphi_\vartheta\}$ is $Z$. So by the monotony of the span it is enough to show that $\varphi_\vartheta$ is a lift generator. The fields are these.

1. `mem`: $\varphi_\vartheta \in \mathbb{C}\varphi_\vartheta$.
2. `exists_type`: the labels $c = (X - 1)_i$. The form $\varphi_\vartheta$ is in the range of the type projection of $c$, and $c$ is a lift setting for $O_p(\vartheta)$ and $\vartheta$, by the theorem on the lift settings of the main pairs (Section 2). The range of the type projection of $c$ is the range of $e_{X-1}$ itself, so the inclusion is equality.
3. `exists_hasLiftHeckePolynomial`: the system $1$. The form $\varphi_\vartheta$ has the Hecke polynomials of a lift of $1$, by the theorem on the Hecke polynomials of the lift of a character (Section 2). Then $R$, the pair $O_p(1)$, the main summand property, the identity of the characters and the Selmer bound.

So the bound for denominators gives the claim. $\square$

**Remark (Formalization).** The statement starts with `open scoped Classical in`. The idempotent `tupleIdem` needs decidable equality on the index type of the chosen places, and the statement takes it from classical logic. The theorem on the lift settings of the main pairs uses the instance of its own statement. The two instances are equal only as propositions. So the source closes the goal on the membership of $\varphi_\vartheta$ with `convert` at [line 464](lean:New/Congruences/FitTwistsExist.lean#L464), and the comment at line 463 says why. This is F-025 of the spec, and it is confirmed.

### From `DenominatorLe` to the first clause

**Lemma (Clearing from a denominator bound).** Let $\vartheta$ be a twist and $j \in \mathbb{N}$. Suppose that
$$\mathtt{DenominatorLe}\ \iota\ (D.\mathrm{descentPair}(\vartheta, j))\ e_0\ Z_{\vartheta, j}\ \beta$$
and $\beta \leq \beta'$. Then the projection to $Z_{\vartheta, j}$ is cleared at $\beta'$ (`D.ClearsProjection ι ϑ j β'`).

Lean: `New.Selmer.DenominatorLe.clearsProjection` (New/Congruences/FitTwistsExist.lean).

*Proof.* Take the operator $\Lambda$ of the hypothesis. The second clause of `ClearsProjection` is the first half of the second clause of `DenominatorLe`, the integrality of $\Lambda(\mathrm{pr}\,y)$. The bound on inner products is dropped. For the determinant, the size of the row type is $\#D.\mathrm{RowIndex} = r$ (`D.card_rowIndex`). Let $d = \dim Z_{\vartheta, j} \geq 0$. Since $\beta \leq \beta'$ and $d r \geq 0$,
$$\exp(-d \cdot r \cdot \beta') \leq \exp(-d \cdot r \cdot \beta) \leq \|\iota \det \Lambda\|.$$
The first step is `gcongr` and the second is the hypothesis. $\square$

The proof of Section 5 uses this lemma with $\beta = \beta_\ell \log \ell$ and $\beta' = \beta_\ell \log \ell + v_\ell(h_{\mathrm{std}}) \log \ell$. The extra term is not needed for the first clause. It comes from the second clause, where the projection bound adds it. The source makes the two clauses use the same number, since `HasDenominatorsLe` has one $\beta$.

**Remark (Formalization).** `ClearsProjection` uses $D.r$ as a real number and `DenominatorLe` uses the cardinality of the row type. The lemma `D.card_rowIndex` joins them. If the space of lifts is $0$, then $d = 0$ and both bounds are $1 \leq \|\iota \det \Lambda\|$, with $\det \Lambda = 1$ on the zero space.
