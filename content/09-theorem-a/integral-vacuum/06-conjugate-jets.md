---
title: Conjugate jets
lean:
  - New/Derivatives/Vacuum/IntegralVacuum.lean
  - Lib/Weil/Construction/ThetaJets.lean
  - New/Derivatives/Field/PrimeDecomposition.lean
  - New/Reduction/Data/FieldsAndPlaces.lean
decls:
  - New.Space.IsJetConjugate
  - New.Parameters.placePerm
  - New.Parameters.bigOmega
  - New.Parameters.bigOmega_pos
  - New.Parameters.finitePart_le_span_translates
  - New.Parameters.map_zetaLinearSeries
  - New.Parameters.exists_rational_translate_eq
  - New.Parameters.IsThetaProduct.isJetConjugate_of_map_taylorAtZero_eq
  - New.Parameters.exists_isJetConjugate_translates
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Conjugate jets

The jets of a theta function are the coefficients of its Taylor series at $0$. For the vacuum they are algebraic up to a power of the scale, and the automorphisms of $\mathbb{C}$ over $K$ permute them in a controlled way. The tool is again the theta product of Section 5, since its jets are products of jets of one theta function of one variable, and the theorem of complex multiplication tells how $\sigma$ acts on those. This section proves the statement used in [theta kernels and gauges](/chapter/theta-kernels-gauges/): one vector $F$ spans the finite part by its translates, and $\sigma$ takes the jets of each translate of $F$ to the jets of a translate of a second vector $F'$, at a scale of modulus $\Omega_E^{-1/2}$, with the places permuted.

### The definition

**Definition (Conjugate jets).** Let $\sigma$ be a ring endomorphism of $\mathbb{C}$, $\pi$ a permutation of the places of $E$, $t, t' \in \mathbb{C}$ and $f, f' \in \mathcal{S}(V)$. The jets of $f'$ at scale $t'$ are *$\sigma$-conjugate* to those of $f$ at scale $t$, with the permutation $\pi$, if applying $\sigma$ to the coefficients of $J_t f$ gives $J_{t'}f'$ with each variable $X_{\tau,k}$ renamed $X_{\pi^{-1}\tau,k}$.

Lean: `New.Space.IsJetConjugate` (Lib/Weil/Construction/ThetaJets.lean).

The constant term of $J_t f$ is the theta functional of the projection of $f$ to the real vacuum, so the definition also relates these two numbers.

**Definition (Permutation of the places).** For $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$, let $\pi_\sigma$ be multiplication, in the group of places identified with $\mathrm{Gal}(E/K)$, by the place of the embedding $\sigma\circ\tau_1$, where $\tau_1$ is the embedding at the trivial place.

Lean: `New.Parameters.placePerm` (New/Derivatives/Field/PrimeDecomposition.lean).

So $\sigma\circ\tau = \pi_\sigma(\tau)$ as embeddings of $E$, for every place $\tau$. This is in [the field E at the primes](/chapter/field-at-primes/).

**Definition (The period constant).** $\Omega_E = e^{C_d}\cdot 2\pi/\mathrm{rd}(E)$. It is positive.

Lean: `New.Parameters.bigOmega` (New/Reduction/Data/FieldsAndPlaces.lean); `New.Parameters.bigOmega_pos` (New/Derivatives/Vacuum/IntegralVacuum.lean).

### Three lemmas

**Lemma.** Let $c \ne 0$ and $c\,\mathrm{vac} = \sum_{j \in \Gamma}\varrho^\pm(a_j)\varrho(\mathrm{fin}(b))F$. Then $V^{\mathrm{fin}}$ is contained in the complex span of the translates $\varrho(\mathrm{fin}(x))F$, $x$ a finite adelic vector.

Lean: `New.Parameters.finitePart_le_span_translates` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* The finite part is spanned by the vectors $\varrho^\pm(z)\,\mathrm{vac}$. Apply $\varrho^\pm(z)$ to the identity and divide by $c$. The product of two finite Heisenberg operators is a scalar times the translation by the sum, so each term is a scalar times a translate of $F$. $\square$

**Lemma (Linear forms).** For $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ and a unit $\Omega$, applying $\sigma$ to the coefficients of $\lambda_{k,j}(\mathrm{jetScale})$, built with the period $\Omega_0$, gives $\lambda_{k,j}(t)$ built with the period $\Omega$, with $t = \sigma(\mathrm{periodFactor})\,\mathrm{areaScale}/\Omega$, and the variables renamed by $\pi_\sigma$.

Lean: `New.Parameters.map_zetaLinearSeries` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* The constant factor of the left form is
$$\frac{\Omega_0}{q_1\,\mathrm{areaScale}}\cdot \mathrm{jetScale} = \frac{\mathrm{periodFactor}}{q_1},$$
and that of the right form is $\sigma(\mathrm{periodFactor})/q_1$. The coefficients are $\overline{\tau(\zeta^k)}$, and $\sigma$ maps them to $\overline{\pi_\sigma(\tau)(\zeta^k)}$, since $\sigma$ commutes with complex conjugation on the CM field $\tau(E)$. $\square$

The second lemma explains the choice of $\mathrm{jetScale}$: it makes the coefficient $\mathrm{periodFactor}/q_1$ free of the period.

**Lemma (Rational translates).** Let $F \in V^{\mathrm{fin}}$, $\beta$ a finite adele of $K$, and for each $x \in K$ let $U_x$ be a neighbourhood of $\beta x$. For $\gamma \in E^n$ there is $a \in K$ such that the translates of $F$ by $\beta\cdot\alpha^{-1}\gamma$ and by $\alpha^{-1}(a\gamma)$ agree, and $a\cdot\mathrm{zc}_k(\gamma_i) \in U_{\mathrm{zc}_k(\gamma_i)}$ for all $k$ and $i$.

Lean: `New.Parameters.exists_rational_translate_eq` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* The translate $\varrho(\mathrm{fin}(\beta'\alpha^{-1}\gamma))F$ is locally constant in $\beta'$, since $F$ lies in the finite part. The finitely many conditions $\beta'\mathrm{zc}_k(\gamma_i) \in U$ hold near $\beta' = \beta$. Both hold on a neighbourhood of $\beta$, and $K$ is dense in its finite adeles. $\square$

### Conjugates of the factors

**Proposition.** Let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$. Let $F$ be a theta product for the CM curve with period $\Omega_0$ and level $e$, and $F'$ a theta product for the conjugate curve $C^\sigma$ with period $\Omega$ and level $e'$. Let $\gamma, \gamma' \in E^n$. Assume that for all $k$ and $j$, $\sigma$ maps the Taylor series of $\vartheta_{k,\gamma_j}$ (for $C$ and $\Omega_0$) to the Taylor series of $\vartheta_{k,\gamma'_j}$ (for $C^\sigma$ and $\Omega$). Then the jets of $\varrho(\mathrm{fin}(\alpha^{-1}\gamma'))F'$ at scale $t = \sigma(\mathrm{periodFactor})\,\mathrm{areaScale}/\Omega$ are $\sigma$-conjugate, with $\pi_\sigma$, to the jets of $\varrho(\mathrm{fin}(\alpha^{-1}\gamma))F$ at scale $\mathrm{jetScale}$.

Lean: `New.Parameters.IsThetaProduct.isJetConjugate_of_map_taylorAtZero_eq` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* By item 3 of a theta product, both jet series are products over $(k, j)$ of a Taylor series in one variable composed with $\lambda_{k,j}$, to the power $q_1$. Applying $\sigma$ to the coefficients is a ring map, and it commutes with substitution. So $\sigma$ maps each factor of the left side to the Taylor series of $\vartheta_{k,\gamma'_j}$ composed with the conjugate linear form. By the lemma on linear forms, that form is $\lambda_{k,j}(t)$ with the variables renamed by $\pi_\sigma$. Renaming the variables is also a ring map, and so the products agree. $\square$

### The theorem

**Theorem (Conjugate jets of translates).** There is a map $B$ from $\mathrm{Gal}(\mathbb{C}/K)$ to the finite adeles of $E$ with the following property. For every standard space $V$ there is $F \in V^{\mathrm{fin}}$ such that:

1. $\theta(F) = 1$;
2. $V^{\mathrm{fin}}$ is contained in the span of the translates $\varrho(\mathrm{fin}(x))F$;
3. for every $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ there are $t \in \mathbb{C}$ with $|t|^2 = \Omega_E^{-1}$ and $F' \in V^{\mathrm{fin}}$ such that, for every finite adelic vector $x$, the jets of $\varrho(\mathrm{fin}(B_\sigma x))F'$ at scale $t$ are $\sigma$-conjugate, with $\pi_\sigma$, to the jets of $\varrho(\mathrm{fin}(x))F$ at scale $\mathrm{jetScale}$.

Lean: `New.Parameters.exists_isJetConjugate_translates` (New/Derivatives/Vacuum/IntegralVacuum.lean).

*Proof.* For each $\sigma$, the theorem of complex multiplication for theta functions ([CM elliptic curves](/chapter/cm-elliptic-curves/)) gives a unit $\Omega_\sigma$ and a finite adele $\beta_\sigma$ of $K$ with these properties: the area of $C^\sigma$ is $|\Omega_\sigma|^2\sqrt d/2$; some multiple $\Omega_\sigma e_\sigma$ with $e_\sigma \ge 1$ lies in the lattice of $C^\sigma$; and for every $x \in K$ there is a neighbourhood $U_x$ of $\beta_\sigma x$ such that, for every $x' \in K \cap U_x$, $\sigma$ maps the Taylor series of $T^1_{x\Omega_0}\theta_C$ to the Taylor series of $T^1_{x'\Omega_\sigma}\theta_{C^\sigma}$. Let $B_\sigma$ be the image of $\beta_\sigma$ in the finite adeles of $E$.

Let $F$ be the theta product of level one for the CM curve (Section 5). Item 1 is $\theta(F) = 1$. Item 2 is the first lemma, with the multiple of the vacuum of Section 5.

Fix $\sigma$. Let $F'$ be a theta product for $C^\sigma$, $\Omega_\sigma$ and $e_\sigma$, which exists by Section 5. Put $t = \sigma(\mathrm{periodFactor})\,\mathrm{areaScale}/\Omega_\sigma$. By the proposition of Section 3 on the size at the infinite places, $|t|^2 = \Omega_E^{-1}$.

Both translates are locally constant in $x$, since $F$ and $F'$ lie in the finite part, and the vectors $\alpha^{-1}\gamma$ with $\gamma \in E^n$ are dense. So the set of $x$ where item 3 fails is open, and it is enough to prove item 3 for $x = \alpha^{-1}\gamma$. By the lemma on rational translates, there is $x_0 \in K$ such that $\varrho(\mathrm{fin}(B_\sigma\alpha^{-1}\gamma))F' = \varrho(\mathrm{fin}(\alpha^{-1}x_0\gamma))F'$ and $x_0\,\mathrm{zc}_k(\gamma_i) \in U_{\mathrm{zc}_k(\gamma_i)}$ for all $k$, $i$. Then $\sigma$ maps the Taylor series of
$$\vartheta_{k,\gamma_i} = T^1_{\mathrm{zc}_k(\gamma_i)\Omega_0}\theta_C \quad\text{to that of}\quad T^1_{x_0\mathrm{zc}_k(\gamma_i)\Omega_\sigma}\theta_{C^\sigma} = T^1_{\mathrm{zc}_k(x_0\gamma_i)\Omega_\sigma}\theta_{C^\sigma},$$
which is the factor $\vartheta_{k,x_0\gamma_i}$ of $F'$. The proposition, with $\gamma' = x_0\gamma$, gives item 3. $\square$

**Example.** Take $\sigma = 1$. Then $\pi_\sigma$ is the identity, and $C^\sigma = C$. If the theorem of complex multiplication gives $\Omega_1 = \Omega_0$ and $\beta_1 = 1$, then $t = \mathrm{jetScale}$ and $B_1 = 1$, and one may take $F' = F$. Then item 3 is the identity $J_{\mathrm{jetScale}} = J_{\mathrm{jetScale}}$, and $|t|^2 = \Omega_E^{-1}$ is the case $\sigma = 1$ of Section 3. The content of the theorem is in the automorphisms $\sigma \ne 1$, which move the period and the torsion points.

**Remark (Formalization).** The theorem is stated with one map $B$ for all standard spaces of all ranks, and with one vector $F$ that works for all $\sigma$ at once. The vector $F'$ and the scale $t$ depend on $\sigma$, and $F'$ is chosen through the theorem of complex multiplication. The statement does not say that $\theta(F') = 1$, although the $F'$ of the proof is a theta product and so has this property. The theorem uses only automorphisms of $\mathbb{C}$ over $K$. The map $B$ is a chosen object.
