---
title: Conjugation of jets
lean:
  - New/UpperBound/Kernels/JetConjugatesAndBounds.lean
decls:
  - New.Parameters.IsJetConjugation
  - New.Space.map_selfDualAddChar_of_isJetConjugate
  - New.Parameters.exists_isJetConjugation
  - New.Parameters.norm_multiplierRatio
  - New.Parameters.IsJetConjugation.eq_zero_of_map_eq_zero
  - New.Parameters.IsJetConjugation.map_apply_finVec
  - New.Parameters.IsJetConjugation.exists_map_schrodingerOp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Conjugation of jets

A jet of a theta function is a complex number. For the argument we need a bound for $|\sigma(\text{jet})|$ for every automorphism $\sigma$ of $\mathbb{C}$, and $\sigma$ is not continuous. So no analytic bound for the jet itself says anything about $\sigma(\text{jet})$. The way out is to show that $\sigma(\text{jet})$ is again a jet, of another datum, at another scale. Then analysis applies to the new datum. This section builds, for each $\sigma$ over $K$, one $\sigma$-semilinear operator $L$ that does this for all data of the finite part at once.

### The model case

Take rank one and the vacuum. The theta function of $\mathrm{vac}$ along the archimedean variable is a theta function of an elliptic curve with complex multiplication by $\mathcal{O}_K$, and its Taylor coefficients at $0$, after the scale $t_0$ is put in, are algebraic. The main theorem of complex multiplication says that $\sigma$ maps the curve with its torsion points to a curve isogenous to it, and so maps the scaled Taylor coefficients of the theta function of one translate to the scaled Taylor coefficients of the theta function of another translate. This is the content of the theorem on conjugate jets of translates of [the integral vacuum and tight frames](/chapter/integral-vacuum/). This section changes nothing in the analysis. It only packs that theorem into a linear operator, and it reads off the consequences for characters, for values and for the vacuum.

### The definition

Recall the notion of conjugate jets of [the integral vacuum and tight frames](/chapter/integral-vacuum/) in one line: for a ring map $\sigma$ of $\mathbb{C}$, a permutation $\pi$ of the infinite places, scales $t, t'$ and data $f, f'$, the relation $\mathrm{IsJetConjugate}(\sigma, \pi, t, t', f, f')$ says
$$\sigma\bigl(J_t f\bigr) = \mathrm{rename}_{\pi^{-1}}\bigl(J_{t'} f'\bigr),$$
where $\sigma$ acts on the coefficients and $\mathrm{rename}_{\pi^{-1}}$ sends the variable $X_{\tau, i}$ to $X_{\pi^{-1}\tau, i}$. Here $J_t f$ has the coefficient $t^{|a|}\,\partial^a(\theta f)(0)/a!$ at the monomial $X^a$.

**Definition (Jet conjugation).** Let $V$ be a hermitian space over $E$ of rank $n$, let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$, let $t \in \mathbb{C}$ and $b \in \mathbb{A}_{E,f}$, and let $L : \mathcal{S}(V) \to \mathcal{S}(V)$ be $\sigma$-semilinear. Then $L$ is a *jet conjugation* for $(\sigma, t, b)$ if:

1. $|t|^2 = \Omega_E^{-1}$;
2. $L$ scales translations by $b$: $\sigma(\psi(z)) = \psi(b \bar b z)$ for all $z \in \mathbb{A}_{E,f}$, where $\psi$ is the self-dual additive character; $L$ maps $V^{\mathrm{fin}}$ into $V^{\mathrm{fin}}$; and $L\,\varrho(\mathrm{fin}(x)) f = \varrho(\mathrm{fin}(b x))\,L f$ for $f \in V^{\mathrm{fin}}$ and all finite adelic vectors $x$;
3. for all $f \in V^{\mathrm{fin}}$, $\mathrm{IsJetConjugate}(\sigma, \pi_\sigma, t_0, t, f, Lf)$, where $\pi_\sigma$ is the permutation of the infinite places of $E$ induced by $\sigma$.

Lean: `New.Parameters.IsJetConjugation` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

Condition 2 is the notion of [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) for a semilinear map that scales translations, [`New.Space.ScalesTranslations`](/decl/New.Space.ScalesTranslations/). Condition 3 says that $\sigma$ of the jets of $f$ at the fixed scale $t_0$ are the jets of $Lf$ at the new scale $t$, with the places permuted. Only the modulus of $t$ is fixed, and only $V^{\mathrm{fin}}$ is constrained.

### The character law

The law for $\psi$ in condition 2 is not part of the input from complex multiplication. It follows from the law for translations, by the Heisenberg relation, in rank one. Recall the relation for finite translations:
$$\varrho(\mathrm{fin}(x))\,\varrho(\mathrm{fin}(y))\,f = \psi\bigl(\tfrac12\,\bar y \cdot x\bigr)\,\varrho(\mathrm{fin}(x + y))\,f,$$
where $\bar y \cdot x = \sum_i \bar y_i x_i$ and $\tfrac12$ is the inverse of $2$ in $\mathbb{A}_{E,f}$.

**Lemma (The character law from conjugate jets).** Let $E$ be a CM field with Weil data and let $V_1$ be the standard space of rank one. Let $\sigma$ be a ring map $\mathbb{C} \to \mathbb{C}$, let $e$ be a permutation of the infinite places of $E$, let $t, t' \in \mathbb{C}$ and $b \in \mathbb{A}_{E,f}$. Let $F, F'$ lie in $V_1^{\mathrm{fin}}$, with $F \ne 0$ and $t \ne 0$. Suppose that for every finite adele $x$,
$$\mathrm{IsJetConjugate}\bigl(\sigma, e, t, t', \varrho(\mathrm{fin}(x)) F, \varrho(\mathrm{fin}(b x)) F'\bigr).$$
Then $\sigma(\psi(z)) = \psi(b \bar b z)$ for all $z \in \mathbb{A}_{E,f}$.

Lean: `New.Space.map_selfDualAddChar_of_isJetConjugate` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Idea.* Translate first by a vector that fixes both data, then by $x$. The two orders give the same datum up to a value of $\psi$, and the hypothesis turns the value at $z$ into the value at $b \bar b z$.

*Proof.* Data of the finite part are locally constant under finite translations. So there is an open neighbourhood of $0$ on which $x \mapsto (\varrho(\mathrm{fin}(x))F, \varrho(\mathrm{fin}(x))F')$ is constant. The set $\{1, b\}$ is compact, so there is an integer $N \ne 0$ with $\varrho(\mathrm{fin}(N))F = F$ and $\varrho(\mathrm{fin}(N b))F' = F'$. The integer $N$ is a unit of $\mathbb{A}_{E,f}$, so $z = N x$ for some finite adele $x$.

Apply the hypothesis at $2x$ and replace $F$ by $\varrho(\mathrm{fin}(N))F$ and $F'$ by $\varrho(\mathrm{fin}(Nb))F'$. By the Heisenberg relation,
$$\varrho(\mathrm{fin}(2x))\,\varrho(\mathrm{fin}(N))\,F = \psi\bigl(\tfrac12 \cdot N \cdot 2x\bigr)\,\varrho(\mathrm{fin}(2x + N))\,F = \psi(N x)\,G,$$
with $G = \varrho(\mathrm{fin}(2x+N))F$, since $N$ is real. In the same way,
$$\varrho(\mathrm{fin}(2bx))\,\varrho(\mathrm{fin}(Nb))\,F' = \psi\bigl(\tfrac12\, \overline{N b} \cdot 2 b x\bigr)\,G' = \psi(b \bar b N x)\,G',$$
with $G' = \varrho(\mathrm{fin}(b(2x + N)))F'$. The hypothesis at $2x$ gives
$$\sigma(\psi(Nx))\,\sigma(J_t G) = \psi(b \bar b N x)\,\mathrm{rename}_{e^{-1}}(J_{t'} G').$$
The hypothesis at $2x + N$ gives $\sigma(J_t G) = \mathrm{rename}_{e^{-1}}(J_{t'} G')$. Subtract: $(\sigma(\psi(Nx)) - \psi(b\bar b N x))\,\sigma(J_t G) = 0$. It remains to see $J_t G \ne 0$. The datum $G$ lies in $V_1^{\mathrm{fin}}$, and a datum of the finite part with $J_t G = 0$ for some $t \ne 0$ is $0$ (one line from [the integral vacuum and tight frames](/chapter/integral-vacuum/): the series determines the theta function on each complex line through $0$, and the values on these lines determine the datum). The operator $\varrho$ is an isometry and $F \ne 0$, so $G \ne 0$. The power series $\sigma(J_t G)$ is then nonzero too, and $\sigma(\psi(z)) = \psi(b \bar b z)$. $\square$

The proof uses only one pair $F, F'$ in rank one. The existence theorem below takes this pair from the rank one case of the theorem on conjugate jets, and uses the lemma for spaces of every rank.

### Existence

**Theorem (Existence of jet conjugations).** Let $V$ be a standard space over $E$: its signs at the infinite places are all $+1$ and its point is the identity matrix. Let $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$. Then there are $t \in \mathbb{C}$, $b \in \mathbb{A}_{E,f}$ and a $\sigma$-semilinear map $L$ on $\mathcal{S}(V)$ such that $L$ is a jet conjugation for $(\sigma, t, b)$.

Lean: `New.Parameters.exists_isJetConjugation` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

The input is the theorem on conjugate jets of translates of [the integral vacuum and tight frames](/chapter/integral-vacuum/), [`New.Parameters.exists_isJetConjugate_translates`](/decl/New.Parameters.exists_isJetConjugate_translates/). In one line: there is a map $B$ from $\mathrm{Gal}(\mathbb{C}/K)$ to the finite adeles such that for every standard $V$ there is $F \in V^{\mathrm{fin}}$ with $\theta(F) = 1$, whose finite translates span a space that contains $V^{\mathrm{fin}}$, and for every $\sigma$ there are $t$ with $|t|^2 = \Omega_E^{-1}$ and $F' \in V^{\mathrm{fin}}$ with $\mathrm{IsJetConjugate}(\sigma, \pi_\sigma, t_0, t, \varrho(\mathrm{fin}(x))F, \varrho(\mathrm{fin}(B_\sigma x))F')$ for all $x$. The point of the uniform $B$ is that the same $b = B_\sigma$ serves in every rank, in particular in rank one.

*Proof.* Take $B$, $F$, $t$ and $F'$ as above, and put $b = B_\sigma$.

*Step 1: the map.* Let $R : V^{\mathrm{fin}} \to \mathbb{C}[[X]]$ be the $\mathbb{C}$-linear map $R(f) = \mathrm{rename}_{\pi_\sigma^{-1}}(J_t f)$. Let $C : \mathcal{S}(V) \to \mathbb{C}[[X]]$ be the $\sigma$-semilinear map $C(f) = \sigma(J_{t_0} f)$. We have $t \ne 0$, since $|t|^2 = \Omega_E^{-1} > 0$. So $R$ is injective: $R(f) = 0$ gives $J_t f = 0$, as renaming is a bijection, and then $f = 0$ as in the proof of the lemma. Choose a linear left inverse $R^\dagger$ of $R$ and put $L = R^\dagger \circ C$, followed by the inclusion of $V^{\mathrm{fin}}$ in $\mathcal{S}(V)$. This $L$ is $\sigma$-semilinear and takes values in $V^{\mathrm{fin}}$.

*Step 2: translates of $F$.* For every $x$ the hypothesis says $C(\varrho(\mathrm{fin}(x))F) = R(\varrho(\mathrm{fin}(bx))F')$, and $\varrho(\mathrm{fin}(bx))F'$ lies in $V^{\mathrm{fin}}$. Since $R^\dagger R$ is the identity,
$$L\,\varrho(\mathrm{fin}(x))\,F = \varrho(\mathrm{fin}(bx))\,F'. \tag{2.1}$$

*Step 3: the character.* Apply the theorem on conjugate jets to the standard space of rank one. It gives $F_1$ with $\theta(F_1) = 1$, so $F_1 \ne 0$, and for our $\sigma$ a datum $F_1'$ and a scale $t_1$ with the hypothesis of the lemma, with the same $b = B_\sigma$ and scale $t_0 \ne 0$. The lemma gives $\sigma(\psi(z)) = \psi(b \bar b z)$.

*Step 4: translations.* Let $f \in V^{\mathrm{fin}}$. We prove $L\,\varrho(\mathrm{fin}(x))f = \varrho(\mathrm{fin}(bx))\,Lf$ for all $x$. The set of $f$ with this property is closed under sums and under multiplication by scalars, since both sides are $\sigma$-semilinear in $f$, and it contains $0$. So by span induction it is enough to take $f = \varrho(\mathrm{fin}(w))F$. Then by (2.1), the Heisenberg relation and Step 3,
$$L\,\varrho(\mathrm{fin}(x))\varrho(\mathrm{fin}(w))F = \sigma\bigl(\psi(\tfrac12 \bar w \cdot x)\bigr)\,\varrho(\mathrm{fin}(b(x+w)))F' = \psi\bigl(\tfrac12\, b\bar b\, \bar w \cdot x\bigr)\,\varrho(\mathrm{fin}(b(x+w)))F',$$
and
$$\varrho(\mathrm{fin}(bx))\,L\,\varrho(\mathrm{fin}(w))F = \varrho(\mathrm{fin}(bx))\varrho(\mathrm{fin}(bw))F' = \psi\bigl(\tfrac12\, \overline{bw} \cdot bx\bigr)\,\varrho(\mathrm{fin}(b(x+w)))F'.$$
The two characters agree, since $\overline{bw}\cdot bx = b \bar b\,\bar w \cdot x$ in the commutative ring $\mathbb{A}_{E,f}$.

*Step 5: jets.* The relation $\mathrm{IsJetConjugate}(\sigma, \pi_\sigma, t_0, t, f, Lf)$ holds for $f = \varrho(\mathrm{fin}(w))F$ by (2.1) and the hypothesis. Both sides of it are additive in $f$, and $\sigma$-semilinear: $\sigma(J_{t_0}(cf)) = \sigma(c)\,\sigma(J_{t_0}f)$ and $J_t(L(cf)) = \sigma(c) J_t(Lf)$. It holds for $f = 0$. So by span induction it holds on $V^{\mathrm{fin}}$. Steps 3 to 5 give the three conditions. $\square$

**Remark (Formalization).** The map $L$ is built with a chosen left inverse $R^\dagger$ of an injective linear map. On $V^{\mathrm{fin}}$ the composite $R^\dagger C$ has the values forced by the jets, but off $V^{\mathrm{fin}}$ its values depend on the choice and have no meaning. The definition constrains $L$ only on $V^{\mathrm{fin}}$, and every later statement applies $L$ only to vectors of $V^{\mathrm{fin}}$. The theorem gives existence only, and later chapters obtain $L$ inside their proofs. No statement of the argument depends on the choice of $L$, $t$ or $b$. The theorem needs $V$ standard, because the theorem on conjugate jets is proved only for standard spaces. Data on other spaces are moved to the standard space by $\omega$ before $L$ is applied.

### The multiplier ratio

The law of $L$ for the Weil operators, from [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/), is [`New.Space.ScalesTranslations.map_omega`](/decl/New.Space.ScalesTranslations.map_omega/). In one line: for a finite unitary matrix $g$ and $f \in V^{\mathrm{fin}}$,
$$L\,\omega(1, g) f = \mu_\sigma(g)\,\omega(1, g)\,Lf,$$
with $\mu_\sigma(g) = \sigma(\Delta(g))/\Delta(g)$ the [multiplier ratio](/decl/New.multiplierRatio/) of the finite part $\Delta$ of the multiplier. For the bounds only its modulus matters.

**Lemma (The multiplier ratio has modulus one).** For $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$ and a finite unitary matrix $g$, $|\mu_\sigma(g)| = 1$.

Lean: `New.Parameters.norm_multiplierRatio` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* It is enough to show $|\mu_\sigma(g)^2| = 1$. By [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/), $\mu_\sigma(g)^2 = \upsilon(\det g)/\sigma(\upsilon(\det g))$, where $\upsilon$ is the splitting character of the Weil data on the norm one ideles, and $\det g$ is read as a norm one idele with archimedean part $1$. The character $\upsilon$ has a weight, in the sense of [class field theory](/chapter/class-field-theory/). For such a character and a norm one idele $u$ with archimedean part $1$, $|\tau(\upsilon(u))| = 1$ for every ring map $\tau : \mathbb{C} \to \mathbb{C}$. Apply this with $\tau = 1$ and $\tau = \sigma$. The quotient of two numbers of modulus $1$ has modulus $1$. $\square$

### Three consequences

**Lemma (Injectivity).** Let $L$ be a jet conjugation for $(\sigma, t, b)$ on a standard space $V$. If $f \in V^{\mathrm{fin}}$ and $Lf = 0$, then $f = 0$.

Lean: `New.Parameters.IsJetConjugation.eq_zero_of_map_eq_zero` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* By condition 3, $\sigma(J_{t_0} f) = \mathrm{rename}(J_t\,0) = 0$, so each coefficient of $J_{t_0}f$ has $\sigma$-image $0$. A ring automorphism is injective, so $J_{t_0} f = 0$. The scale $t_0$ is not $0$, so $f = 0$. $\square$

**Lemma (Conjugate values).** Let $L$ be a jet conjugation for $(\sigma, t, b)$ on a space $V$, and let $f \in V^{\mathrm{fin}}$. Then for all finite adelic vectors $x$,
$$\sigma\bigl(f(\mathrm{fin}(x))\bigr) = (Lf)(\mathrm{fin}(b x)).$$

Lean: `New.Parameters.IsJetConjugation.map_apply_finVec` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* The datum $\varrho(\mathrm{fin}(x))f$ lies in $V^{\mathrm{fin}}$, and $L$ maps it to $\varrho(\mathrm{fin}(bx))Lf$ by condition 2. So condition 3 gives
$$\sigma\bigl(J_{t_0}\varrho(\mathrm{fin}(x))f\bigr) = \mathrm{rename}\bigl(J_t\,\varrho(\mathrm{fin}(bx))Lf\bigr).$$
Take constant terms. The constant term of $J_s g$ is $\theta(g)$ for every scale $s$, and renaming does not change it. By the definition of values, $\theta(\varrho(\mathrm{fin}(x))f) = f(\mathrm{fin}(x))$. $\square$

This lemma is the only place where the analysis of Section 3 meets $\sigma$: a conjugate of a value of $f$ is a value of $Lf$, and values of $Lf$ can be bounded.

**Theorem (The image of the vacuum).** Let $L$ be a jet conjugation for $(\sigma, t, b)$ on a standard space $V$, and let $R$ be a set of finite places of $E$ that is disjoint from its complex conjugate. Then there are $c \in \mathbb{C}$ with $c \ne 0$ and a finite adele $u$ with $u \bar u = 1$ such that
$$L\,\mathrm{vac} = c\,\omega(1, u)\,\mathrm{vac}, \qquad L\bigl(\Psi \otimes \mathrm{vac}\bigr) = c\,\omega(1, u)\bigl((\sigma\circ\Psi) \otimes \mathrm{vac}\bigr)$$
for every function $\Psi$ on $(\mathbb{A}_{E,f})^n$ that is Schwartz-Bruhat above $R$. Here $\omega(1, u)$ is the Weil operator of the scalar matrix $u$ at the finite places, and $\Psi \otimes \mathrm{vac}$ is the Schrödinger datum $\mathrm{schrodingerOp}_R(\Psi)\,\mathrm{vac}$.

Lean: `New.Parameters.IsJetConjugation.exists_map_schrodingerOp` (New/UpperBound/Kernels/JetConjugatesAndBounds.lean).

*Proof.* The law for a map that scales translations, [`New.Space.ScalesTranslations.exists_map_schrodingerOp`](/decl/New.Space.ScalesTranslations.exists_map_schrodingerOp/) of [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/), gives $c$ and $u$ with the two identities. It remains to show $c \ne 0$. If $c = 0$, then $L\,\mathrm{vac} = 0$. The vacuum lies in $V^{\mathrm{fin}}$, so $\mathrm{vac} = 0$ by injectivity. This is false, because $\langle \mathrm{vac}, \mathrm{vac} \rangle = 1$. $\square$

**Example.** For $\sigma = 1$ one may take $t = t_0$, $b = 1$ and $L$ the identity on $V^{\mathrm{fin}}$, provided $|t_0|^2 = \Omega_E^{-1}$. This holds by [the integral vacuum and tight frames](/chapter/integral-vacuum/). Then the theorem on the vacuum holds with $c = 1$ and $u = 1$, and the multiplier ratio is $1$. Complex conjugation is not in $\mathrm{Gal}(\mathbb{C}/K)$, since it maps $\sqrt{-d}$ to $-\sqrt{-d}$. For it there is no jet conjugation in the sense above. Section 4 treats an arbitrary automorphism of $\mathbb{C}$ through one over $K$ with the same absolute values.

**Remark.** The numbers $c$ and $u$ are not explicit. The bounds of Section 3 need only an upper bound for $|c|$. They get it from the conjugate values of $\theta^\circ$ at finite vectors, by the lemma on conjugate values. So $|c|$ is bounded but never computed.
