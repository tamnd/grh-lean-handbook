---
title: The infinite places and the number Ω
lean:
  - New/Reduction/Data/FieldsAndPlaces.lean
  - New/Reduction/Data/LevelAndTwists.lean
  - New/Reduction/Data/AdmissibleData.lean
  - Lib/General/NumberTheory/ImaginaryQuadraticField.lean
decls:
  - New.Parameters.galOfPlace
  - New.Parameters.placeMulEquiv
  - New.Parameters.placeOfInt
  - New.Parameters.placeClass
  - New.Parameters.galOfPlace_zeta
  - New.Parameters.numInfPlaces_E
  - New.Parameters.card_placeClass_eq_one_eq_towerDeg
  - New.Parameters.placeClass_placeOfInt_eq_neg_one_iff
  - New.Parameters.prod_phi_eq_norm
  - New.chowlaSelbergConst
  - New.Parameters.bigOmega
  - New.rootDiscr_mem_Icc
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The infinite places and the number $\Omega$

The automorphic forms of the argument have a weight at each infinite place of $E$. This section shows that these places form a group $\Phi$, isomorphic to $\mathrm{Gal}(E/K)$ and to $(\mathbb{Z}/q_1)^\times$, and it counts them. It ends with the real number $\Omega$, a period scale built from the constant of Chowla and Selberg and the root discriminant of $E$.

### The places as a group

The field $E$ is totally complex of degree $2\varphi(q_1)$, so it has $\varphi(q_1)$ infinite places. Each is a pair $\{\tau, \bar\tau\}$ of complex embeddings. The field $K$ has one infinite place, and its two embeddings are the inclusion $K \subset \mathbb{C}$ and its conjugate. So each infinite place $v$ of $E$ has exactly one embedding $\Phi_v : E \to \mathbb{C}$ that restricts to the inclusion on $K$. The group $G = \mathrm{Gal}(E/K)$ acts on the $K$-embeddings simply transitively. So, after the choice of one $K$-embedding $\iota : E \to \mathbb{C}$, every infinite place has the form $v_g$, the place of $\iota \circ g$, for exactly one $g \in G$.

**Definition (The group of places).** Fix a $K$-embedding $\iota$ of $E$ into $\mathbb{C}$. The set $\Phi$ of infinite places of $E$ is a commutative group, with the law transported from $G$ along $g \mapsto v_g$. Let $\sigma : \Phi \to \mathrm{Gal}(E/K)$ be the inverse isomorphism, $v \mapsto \sigma_v$. Composed with $\mathrm{Gal}(E/K) \cong (\mathbb{Z}/q_1)^\times$, it gives an isomorphism $\Phi \cong (\mathbb{Z}/q_1)^\times$.

Lean: `New.Parameters.galOfPlace`, `New.Parameters.placeMulEquiv` (New/Reduction/Data/FieldsAndPlaces.lean).

The embedding at the place $v$ is $\Phi_v = \iota \circ \sigma_v$. The family $(\Phi_v)_{v \in \Phi}$ is a CM type of $E$: one embedding from each conjugate pair. It satisfies $\Phi_{vv'} = \Phi_v \circ \sigma_{v'}$ (Lean: `New.Parameters.phi_mul`), and each $\Phi_v$ is the inclusion on $K$ (Lean: `New.Parameters.phi_algebraMap`). The place that corresponds to $a \in (\mathbb{Z}/q_1)^\times$ acts on $\zeta$ by $\zeta \mapsto \zeta^a$.

**Lemma.** For every $v \in \Phi$, one has $\sigma_v(\zeta) = \zeta^{a}$, where $a$ is the image of $v$ in $(\mathbb{Z}/q_1)^\times$, read as an integer in $[0, q_1)$.

Lean: `New.Parameters.galOfPlace_zeta` (New/Reduction/Data/FieldsAndPlaces.lean).

**Remark (Formalization).** The group law on $\Phi$ depends on the choice of $\iota$. Another choice $\iota \circ h$ moves the identity element by $h$. The source fixes $\iota$ once, as Mathlib's lift of $E$ into the algebraically closed field $\mathbb{C}$, so the identity place and the CM type $(\Phi_v)$ are choices. The source proves its statements for this one fixed choice.

### Places named by integers, and classes of places

The source names places by integers.

**Definition.** For $\nu \in \mathbb{Z}$, the place $v_\nu \in \Phi$ is the place that corresponds to $\nu \bmod q_1$ if $\nu$ is prime to $q_1$, and the identity place otherwise. For $m \mid q_1$, the class of $v$ modulo $m$ is the image of $v$ under $\Phi \cong (\mathbb{Z}/q_1)^\times \to (\mathbb{Z}/m)^\times$.

Lean: `New.Parameters.placeOfInt`, `New.Parameters.placeClass` (New/Reduction/Data/FieldsAndPlaces.lean).

**Remark (Formalization).** The value $v_\nu = 1$ for $\nu$ not prime to $q_1$ is a junk value. The lemmas on $v_\nu$ carry the hypothesis that $\nu$ is prime to $q_0$, which is the same as prime to $q_1$, since $q_0$ and $q_1$ have the same prime factors. Under this hypothesis the class of $v_\nu$ modulo $m$ is $\nu \bmod m$, $\sigma_{v_\nu}(\zeta) = \zeta^\nu$, and $v_\nu^i = v_{\nu^i}$ (Lean: `New.Parameters.placeClass_placeOfInt`, `New.Parameters.galOfPlace_placeOfInt_zeta`, `New.Parameters.placeOfInt_pow`).

The data of the argument split $\Phi$ by the class modulo $q_0$. The $a$-places are the places of class $1$ modulo $q_0$. The $b$-places are a chosen sparse set of places of class $-1$ modulo $q_0$. The two counts below are used in [the data and its sizes](/chapter/data-and-sizes/) and in [prime sums and the total remainder](/chapter/prime-sums/).

**Theorem.** The number of infinite places of $E$ is $f = \#\Phi = \mathrm{towerDeg}(s) \cdot \varphi(q_0)$. Exactly $\mathrm{towerDeg}(s)$ of them have class $1$ modulo $q_0$.

Lean: `New.Parameters.numInfPlaces_E`, `New.Parameters.card_placeClass_eq_one_eq_towerDeg` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* We have $\#\Phi = \varphi(q_1)$. If a prime $p$ divides $N$, then $\Phi_N(X^p) = \Phi_{Np}(X)$. Since $2$ and $3$ divide $q_0$, repeated use gives $\Phi_{q_0}(X^{\mathrm{towerDeg}(s)}) = \Phi_{q_1}(X)$ (Lean: `New.Parameters.expand_towerDeg_cyclotomic`). Compare degrees: $\varphi(q_1) = \varphi(q_0) \cdot \mathrm{towerDeg}(s)$. For the second claim, the reduction map $(\mathbb{Z}/q_1)^\times \to (\mathbb{Z}/q_0)^\times$ is onto. So its kernel, the places of class $1$, has index $\varphi(q_0)$ and order $\varphi(q_1)/\varphi(q_0) = \mathrm{towerDeg}(s)$. $\square$

**Proposition.** Suppose $q_0 \mid q_1$. For $\nu \in \mathbb{Z}$, the place $v_\nu$ has class $-1$ modulo $q_0$ if and only if $\nu \equiv -1 \bmod q_0$.

Lean: `New.Parameters.placeClass_placeOfInt_eq_neg_one_iff` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* If $\nu$ is a unit modulo $q_1$ the class is $\nu \bmod q_0$. If not, then $v_\nu = 1$, its class is $1$, and $1 \ne -1$ in $\mathbb{Z}/q_0$, by the lemma $d^0 \not\equiv -1$ of Section 2. Conversely, $\nu \equiv -1 \bmod q_0$ makes $\nu$ prime to $q_0$. $\square$

The hypothesis $q_0 \mid q_1$ is always true. The reduction map of the source takes it as an argument.

### Norms as products over the places

**Theorem.** For every $y \in E$,
$$\prod_{v \in \Phi} \Phi_v(y) = N_{E/K}(y),$$
where $K \subset \mathbb{C}$ is the subfield $\mathbb{Q}(i\sqrt d)$.

Lean: `New.Parameters.prod_phi_eq_norm` (New/Reduction/Data/FieldsAndPlaces.lean).

*Proof.* The norm is the product of the conjugates $\sigma_v(y)$ over $v \in \Phi$, since $v \mapsto \sigma_v$ is a bijection onto $\mathrm{Gal}(E/K)$. Apply the embedding $\Phi_1 = \iota$, which is the identity on $K$, and use $\Phi_1 \circ \sigma_v = \Phi_v$. $\square$

With $N_{E/K}(\zeta) = 1$ this gives $\prod_v \Phi_v(\zeta^k)^{n} = 1$ for every $k$ and $n$. Section 6 uses this.

### The number $\Omega$

The constant of Chowla and Selberg is the real number
$$C_d = \gamma - \operatorname{Re} \frac{L'}{L}(1, \chi_K),$$
where $\gamma$ is Euler's constant and $L(s, \chi_K)$ is the Dirichlet L-function of the character $\chi_K = (\cdot/d)$.

Lean: `New.chowlaSelbergConst` (Lib/General/NumberTheory/ImaginaryQuadraticField.lean).

**Remark (Formalization).** The source writes $\chi_K$ as the twist of the character modulo $1$ by $(\cdot/d)$, a character modulo $1 \cdot d$, and it takes the logarithmic derivative of the entire function `New.entireL` of this character. For $d$ odd the character is not principal, so this function is $L(s, \chi_K)$ itself. Its value at $s = 1$ is not $0$, so the logarithmic derivative at $1$ is a true value, not a junk value. The value $L'/L(1,\chi_K)$ is real, since $\chi_K$ is real; the real part in the definition only makes the type real.

**Definition.** For parameters $(q_0, d)$ and $s \ge 0$ let
$$\Omega = e^{C_d} \cdot \frac{2\pi}{\mathrm{rd}_E},$$
where $\mathrm{rd}_E = |d_E|^{1/[E:\mathbb{Q}]}$ is the root discriminant of $E$.

Lean: `New.Parameters.bigOmega` (New/Reduction/Data/FieldsAndPlaces.lean).

The root discriminant is Mathlib's `rootDiscr`. It is positive, so $\Omega > 0$ (Lean: `New.Parameters.bigOmega_pos`). The source bounds $\mathrm{rd}_E$ through the different.

**Proposition.** Let $F$ be a number field, and let $c \ne 0$ be a natural number with $c \in \mathfrak{D}_F$, the different of $F$. Then $1 \le \mathrm{rd}_F \le c$. For $F = E$ one can take $c = q_1 d$, so $1 \le \mathrm{rd}_E \le q_1 d$.

Lean: `New.rootDiscr_mem_Icc` (New/Reduction/Data/AdmissibleData.lean).

*Proof.* The absolute norm of $\mathfrak{D}_F$ is $|d_F|$. Since $c \in \mathfrak{D}_F$, the ideal $(c)$ is contained in $\mathfrak{D}_F$, so $|d_F|$ divides $N(c) = c^{[F:\mathbb{Q}]}$. Take the root of degree $[F:\mathbb{Q}]$. The lower bound is $|d_F| \ge 1$. For $E$, the different of $E$ is the product of the different of $E/K$, which contains $q_1$, and the different of $K$, which is $(\sqrt{-d})$ and contains $d$ (Lean: `New.Parameters.conductor_mem_differentIdeal`). $\square$

For the data the source proves the sharper bounds $x^{10} \le \mathrm{rd}_E \le x^{12}$, and from them
$$x^{-13} \le \Omega \le 1$$
(Lean: `New.Data.rootDisc_mem_Icc`, and an instance at [LevelAndTwists.lean](lean:New/Reduction/Data/LevelAndTwists.lean#L184)). The proof uses $|C_d| + 6 \le \log x$, a scale inequality of [the data and its sizes](/chapter/data-and-sizes/), and $1 \le 2\pi \le e^6$.

**Remark (Formalization).** The role of $\Omega$ is in the later volumes. The source uses it as the scale by which the Galois conjugates of the Petersson norms of the lifts differ: for $\sigma \in \mathrm{Aut}(\mathbb{C}/K)$ (here $\sigma$ is an automorphism of $\mathbb{C}$, not an automorphism $\sigma_v$ of $E$), the absolute value of the conjugate of the Petersson square of a scaled lift of total row length $J$ is $\Omega^{-J}$ times a positive constant times the squared norm of another lift (see `New.Data.CriticalPair.exists_norm_map_inner_trivialLift_eq_mul` in New/OneLift/HeckeValues/AlgebraicPartSize.lean). The same constant $C_d$ appears in the value of the constant $c_q$ of [the weighted prime remainder](/chapter/weighted-prime-remainder/).
