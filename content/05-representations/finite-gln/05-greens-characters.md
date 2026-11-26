---
title: Green's characters with squarefree labels
lean:
  - Lib/LocalGL/Green/TauFunctions.lean
  - Lib/LocalGL/Green/LabelCharacters.lean
  - Lib/General/Groups/CharacterTheory.lean
decls:
  - New.thetaChar
  - New.charName
  - New.thetaChar_mul
  - New.thetaChar_eq_apply_norm_pow
  - New.thetaChar_charName
  - New.greenTau
  - New.labelChar
  - New.IsLabel
  - New.detChar
  - New.isCuspidal_greenTau
  - New.greenTau_eq
  - New.rankInner_greenTau
  - New.rankInner_labelChar
  - New.rankInner_labelChar_mul_constOne
  - New.skew_greenTau_labelChar_eq_zero
  - New.labelChar_X_sub_C
  - New.labelChar_degree_bounds
  - New.IsIrreducibleChar
  - New.IsLabel.isIrreducibleChar_labelChar
  - New.IsLabel.isChar_labelChar
  - New.labelIdem
  - New.hyperplaneSum
  - New.labelIdem_orthogonal
  - New.hyperplaneSum_mul_labelIdem
  - New.tupleIdem
  - New.isCentralProj_sum_tupleIdem
  - New.evalGL_labelChar_mul_det
  - New.injOn_Iio_pow_card_pow_of_isPrimitiveRoot
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Green's characters with squarefree labels

This section forms Green's functions $\tau_P$ and $\Xi_c$ from the cuspidal functions $C_\eta$ of Section 4, and proves the main theorems of the chapter on them: orthonormality, a lower bound for the degree, and irreducibility. It ends with the tools that the later chapters use.

### Names of characters

The source fixes an injective multiplicative character $T$ of an algebraically closed field $K \supseteq k$, and names the characters of each finite subfield by its elements. Let $\zeta_N = e^{2\pi i/N}$, and let $\mu_{Q-1}$ be the group of $(Q-1)$-th roots of unity in $K$.

**Definition (The characters $\theta_x$).** A pair $(K, T)$ is *faithful* if $K$ is algebraically closed and the multiplicative character $T : K \to \mathbb{C}$ is injective. For $Q \geq 2$ and $x \in K$, let $j(x)$ be a chosen natural number with $T(x) = \zeta_{Q-1}^{j(x)}$, and put $\theta_x = T^{j(x)}$, a multiplicative character of $K$. For a faithful pair and a multiplicative character $\chi$ of $k$, the *name* $x_\chi \in k^\times$ is the inverse of the map $a \mapsto \theta_a|_k$, with $Q = q$.

Lean: `New.IsFaithfulMulChar`, `New.thetaExponent`, `New.thetaChar`, `New.charName`, `New.faithfulChar`, `New.faithfulChar_injective` (Lib/LocalGL/Green/TauFunctions.lean, Lib/General/Geometry/GaloisCovers.lean).

If $T(x) = \zeta^{a}$ and $T(z) = \zeta^{b}$ with $\zeta = \zeta_{Q-1}$, then $\theta_x(z) = \zeta^{ab} = \theta_z(x)$. This symmetry gives the following rules.

**Theorem (Rules for names).** Let $T$ be a multiplicative character of $K$ and $Q \geq 2$.

1. If $x, y, z \in \mu_{Q-1}$, then $\theta_{xy}(z) = \theta_x(z)\theta_y(z)$.
2. Let $Q' = Q^r \geq 2$, $x \in \mu_{Q-1}$, $y = x^a$ and $z \in \mu_{Q'-1}$. Then $\theta_y(z)$, formed with $Q'$, equals $\theta_x(z^{1 + Q + \cdots + Q^{r-1}})^a$, formed with $Q$.
3. If $(K, T)$ is faithful, then $\chi \mapsto x_\chi$ is a group isomorphism from the characters of $k^\times$ onto $k^\times$, and $\theta_{x_\chi}(y) = \chi(y)$ for every $y \in k$.

Lean: `New.thetaChar_mul`, `New.thetaChar_eq_apply_norm_pow`, `New.thetaChar_charName`, `New.charName`, `New.thetaChar_apply_pow` (Lib/LocalGL/Green/TauFunctions.lean).

*Proof.* The key step is this: if $N = (Q-1)m \neq 0$ and $T(z) = \zeta_N^a$, then $\theta_x(z^m) = T(x)^a$. Indeed $\theta_x(z^m) = T(z)^{m j(x)} = \zeta_{Q-1}^{a j(x)} = T(x)^a$. For 1, write $T(z) = \zeta_{Q-1}^a$. Then $\theta_w(z) = T(w)^a$ for each $w \in \{x, y, xy\}$, and $T$ is multiplicative. For 2, $Q' - 1 = (Q-1)(1 + Q + \cdots + Q^{r-1})$, and the key step with $m = 1 + \cdots + Q^{r-1}$ turns both sides into $T(y)^b = T(x)^{ab}$, where $T(z) = \zeta_{Q'-1}^b$. For 3, the map $a \mapsto \theta_a|_k$ is a homomorphism by 1. Its kernel is trivial: if $\theta_a(y) = 1$ for all $y \in k^\times$, then $T(y)^{j(a)} = 1$ for all $y$, so $q - 1$ divides $j(a)$ since $T$ is injective on the cyclic group $k^\times$, and $T(a) = 1$, so $a = 1$. Both groups have $q - 1$ elements. $\square$

So a change from $Q$ to $Q^r$ is composition with the norm.

**Remark (Formalization).** Three objects are chosen by Hilbert's epsilon: the exponent $j(x)$, arbitrary if none exists; the root $x_P$ in $\tau_P$ below, arbitrary if $P$ has no root; and the faithful character of the algebraic closure, used in the idempotents $e_c$, which an instance proves injective. For $x \in \mu_{Q-1}$, $\theta_x$ on $\mu_{Q-1}$ does not depend on the choice of $j(x)$.

### Green's functions

**Definition (Labels and Green's functions).** Let $T$ be a multiplicative character of $K$.

- For $P \in k[X]$ of degree $d$, let $x_P$ be a chosen root of $P$ in $K$, and let $\theta = \theta_{x_P}$, formed with $Q = q^d$. *Green's function* is $\tau_P = (-1)^d \, [C_\theta]_d$.
- For $c \in k[X]$, put $\Xi_0 = 0$ and $\Xi_c = \prod_P \tau_P$ for $c \neq 0$, where the product $*$ runs over the monic irreducible factors $P$ of $c$ with multiplicity. So $c \mapsto \Xi_c$ is multiplicative.
- A *label of degree $r$* is a monic squarefree $c \in k[X]$ of degree $r$ with $c(0) \neq 0$.
- For a character $\chi$ of $k^\times$, the function $\chi \circ \det$ is $c \mapsto \chi((-1)^{\dim c} \, \chi_c(0))$.

Lean: `New.greenTau`, `New.chosenRoot`, `New.labelChar`, `New.IsLabel`, `New.detChar`, `New.labelChar_eq_greenTau` (Lib/LocalGL/Green/TauFunctions.lean).

For a label $c = P_1 \cdots P_s$ of degree $r$, the function $\Xi_c = \tau_{P_1} * \cdots * \tau_{P_s}$ lives in rank $r$, and on $\mathrm{GL}_r(k)$ it is the parabolic induction of $\tau_{P_1} \otimes \cdots \otimes \tau_{P_s}$ from a Levi subgroup $\prod_i \mathrm{GL}_{\deg P_i}(k)$. In rank $2$, for irreducible $P$ of degree $2$, $\tau_P = C_\theta$ with $\theta = \theta_{x_P}$, and $\Xi_{(X-a)(X-b)}$ is the principal series.

**Theorem (Green's functions $\tau_P$).** Let $T$ be a multiplicative character of $K$ and $P \in k[X]$.

1. $\tau_P$ is cuspidal, and it vanishes on the classes of dimension different from $\deg P$.
2. Let $(K, T)$ be faithful, and let $P$ be irreducible with $P(0) \neq 0$. For every root $x$ of $P$ in $K$, $\tau_P = (-1)^d [C_{\theta_x}]_d$, with $d = \deg P$ and $\theta_x$ formed with $q^d$.
3. Let $(K, T)$ be faithful, and let $P$ be monic irreducible with $P(0) \neq 0$. For every monic irreducible $S$ with $S(0) \neq 0$, $\langle \tau_P, \tau_S \rangle_{\deg P}$ is $1$ if $P = S$ and $0$ otherwise. If $P(1) \neq 0$, then $\partial^{\deg P}_{\tau_P} \mathbb{1} = 0$.

Lean: `New.isCuspidal_greenTau`, `New.greenTau_eq_zero_of_dim_ne`, `New.greenTau_eq`, `New.rankInner_greenTau` (Lib/LocalGL/Green/TauFunctions.lean).

*Proof.* 1. The rank $d$ part of a cuspidal function is cuspidal, and $C_\theta$ is [cuspidal](/decl/New.Hall.isCuspidal_greenCuspidal/).

2. Let $d = \deg P$. The chosen root is $x^{q^i}$ for some $i$. Since $x^{q^d - 1} = 1$, part 2 of the rules with $r = 1$ and $a = q^i$ gives $\theta_{x^{q^i}}(z) = \theta_x(z^{q^i})$ for every $z \in \mu_{q^d-1}$. At a class of dimension $d$ where $C$ can be nonzero, the eigenvalues $z$ form a Frobenius orbit with $z^{q^d} = z$, and $z \mapsto z^{q^i}$ permutes the orbit. So [the dependence on the orbit](/decl/New.greenCuspidal_simClassOf_eq_mul/), with $a = 1$, gives the claim.

3. Let $L$ be the field with $q^d$ elements, embedded in $K$. Every monic irreducible $S$ of degree $d$ with $S(0) \neq 0$ has a root in $L^\times$, and every element of $L^\times$ is the name $x_\xi$ of a character $\xi$ of $L^\times$. Write $x_P = x_\chi$ and $x_S = x_\xi$ by part 2. Since $C_{\theta_\chi}$ is cuspidal, [the Leibniz rule](/decl/New.Hall.rankInner_mul_of_isCuspidal/) applies to $C_{\theta_\xi} = (\beta_{\theta_\xi}\mu) * \mathbb{1}$. The term with $\langle C_{\theta_\chi}, \mathbb{1} \rangle_d$ has the factor $(\beta_{\theta_\xi}\mu)(o) = 0$. So [the mean over a torus](/decl/New.rankInner_greenCuspidal_mulMoebius/) gives
$$\langle C_{\theta_\chi}, C_{\theta_\xi} \rangle_d = \frac{1}{|L^\times|} \sum_{z \in L^\times} \overline{\chi(z)} \sum_{i < d} \xi(z^{q^i}),$$
since $\theta_{x_\chi} = \chi$ on $L$ and the eigenvalues of $m_z$ are the $z^{q^i}$. By orthogonality of the characters of $L^\times$, this is the number of $i < d$ with $\chi = \xi^{q^i}$, that is, with $x_P = x_S^{q^i}$. It is $1$ if $S = P$ and $0$ otherwise. The two signs $(-1)^d$ cancel. If $\deg S \neq d$, then $\tau_S$ vanishes in rank $d$.

For the last claim, $\partial^d_{\tau_P}\mathbb{1}(a) = \langle \tau_P, \mathbb{1} \rangle_d$ for every $a$, since $\delta\mathbb{1} = \mathbb{1}$. Apply the Leibniz rule to $(\mathbb{1}\mu) * \mathbb{1} = 1$, which vanishes in rank $d \geq 1$: $0 = \langle C, \mu \rangle_d + \langle C, \mathbb{1} \rangle_d$, with $C = C_{\theta_\chi}$ and $\mu(o) = 1$. The mean over the torus gives $\langle C, \mu \rangle_d = |L^\times|^{-1} \sum_z \overline{\chi(z)} = 0$, since $\chi$ is not trivial: $x_\chi = x_P \neq 1$, because $P(1) \neq 0$. $\square$

### Orthonormality and the degree

**Theorem (Orthonormality).** Let $(K, T)$ be faithful and let $c$ be a label of degree $r$.

1. For every label $c'$ of degree $r$, $\langle \Xi_c, \Xi_{c'} \rangle_r$ is $1$ if $c = c'$ and $0$ otherwise.
2. If $c(1) \neq 0$, then $\langle \Xi_c, A * \mathbb{1} \rangle_r = \langle \Xi_c, A \rangle_r$ for every $A \in \mathcal{H}(k)$.
3. If $P$ is an irreducible label of degree $d$ that does not divide $c$, then $\partial^d_{\tau_P} \Xi_c = 0$.
4. For every character $\chi$ of $k^\times$, $\Xi_{X - x_\chi} = [\chi \circ \det]_1$.

Lean: `New.rankInner_labelChar`, `New.rankInner_labelChar_mul_constOne`, `New.skew_greenTau_labelChar_eq_zero`, `New.labelChar_X_sub_C`, `New.rankPart_labelChar` (Lib/LocalGL/Green/LabelCharacters.lean).

*Proof.* All parts use that $\partial^d_{\tau_P}$ is [a derivation](/decl/New.Hall.skew_mul/) and that $\partial^d_{\tau_P} \tau_S = \langle \tau_P, \tau_S \rangle_d \cdot 1$ for cuspidal $\tau_S$, by [the Leibniz rule](/decl/New.Hall.rankInner_mul_of_isCuspidal/).

3. Apply the derivation to $\Xi_c = \prod_S \tau_S$. Each term contains $\partial^d_{\tau_P} \tau_S = \langle \tau_P, \tau_S \rangle_d \cdot 1$, and this is $0$ since $S \neq P$.

1. Induct on the factors of $c$. For $c = 1$ the claim is $\langle 1, \Xi_{c'} \rangle_0 = \Xi_{c'}(o)$, which is $1$ for $c' = 1$ and $0$ otherwise. For $c = P c''$, [the adjunction in one degree](/decl/New.Hall.rankInner_mul_eq_rankInner_skew/) gives $\langle \tau_P * \Xi_{c''}, \Xi_{c'} \rangle_r = \langle \Xi_{c''}, \partial^d_{\tau_P} \Xi_{c'} \rangle_{r-d}$. If $P \nmid c'$, then this is $0$ by 3. If $c' = P c'''$, then $\partial^d_{\tau_P} \Xi_{c'} = \langle \tau_P, \tau_P \rangle_d \, \Xi_{c'''} + \tau_P * \partial^d_{\tau_P} \Xi_{c'''} = \Xi_{c'''}$ by 3, since $P \nmid c'''$. Apply induction.

2. The same induction, with $\partial^d_{\tau_P}(A * \mathbb{1}) = (\partial^d_{\tau_P} A) * \mathbb{1}$, since $\partial^d_{\tau_P}\mathbb{1} = 0$ by [the theorem on $\tau_P$](/decl/New.rankInner_greenTau/) when $P(1) \neq 0$. At $c = 1$ both sides are $A(o)$.

4. Let $\theta = \theta_{x_\chi}$, formed with $q$. In rank $1$, $C_\theta = -\beta_\theta$, since $C_\theta * \mathbb{1} = -\beta_\theta$ and $C_\theta(o) = 0$. So $\tau_{X - x_\chi}$ is $\theta$ at the eigenvalue $a$ of a class of dimension $1$, and $\theta(a) = \chi(a)$ by the rules for names. $\square$

The degree is the value at $1$. The proof below finds it exactly, although the source states only a bound. Let $\delta_1$ be the indicator function of the classes of identity maps. A factor $\tau_P$ of degree $d$ in front of $F$ multiplies the pairing with $\delta_1 \mu$ by $(-1)^d / (q^d - 1)$. This follows from the adjunction and [the corollary on $C_\eta\mu$](/decl/New.mulMoebius_greenCuspidal_lsmul/) at the generator $1$ of $k$. So $\langle \Xi_c, \delta_1 \mu \rangle_r \cdot B = (-1)^r$ with $B = \prod_{P \mid c} (q^{\deg P} - 1) \leq q^r$. With $\mu(1) = \prod_{i<r}(-q^i)$, this gives
$$\Xi_c(1) = \frac{|\mathrm{GL}_r(k)|}{B \prod_{i<r} q^i} = \frac{\prod_{i=1}^r (q^i - 1)}{\prod_{P \mid c} (q^{\deg P} - 1)}.$$
In rank $2$ this is $q - 1$ or $q + 1$, as in Section 1.

**Theorem (Degree bound).** Let $(K, T)$ be faithful, let $n$ be a finite set and let $c$ be a label of degree $|n|$. Put $d = \Xi_c(1)$ on $\mathrm{GL}_n(k)$. Then $\operatorname{Re} d \geq 0$ and
$$\frac{1 - |n|/q}{q^{|n|}} \leq \frac{d \, \bar d}{|\mathrm{GL}_n(k)|}.$$

Lean: `New.labelChar_degree_bounds`, `sub_mul_pow_mul_prod_le_mul_prod` (Lib/LocalGL/Green/TauFunctions.lean).

*Proof.* By the value above, $d$ is a positive real number. Write $r = |n|$. Then $d^2 / |\mathrm{GL}_r(k)| = q^r \prod_{i<r} (1 - q^{-(i+1)}) / B^2 \geq q^{-r} \prod_{i < r}(1 - q^{-(i+1)})$, since $B \leq q^r$. By induction on $r$, $\prod_{i<r} (1 - q^{-(i+1)}) \geq 1 - r/q$: one more factor needs $(q - r - 1) q^{r+1} \leq (q - r)(q^{r+1} - 1)$, that is, $q - r \leq q^{r+1}$. $\square$

The inequality is in the partial order of $\mathbb{C}$, so it also says that the quotient is real. The bound is empty when $q \leq |n|$.

### Irreducibility

**Theorem (Green's characters are irreducible).** Let $(K, T)$ be faithful, let $n$ be a finite set, and let $c$ be a label of degree $|n|$. Then $f = \Xi_c|_{\mathrm{GL}_n}$ is an irreducible character in this sense:

1. $f$ is the character of a finite dimensional complex representation of $G = \mathrm{GL}_n(k)$;
2. $\langle f, f \rangle_G = 1$;
3. for every class function $h$ on $G$ and every $y \in G$, $f(1) \cdot |G|^{-1} \sum_t \overline{f(t)} h(ty) = \langle f, h \rangle_G \, f(y)$.

For every label $c$ of any degree $r$, $\Xi_c|_{\mathrm{GL}_n}$ is a character.

Lean: `New.IsLabel.isIrreducibleChar_labelChar`, `New.IsIrreducibleChar`, `New.IsChar`, `New.IsLabel.isChar_labelChar`, `New.isIrreducibleChar_and_mem_virtualChars_and_exists_mul` (Lib/LocalGL/Green/LabelCharacters.lean, Lib/General/Groups/CharacterTheory.lean).

*Proof.* First, $f$ is a $\mathbb{Z}$-combination of characters of $G$. Section 6 proves this: [the eigenvalue sum has a virtual lift](/decl/New.exists_lift_brauerLift/), the lifts are closed under the operations that make $\tau_P$ from $\beta_\theta$, and [they are closed under products](/decl/New.Lift.mul/). Write $f = \sum_\rho m_\rho \chi_\rho$ over the irreducible characters, with $m_\rho \in \mathbb{Z}$. By orthonormality, $\sum m_\rho^2 = 1$, so $f = \pm\chi_\rho$ for one $\rho$. Since $\operatorname{Re} f(1) \geq 0$ by the degree bound, the sign is $+$. So $f$ is the character of an irreducible representation, and clause 3 is Schur's lemma for the central element $\sum_t h(t^{-1}) t$.

For a label of degree $r \neq |n|$, $f = 0$, the character of the zero representation. $\square$

**Remark (Formalization).** The textbook form is that $\Xi_c$ is the character of an irreducible representation. The source adds clause 3, a consequence of irreducibility, because the idempotents below need it. The source does not state the exact degree, and it treats only squarefree labels. Green's theorem gives all the irreducible characters of $\mathrm{GL}_n(k)$, with labels that are functions from irreducible polynomials to partitions (Macdonald, *Symmetric Functions and Hall Polynomials*, Chapter IV). A squarefree label is the case where all partitions have one part equal to $1$. So in rank $2$ the chapter does not reach $\chi \circ \det$ or the Steinberg twists.

### Idempotents, hyperplanes and twists

Let $n$ be a finite set, $G = \mathrm{GL}_n(k)$, and let $\Xi_c$ be formed with the chosen faithful character of the algebraic closure of $k$.

**Theorem (Label idempotents).** For $c \in k[X]$ let $e_c \in \mathbb{C}[G]$ be $\sum_g (\Xi_c(1)/|G|) \, \overline{\Xi_c(g)} \, g$ if $c$ is a label of degree $|n|$, and $e_c = 0$ otherwise.

1. The $e_c$ are idempotents, $e_c e_{c'} = 0$ for $c \neq c'$, and the coefficients of each $e_c$ form a class function.
2. Let $\chi$ be a character of $k^\times$ with $c(x_\chi) \neq 0$, and let $l \in k^n$ be nonzero. Let $H_l = \sum_h \chi(\det h)^{-1} \, h$, over the $h \in G$ of the form $1 + u l^{\mathsf T}$ with $u \in k^n$. Then $H_l \, e_c = 0$.
3. For finite fields $k_w$, $w \in \iota$, and a tuple $c = (c_w)$, let $e_c = \bigotimes_w e_{c_w}$ in $\mathbb{C}[\prod_w \mathrm{GL}_n(k_w)]$. These are orthogonal idempotents, and for every finite set $s$ of tuples, $\sum_{c \in s} e_c$ is a central idempotent.

Lean: `New.labelIdem`, `New.labelIdem_orthogonal`, `New.isClassFunction_labelIdem_coeff`, `New.hyperplaneSum`, `New.hyperplaneSum_mul_labelIdem`, `New.skew_detChar_labelChar_eq_zero`, `New.tupleIdem`, `New.tupleIdem_orthogonal`, `New.isCentralProj_tupleIdem`, `New.isCentralProj_sum_tupleIdem`, `New.IsCentralProj` (Lib/LocalGL/Green/LabelCharacters.lean, Lib/General/Groups/CharacterTheory.lean).

*Proof.* 1. The coefficient of $e_c e_{c'}$ at $x$ is $\Xi_c(1)/|G|$ times $\Xi_{c'}(1) |G|^{-1} \sum_t \overline{\Xi_{c'}(t)} \, \Xi_c(t x^{-1})$, up to the conjugation $\overline{\Xi(g)} = \Xi(g^{-1})$ of a character. Clause 3 of irreducibility, with $h = \Xi_c$, and orthonormality turn this into $[c = c'] \, \Xi_c(1)/|G| \cdot \overline{\Xi_c(x)}$. A product of class functions under conjugation is a class function.

2. The $h = 1 + u l^{\mathsf T}$ that are invertible form a subgroup $N$. Choose a basis whose first vector $v$ has $l \cdot v = 1$ and whose other vectors span the hyperplane $l^{\perp}$. In it, $N$ is the group of block triangular matrices with a $1 \times 1$ block $g \in k^\times$, an identity block on $l^\perp$, and an arbitrary corner. The mean over $N$ of $\Xi_c \cdot \chi^{-1}(\det)$ is then a value of $\partial^1_{\chi \circ \det} \Xi_c$, and this vanishes. Indeed, $\chi \circ \det$ in rank $1$ is $\tau_{X - x_\chi}$ by orthonormality part 4, and $X - x_\chi$ does not divide $c$, so part 3 applies. The same holds for every translate $\Xi_c(\cdot \, x)$, by clause 3 of irreducibility, so each coefficient of $H_l e_c$ is $0$.

3. Tensor products are multiplicative, so 1 gives the relations. A sum of orthogonal idempotents is idempotent. $\square$

**Theorem (Twists and conjugates).** Let $(K, T)$ be faithful.

1. Let $c$ be a label and $\chi$ a character of $k^\times$. Let $c'$ be the polynomial whose roots are $x_\chi$ times those of $c$, namely $c' = x_\chi^{\deg c} c(x_\chi^{-1} X)$. Then $c'$ is a label of the same degree, and $\Xi_c(g) \chi(\det g) = \Xi_{c'}(g)$ for every finite set $n$ and $g \in \mathrm{GL}_n(k)$.
2. Let $9 \mid q - 1$, $e \geq 0$, let $\xi \in K$ be a primitive root of unity of order $q^{3^{e+1}} - 1$, let $\ell$ be a prime and $a \geq 0$. Then the $(\xi^{\ell^a})^{q^i}$ for $0 \leq i < 3^{e+1}$ are distinct.

Lean: `New.evalGL_labelChar_mul_det`, `New.scaleRootsEquiv`, `New.IsLabel.scaleRoots`, `New.injOn_Iio_pow_card_pow_of_isPrimitiveRoot` (Lib/LocalGL/Green/LabelCharacters.lean).

*Proof.* 1. Let $\theta$ be the character of $K$ named by $x_\chi$, so $\chi(\det g)$ is $\theta$ at the product of the eigenvalues of $g$. This value is multiplicative over a stable subspace and its quotient, so twisting commutes with $*$, and it suffices to twist one factor $\tau_P$. Take a root $y$ of $P$ and the root $x_\chi y$ of the scaled polynomial, by part 2 of the theorem on $\tau_P$. At a class whose eigenvalues are the $z^{q^i}$, $i < \deg P$, the value of $\theta$ at $\det$ is $\theta$ at the norm of $z$. By part 2 of the rules for names, this is the character named by $x_\chi$ for $q^{\deg P}$, at $z$. The dependence on the orbit then gives the claim.

2. Put $s$ with $q^{3^e} = 9s + 1$, which exists since $9 \mid q - 1$, and $s \neq 0$. Then $q^{3^{e+1}} - 1 = 9s \cdot b$ with $b = 81 s^2 + 27 s + 3$. The orbit of $\xi^{\ell^a}$ under $z \mapsto z^q$ has a length that divides $3^{e+1}$. If it divided $3^e$, then $\xi^{\ell^a (q^{3^e} - 1)} = 1$, so the element $\xi^{9s}$ of order $b$ would satisfy $(\xi^{9s})^{\ell^a} = 1$ and $b \mid \ell^a$. But $3 \mid b$ and $9 \nmid b$, so $b = 3$, and then $s = 0$. $\square$

Part 2 gives elements of degree exactly $3^{e+1}$ over $k$, and so irreducible labels of that degree.
