---
title: The Bessel group and equivariant functions
lean:
  - Lib/Weil/Periods/Grading.lean
  - Lib/Weil/Periods/Equivariant.lean
  - Lib/Weil/Periods/BesselIntegral.lean
decls:
  - New.Grading.unipotent
  - New.Grading.inclX
  - New.Grading.besselGroup
  - New.Grading.exists_besselGroup_proj
  - New.Grading.isCocompact_ratBessel
  - New.Grading.besselMeasure
  - New.Grading.unipotentChar
  - New.Grading.unipotentChar_mul
  - New.Grading.IsEquivariant
  - New.Grading.sourceFn
  - New.Grading.isEquivariant_sourceFn
  - New.Grading.IsEquivariant.eq_sourceFn
  - New.Grading.integral_besselMeasure_eq_of_mean
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Bessel group and equivariant functions

A grading of $V$ defines three subgroups of the adelic unitary group $G$ of $V$: a unipotent group $U$, a copy $H$ of the unitary group of $X$, and the Bessel group $R = U \rtimes H$. This section defines them, proves that $R(E)$ is cocompact in $R(\mathbb{A})$, and defines the generic character $\psi_U$. It then defines the functions on $[R] = R(E) \backslash R(\mathbb{A})$ that the unfolding acts on, and the first such function, built from an automorphic form on $U(X)$.

Throughout, $Y$ is a grading of $V$ with constant $N$, part $X$, string length $s$ and constant $c$, as in [Definition](/decl/New.Grading/). All conditions on an element $g \in G$ are conditions on its matrix in rational coordinates, which is also written $g$.

### Three subgroups

**Definition (The unipotent group).** The group $U$ is the set of $g \in G$ such that $g - 1$ has degree at least $1$ for the grades: $g - 1$ sends each basis vector of grade $k$ into the span of the basis vectors of grade $> k$.

Lean: `New.Grading.unipotent`, with `New.Grading.mem_unipotent` (Lib/Weil/Periods/Grading.lean).

**Definition (The embedding of $U(X)$).** Let $H = G_X$ be the adelic unitary group of the standard definite space on $X$. The map $\iota_X \colon H \to G$ sends $a$ to the element whose matrix in rational coordinates is $a$ on $X$ and the identity on the string.

Lean: `New.Grading.inclX` (Lib/Weil/Periods/Grading.lean).

**Definition (The Bessel group).** The Bessel group $R$ is the set of $g \in G$ such that, for each string vector $e_k$ of grade $\geq 0$, the vector $g e_k - e_k$ lies in the span of the basis vectors of grade $> \operatorname{grade}(e_k)$. Equivalently, the entry $(i, k)$ of the matrix of $g$ is that of the identity whenever $e_k$ is a string vector of grade $\geq 0$ and the grade of $i$ is at most that of $e_k$. Its rational points are $R(E) = R \cap V.\Gamma$.

Lean: `New.Grading.besselGroup`, `New.Grading.mem_besselGroup`, `New.Grading.ratBessel` (Lib/Weil/Periods/Grading.lean).

The group $R$ contains $U$ and $\iota_X(H)$ (Lean: `New.Grading.unipotent_le_besselGroup`, `New.Grading.inclX_mem_besselGroup`), and it is closed (Lean: `New.Grading.isClosed_besselGroup`).

**Proposition (Levi decomposition).** There is a continuous homomorphism $p \colon R \to H$ with these properties:

1. $r \cdot \iota_X(p(r))^{-1} \in U$ for every $r \in R$;
2. $p(\iota_X(a)) = a$ for every $a \in H$;
3. $r \in U$ if and only if $p(r) = 1$;
4. $p$ maps $R(E)$ into the rational points of $H$.

Lean: `New.Grading.exists_besselGroup_proj`, with `New.Grading.besselProj` and `New.Grading.exists_unipotent_mul_inclX` (Lib/Weil/Periods/Grading.lean).

*Proof.* Take for $p(r)$ the block of the matrix of $r$ on $X$. For $r \in R$ this block is unitary for the standard form on $X$. The map $p$ is multiplicative on $R$. Indeed, the $X$ block of a product $gh$ is the product of the $X$ blocks plus a sum over the string vectors $e_a$ of (entry of $g$ from $e_a$ to $X$) times (entry of $h$ from $X$ to $e_a$). For $g, h \in R$ one of the two factors is $0$ for each $a$: the first if $e_a$ has grade $\geq 0$, the second if $e_a$ has grade $\leq 0$. Off the $X$ block, the conditions that define $U$ and $R$ are the same. So $r \in U$ if and only if $p(r) = 1$, which is (3). Apply (3) to $r\, \iota_X(p(r))^{-1}$, whose image under $p$ is $1$ by (2), to get (1). Property (2) holds because $\iota_X(a)$ has $X$ block $a$. Property (4) holds because the entries of the $X$ block of a rational matrix are rational. $\square$

So $R = U \rtimes \iota_X(H)$: every $g \in R$ is $n \cdot \iota_X(a)$ with $n \in U$ and $a \in H$. The source fixes one such projection by choice (Lean: `New.Grading.leviPart`).

**Theorem (Cocompactness).** There is a compact set $C \subseteq R$ such that every $g \in R$ has a rational $\gamma \in R(E)$ with $\gamma g \in C$.

Lean: `New.Grading.isCocompact_ratBessel` (Lib/Weil/Periods/BesselIntegral.lean).

*Proof.* There is a compact $A \subseteq \mathbb{A}$ that meets every coset $a + E$, since $\mathbb{A}/E$ is compact. The group $H$ is the unitary group of a definite space, so $H(E) \backslash H$ is compact: there is a compact $D \subseteq H$ such that each $a \in H$ has a rational $\delta$ with $\delta a \in D$. Let $g \in R$. First move $p(g)$ into $D$ with $\gamma = \iota_X(\delta)$ for a rational $\delta$. Then $\gamma g = m\, \iota_X(a)$ with $m \in U$ and $a \in D$. The matrix $m - 1$ raises grades, so $m$ is unitriangular for the order of the grades. By downward recursion on the grades there is a rational unitriangular matrix $Z$ such that every entry of $m^{-1} Z$ is $0$, $1$ or an element of $A$. A lemma on frames of bounded entries then gives a rational unitriangular isometry $\beta$ with $\beta m$ in a fixed compact set $K$ of $G$. The element $\beta$ agrees with $1$ wherever the grade does not rise, so $\beta \in R(E)$. Then $\beta\gamma g \in K \cdot \iota_X(D)$, and the compact set is $R \cap K \cdot \iota_X(D)$. $\square$

**Definition (The measure on $[R]$).** The measure $\mu_R$ on $R$ is Haar measure times a cutoff: it integrates functions that are left invariant under $R(E)$ over the quotient $R(E) \backslash R$.

Lean: `New.Grading.besselMeasure`, with the instances `New.Grading.isFiniteMeasure_besselMeasure` and `New.Grading.isMulRightInvariant_haar_besselGroup` (Lib/Weil/Periods/BesselIntegral.lean).

The measure is finite by cocompactness.

**Remark (Formalization).** The measure $\mu_R$ is the measure `quotMeasure` of the library on adelic quotients, for the Haar measure `haar` that Mathlib fixes on the group $R$. Its normalisation is not the Tamagawa measure, and no statement of this chapter needs a normalisation. The integral of a function that is not integrable is $0$ in Lean. The theorems of Section 5 state integrability as a conclusion, so that their identities are identities of true integrals.

### The generic character

Let $\psi$ be the standard additive character of $\mathbb{A}/E$ and let $\jmath$ be the imaginary element of the Weil data. Write $\mathfrak{e}$ for the shift of $Y$.

**Definition (The character $\psi_U$).** For $u \in G$ put

$$\psi_U(u) = \psi\Big(\tfrac{\jmath}{2} \operatorname{tr}(\mathfrak{e}\, u)\Big),$$

with $u$ its matrix in rational coordinates.

Lean: `New.Grading.unipotentChar` (Lib/Weil/Periods/Equivariant.lean).

The trace $\operatorname{tr}(\mathfrak{e} u)$ reads the entries of $u$ from the grade $k + 2$ part to the grade $k$ part, against the factors of the shift. Write $U^{\geq 2}$ for the set of $u$ such that $u - 1$ has degree at least $2$.

**Proposition (Properties of $\psi_U$).**

1. If $u - 1$ and $u' - 1$ have degree at least $2$, then $\psi_U(u u') = \psi_U(u)\psi_U(u')$.
2. $\psi_U(\gamma) = 1$ for every rational point $\gamma \in V.\Gamma$.
3. $\psi_U(\iota_X(a)\, u\, \iota_X(a)^{-1}) = \psi_U(u)$ for $a \in H$ and $u \in G$.

Lean: `New.Grading.unipotentChar_mul`, `New.Grading.unipotentChar_of_mem_Gamma`, `New.Grading.unipotentChar_conj` (Lib/Weil/Periods/Equivariant.lean).

*Proof.* (1) The shift lowers grades by $2$, so $\operatorname{tr}(\mathfrak{e} A)$ depends only on the entries of $A$ of degree exactly $2$. For $u, u'$ in $U^{\geq 2}$ the part of degree $2$ of $u u' - 1$ is the sum of the parts of degree $2$ of $u - 1$ and $u' - 1$, because the product $(u - 1)(u' - 1)$ has degree at least $4$. So the trace is additive, and $\psi$ turns the sum into a product. (2) For $\gamma$ rational the trace is an element of $E$, and $\psi$ is trivial on $E$. (3) The shift kills $X$ and $\iota_X(a)$ is the identity on the string, so $\iota_X(a)$ commutes with $\mathfrak{e}$, and the trace is invariant under conjugation. $\square$

So $\psi_U$ is a character of $U^{\geq 2}(\mathbb{A})$, trivial on rational points and invariant under $H$. If $s$ is odd, every grade is even, so every element of $U$ has $u - 1$ of degree at least $2$ (Lean: `New.Grading.hasDegreeGe_two_of_odd`). Then $U^{\geq 2} = U$, and $\psi_U$ is a character of all of $U(\mathbb{A})$. This is the Bessel case. If $s$ is even, $U^{\geq 2}$ is a proper subgroup, and $\psi_U$ is a character of it only. This is the Fourier-Jacobi case.

### Equivariant functions

**Definition (Equivariant function).** A function $W \colon R \to \mathbb{C}$ is equivariant if

1. $W$ is continuous;
2. $W(\gamma r) = W(r)$ for every $\gamma \in R \cap V.\Gamma$ and $r \in R$;
3. $W(u r) = \psi_U(u) W(r)$ for every $u \in R$ such that $u - 1$ has degree at least $2$, and every $r \in R$.

Lean: `New.Grading.IsEquivariant` (Lib/Weil/Periods/Equivariant.lean).

The first example comes from an automorphic form on the definite group $H$. Let $\varphi$ be an algebraic automorphic form on $H$ of weight $(\kappa, e)$: a function on the finite adelic points of $H$ with values in a representation $\rho$ of the real points of $H$, left invariant under rational points and transforming under a level. Let $t$ be a linear functional on the space of $\rho$. The scalar function $\varphi_t(a) = t(\rho(a_\infty^{-1}) \varphi(a_f))$ on $H$ is automorphic (Lean: `New.algFormCoeff`).

**Definition (The source function).** The source function of $\varphi$ and $t$ is

$$\mathcal{W}_\varphi(r) = \psi_U\big(r\, \iota_X(p(r))^{-1}\big)\, \varphi_t(p(r)), \qquad r \in R,$$

where $p$ is the projection fixed by the source.

Lean: `New.Grading.sourceFn` (Lib/Weil/Periods/Equivariant.lean).

So $\mathcal{W}_\varphi(u\, \iota_X(a)) = \psi_U(u)\varphi_t(a)$ for $u \in U$ and $a \in H$ (Lean: `New.Grading.sourceFn_mul`).

**Theorem (The source function is equivariant).** If $s$ is odd, then $\mathcal{W}_\varphi$ is equivariant.

Lean: `New.Grading.isEquivariant_sourceFn` (Lib/Weil/Periods/Equivariant.lean).

*Proof.* Write $r = u\, \iota_X(a)$. Continuity follows from that of $p$, $\psi_U$ and $\varphi_t$. The key identity is that the factor in $U$ of a product $p' r$ is the factor of $p'$ times the conjugate, by $\iota_X(p(p'))$, of the factor of $r$. Since $s$ is odd, both factors lie in $U^{\geq 2}$, and so does the conjugate. By the proposition on $\psi_U$, the first factor of $\mathcal{W}_\varphi$ is multiplicative. For rational $\gamma$, the first factor at $\gamma$ is $1$, because $\gamma\, \iota_X(p(\gamma))^{-1}$ is rational, and the second factor is invariant because $p(\gamma)$ is rational and $\varphi_t$ is automorphic. For $u \in U^{\geq 2}$ one has $p(u) = 1$, and the identity gives $\mathcal{W}_\varphi(u r) = \psi_U(u)\mathcal{W}_\varphi(r)$. $\square$

**Proposition (Uniqueness).** Let $s$ be odd, and let $W$ be equivariant with $W(\iota_X(a)) = \varphi_t(a)$ for every $a \in H$. Then $W = \mathcal{W}_\varphi$.

Lean: `New.Grading.IsEquivariant.eq_sourceFn` (Lib/Weil/Periods/Equivariant.lean).

*Proof.* Write $r = u\, \iota_X(a)$ with $u \in U$. Since $s$ is odd, $u \in U^{\geq 2}$, so $W(r) = \psi_U(u) W(\iota_X(a)) = \psi_U(u)\varphi_t(a) = \mathcal{W}_\varphi(r)$. $\square$

**Remark (Formalization).** The projection $p$ in the source function is `New.Grading.leviPart`, which is defined as the `choose` of the existence statement [Proposition](/decl/New.Grading.exists_besselGroup_proj/). Any two such projections agree: by (1) and (3), $p(r)$ is determined by $r$ modulo $U$, and by (2) it is then fixed. So the function $\mathcal{W}_\varphi$ does not depend on the choice. For even $s$ the source does not claim that $\mathcal{W}_\varphi$ is equivariant.

### Integrals over the Bessel group

The next result reduces integrals over $[R]$ to $[H]$. It averages over the part of $U$ that moves $X$ into grade $1$. The grades of the string are distinct, so at most one string vector has grade $1$. It exists if and only if $s$ is even.

**Theorem (Integration over $[R]$).** Let $q$ be a finite set with an injective map $v$ into the basis indices of grade $1$, so that $q$ has at most one element. Define $\mathrm{row}(n) \in \mathbb{A}^{q \times X}$ by $\mathrm{row}(n)_{j, a} = c \cdot (n - 1)_{v(j), x_a}$. There is a constant $\kappa \in \mathbb{C}$ with this property. Let $\phi \colon R \to \mathbb{C}$, $f \colon H \times \mathbb{A}^{q \times X} \to \mathbb{C}$ and $M \colon H \to \mathbb{C}$ satisfy:

1. $\phi$ is continuous and left invariant under $R(E)$;
2. $\phi(n\, \iota_X(a)) = f(a, \mathrm{row}(n))$ for $n \in U$ and $a \in H$;
3. for each $a$, the function $f(a, \cdot)$ is continuous and periodic under $E^{q \times X}$, with mean $M(a)$ over $\mathbb{A}^{q \times X} / E^{q \times X}$;
4. $M$ is continuous and left invariant under $H(E)$.

Then $\int_R \phi\, d\mu_R = \kappa \int_{[H]} M$.

Lean: `New.Grading.integral_besselMeasure_eq_of_mean` (Lib/Weil/Periods/BesselIntegral.lean).

*Proof.* Let $\bar M(r) = M(p(r))$. Both $\phi$ and $\bar M$ are continuous and invariant under $R(E)$, so they are integrable for $\mu_R$ by cocompactness. For an adelic vector $b \in \mathbb{A}^{q \times X}$, the Eichler transformation $v \mapsto v + h(u, v)x - h(x, v)(u + \varsigma x)$, with $x$ the string vector of grade $1$ and $u \in X$ built from $b$, gives an element $u_b \in U$. It depends continuously on $b$, and $\mathrm{row}(n u_b) = b + \mathrm{row}(n)$ for $n \in U$, because the row is additive on $U$: the cross term $(n - 1)(u_b - 1)$ has degree at least $2$. Average $\phi - \bar M$ over the right translates by these elements, inside the subgroup $p^{-1}(H(E))$, which is unimodular. By (2) and (3) the average over $b$ is $\int (f(a, b + c) - M(a))\, db = 0$. Since right translation keeps Haar measure, the integral of $\phi - \bar M$ is $0$. The function $\bar M$ factors through $p$, and an integral over $[R]$ of a function of $p(r)$ is a fixed multiple of the integral over $[H]$, by unfolding in stages along $p$. $\square$

**Remark (Formalization).** The theorem does not claim $\kappa \neq 0$. It is the volume of a quotient for the chosen Haar measures, and the source does not compute it.
