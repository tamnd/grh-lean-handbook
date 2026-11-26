---
title: Integrals over groups and kernels
lean:
  - Lib/General/Measure/HaarNormalisation.lean
  - Lib/General/Measure/IntegralOperators.lean
  - Lib/General/Measure/IdempotentKernel.lean
  - Lib/General/Groups/BesselGroups.lean
decls:
  - New.addHaar_eq_of_integral_eq_one
  - New.setIntegral_char
  - New.setIntegral_eq_finsum
  - New.HasGaussianIntegral
  - New.lintegral_inv_add_rpow
  - New.lintegral_rpow_neg_le_of_measure_sublevel_le
  - New.IsL2Contraction
  - New.IsL2Contraction.pi
  - New.integrable_of_isCocompact
  - New.IsIdempotentKernel
  - New.IsIdempotentKernel.convolution_self
  - New.wave
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Integrals over groups and kernels

This section collects the integration lemmas of the chapter. Each one is a standard computation. They fall into four groups. The first group fixes a Haar measure by one integral and computes integrals over compact open subgroups. The second group normalises a volume by a Gaussian integral and integrates negative powers. The third group bounds integral operators on $L^2$. The fourth group is the idempotent kernels on a group and the unitary function $\mathrm{wave}$.

### Normalisation and orthogonality

A Haar measure is unique up to a positive constant. So one integral fixes it.

**Lemma.** Let $G$ be a locally compact second countable abelian group, and let $\mu$ and $\nu$ be Haar measures on $G$. If a real function $f$ has $\int f \, d\mu = 1$ and $\int f \, d\nu = 1$, then $\mu = \nu$.

Lean: `New.addHaar_eq_of_integral_eq_one` (Lib/General/Measure/HaarNormalisation.lean).

*Proof.* There is $c \geq 0$ with $\mu = c\nu$. Then $1 = \int f \, d\mu = c \int f \, d\nu = c$. $\square$

The lemma asks nothing of $f$. If $f$ is not integrable, its integral is $0$ by the convention of the Bochner integral, and the hypothesis fails. So the hypothesis contains the integrability.

The next result is the orthogonality of characters on a subgroup. It is the reason why exponential sums over compact open subgroups are either a volume or zero.

**Proposition.** Let $V$ be a topological abelian group with a translation invariant Borel measure $\nu$. Let $M \leq V$ be an open subgroup and let $\chi : V \to \mathbb{C}$ satisfy $\chi(x + y) = \chi(x)\chi(y)$. Then
$$\int_M \chi \, d\nu = \begin{cases} \nu(M) & \text{if } \chi = 1 \text{ on } M, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.setIntegral_char` (Lib/General/Measure/HaarNormalisation.lean).

*Proof.* If $\chi = 1$ on $M$, the integral is $\nu(M)$. Otherwise choose $m \in M$ with $\chi(m) \neq 1$. Translation by $m$ preserves $M$ and $\nu$, so it does not change the integral. It also multiplies the integrand by $\chi(m)$. So the integral $I$ satisfies $\chi(m) I = I$, and $I = 0$. $\square$

**Remark (Formalization).** In the first case the source gives the value as `ν.real M`, the measure of $M$ as a real number. This number is $0$ if $\nu(M) = \infty$. In that case the integrand $1$ is not integrable, and the Bochner integral is also $0$ by convention. So the statement is true in this case, but it carries no information. In the uses, $M$ is compact and its measure is finite. The proposition asks for no continuity or boundedness of $\chi$. In the second case, a non-integrable $\chi$ also gives the value $0$ by convention.

When the integrand is constant on the cosets of a smaller subgroup, the integral is a finite sum.

**Proposition.** Let $V$ be a Hausdorff topological abelian group with a translation invariant measure $\nu$ that is finite on compact sets. Let $M \leq V$ be compact and let $L \leq V$ be open. Let $F$ be a function on $V$ with $F(y) = F(x)$ for all $x, y \in M$ with $y - x \in L$. Then
$$\int_M F \, d\nu = \nu(L \cap M) \sum_{q \in M/(L \cap M)} F(x_q),$$
where $x_q \in M$ is any representative of the coset $q$.

Lean: `New.setIntegral_eq_finsum` (Lib/General/Measure/HaarNormalisation.lean).

*Proof.* The group $L \cap M$ is open in the compact group $M$, so it has finite index. The set $M$ is the disjoint union of the cosets $x_q + (L \cap M)$. On each coset $F$ is constant, and each coset has measure $\nu(L \cap M)$. $\square$

**Remark (Formalization).** The representative $x_q$ is `q.out`, a representative that Lean picks by choice. By the hypothesis on $F$, the value $F(x_q)$ does not depend on the pick. So the sum is determined by $F$. The sum is a `finsum`, which is $0$ if the index set is infinite. Here the index set is finite, as the proof shows.

### Gaussian normalisation

To fix a volume without a basis, the source uses a Gaussian integral.

**Definition (Gaussian normalisation).** Let $V$ be a measure space, let $q : V \to \mathbb{R}$ and let $a \in \mathbb{R}$. The volume of $V$ has Gaussian integral $(a, q)$ if for every $t > 0$
$$\int_V e^{-t q(x)} \, dx = \left(\frac{\pi}{t}\right)^a.$$

Lean: `New.HasGaussianIntegral` (Lib/General/Measure/HaarNormalisation.lean).

**Example.** Lebesgue measure on $\mathbb{R}$ has Gaussian integral $(\tfrac12, x^2)$. Lebesgue measure on $\mathbb{C}$ has Gaussian integral $(1, |z|^2)$. If $V$ and $W$ have Gaussian integrals $(a, q)$ and $(b, q')$, then $V \times W$ with the product measure has $(a + b, q + q')$. The power $V^\iota$ for a finite set $\iota$ has $(a |\iota|, \sum_i q(x_i))$. By Fubini each of these reduces to $\int_{\mathbb{R}} e^{-t x^2} dx = (\pi/t)^{1/2}$. The source has the four statements as instances, and the last one is [the power case](/decl/New.HasGaussianIntegral.pi/).

**Remark (Formalization).** The integral in the definition is a Bochner integral, which is $0$ for a non-integrable function. The right side $(\pi/t)^a$ is positive. So the definition forces $e^{-tq}$ to be integrable for every $t > 0$, and no separate hypothesis is needed. The source makes the definition a class with $a$ and $q$ as output parameters. So Lean finds the exponent and the quadratic form from the type $V$ alone. The instance for products is global. It adds the forms and the exponents, and it applies to every product type with a volume.

The Gaussian normalisation computes integrals of negative powers.

**Theorem.** Let the volume of $V$ be $\sigma$-finite with Gaussian integral $(a, q)$, and let $q \geq 0$ be measurable. Let $c > 0$, $s > 0$ and $a < s$. Then
$$\int_V (c + q(x))^{-s} \, dx = \frac{\pi^a \, \Gamma(s - a)}{\Gamma(s)} \, c^{a - s}.$$

Lean: `New.lintegral_inv_add_rpow` (Lib/General/Measure/HaarNormalisation.lean). The integral is a lower Lebesgue integral.

*Proof.* Write $(c + q)^{-s} = \Gamma(s)^{-1} \int_0^\infty t^{s-1} e^{-(c+q)t} \, dt$. Exchange the integrals by Tonelli. The inner integral is $e^{-ct} (\pi/t)^a$. The outer integral is $\pi^a \int_0^\infty t^{s-a-1} e^{-ct} \, dt = \pi^a c^{a-s} \Gamma(s - a)$. $\square$

For $V = \mathbb{R}^n$ with $q = |x|^2$ and $c = 1$, the theorem gives $\int (1 + |x|^2)^{-s} dx = \pi^{n/2} \Gamma(s - n/2) / \Gamma(s)$ for $s > n/2$.

The next lemma bounds an integral of a negative power by the volumes of sublevel sets. It is the layer cake representation (Lieb and Loss, *Analysis*, Theorem 1.13) with a bound on each layer.

**Lemma.** Let $\nu$ be a measure on $S$, let $u : S \to \mathbb{R}$ be measurable with $u \geq 1$, and let $K \geq 0$, $V \in [0, \infty]$, $e \in \mathbb{R}$ and $d \in \mathbb{N}$. Assume that
$$\nu\{u \leq R\} \leq (K R^e)^d \, V \quad \text{for all } R \geq 1.$$
Let $A$ and $c$ satisfy $ed < A$ and $A \leq c(A - ed)$. Then $\int_S u^{-A} \, d\nu \leq K^d c \, V$.

Lean: `New.lintegral_rpow_neg_le_of_measure_sublevel_le` (Lib/General/Measure/IntegralOperators.lean).

*Proof.* By the layer cake formula, $\int u^{-A} d\nu = A \int_0^\infty \nu\{u^{-1} \geq t\} \, t^{A-1} \, dt$. For $t > 1$ the set is empty. For $t \leq 1$ it is $\{u \leq t^{-1}\}$, of measure at most $K^d t^{-ed} V$. So the integral is at most $A K^d V \int_0^1 t^{A - ed - 1} dt = K^d V \cdot A/(A - ed) \leq K^d c V$. $\square$

The hypothesis $A \leq c(A - ed)$ is a way to state the constant $A/(A - ed)$ without a division. The source uses the lemma in the unfolding computations.

### Integral operators on $L^2$

**Definition ($L^2$ contraction).** Let $m$ be a measure on $X$, let $\mu$ and $n$ be measures on $Y$, and let $(k_i)_{i \in I}$ be a finite family of kernels $k_i : X \times Y \to \mathbb{C}$. The family is an $L^2$ contraction if for every bounded measurable $\varphi : Y \to \mathbb{C}$
$$\int_X \sum_{i \in I} \left| \int_Y \varphi(y) k_i(x, y) \, d\mu(y) \right|^2 dm(x) \leq \int_Y |\varphi|^2 \, dn.$$

Lean: `New.IsL2Contraction` (Lib/General/Measure/IntegralOperators.lean).

The definition tests only bounded $\varphi$. The definition has two measures on $Y$. The kernel is integrated against $\mu$, and the norm of $\varphi$ is taken for $n$.

**Proposition.** Let $(k_v)_{v \in \iota}$ be a finite family of $L^2$ contractions on common spaces $X$ and $Y$, for $\sigma$-finite measures $m_v$, $\mu_v$ and $n_v$. Assume that each kernel is measurable and integrable in $y$. Then the products $\prod_v k_{v, i_v}(x_v, y_v)$, indexed by $(i_v) \in \prod_v I_v$, form an $L^2$ contraction for the product measures on $X^\iota$ and $Y^\iota$.

Lean: `New.IsL2Contraction.pi` (Lib/General/Measure/IntegralOperators.lean). The case of two factors is `New.IsL2Contraction.prod`.

*Proof.* For two factors, apply the bound for the first kernel in the first variable with the second variable fixed, and then the bound for the second kernel. Fubini justifies each step. For $\iota$ use induction on the size. $\square$

The proposition is the reason the definition allows a family: a tensor product of operators on a product of places is again in the class.

The last lemma of this group says that periodic continuous functions are integrable. A subgroup $\Gamma \leq G$ is cocompact if some compact set meets every orbit $\Gamma g$.

**Lemma.** Let $\Gamma \leq G$ be cocompact and let $\mu$ be a finite measure on $G$. Let $F : G \to \mathbb{C}$ be continuous with $F(\gamma g) = F(g)$ for $\gamma \in \Gamma$. Then $F$ is $\mu$-integrable.

Lean: `New.integrable_of_isCocompact` (Lib/General/Measure/IntegralOperators.lean). The product of two cocompact subgroups is cocompact by `New.isCocompact_prod`.

*Proof.* Every value of $F$ is taken on the compact set, where $|F|$ is bounded. A bounded measurable function is integrable for a finite measure. $\square$

### Idempotent kernels

Let $G$ be a group with a measure, written $dz$. For functions $f$ and $h$ on $G$, the convolution is $(f * h)(y) = \int f(z) h(z^{-1} y) \, dz$.

**Definition (Idempotent kernel).** A function $e : G \to \mathbb{C}$ is an idempotent kernel if $e$ is continuous and integrable, $e(g^{-1}) = \overline{e(g)}$ for all $g$, $e(1) \neq 0$, and
$$\int_G e(z) \, e((zx)^{-1} y) \, dz = \frac{e(x^{-1})}{e(1)} \, e(y) \quad \text{for all } x, y \in G.$$

Lean: `New.IsIdempotentKernel` (Lib/General/Measure/IdempotentKernel.lean).

For a measure that is invariant under right translation, the last condition says that $e * \delta_x * e = (e(x^{-1})/e(1)) \, e$, where $\delta_x$ is the point mass at $x$. So the convolution algebra $e * \mathbb{C}[G] * e$ is spanned by $e$.

**Lemma.** An idempotent kernel satisfies $e * e = e$.

Lean: `New.IsIdempotentKernel.convolution_self` (Lib/General/Measure/IdempotentKernel.lean).

*Proof.* Take $x = 1$ in the definition. $\square$

**Example.** Let $G$ be compact with Haar measure of total mass $1$, and let $\chi : G \to \mathbb{C}^\times$ be a continuous unitary character. Then $\chi(g^{-1}) = \overline{\chi(g)}$ and
$$\int_G \chi(z) \chi(x^{-1} z^{-1} y) \, dz = \chi(x^{-1}) \chi(y).$$
So $\chi$ is an idempotent kernel. The character of an irreducible representation of dimension $d > 1$, scaled by $d$, satisfies $e * e = e$ but not the last condition: the convolution $e * \delta_x * e$ is $d\,\chi(x^{-1} \cdot)$, which is not a multiple of $e$ in general. So the definition is stronger than idempotence.

**Remark (Formalization).** The definition is a structure with five fields. It is not a property that the file derives from other facts. A user who wants an idempotent kernel must supply the five fields for a specific $e$. The file also proves the Fubini forms that such proofs need, for example `MeasureTheory.MeasurePreserving.integral_integral_comp` and `New.integral_conv`. The measure in the definition is the default measure `volume` of the type $G$. The source does not ask it to be a Haar measure, but the proofs that construct kernels use Haar measures.

### The function wave

At the complex places, some formulas of the source use a unitary function in place of an additive character.

**Definition (Wave).** For $c \in \mathbb{C}$, let $\mathrm{wave}(c) = \exp(c - \bar c) = \exp(2i \operatorname{Im} c)$.

Lean: `New.wave` (Lib/General/Groups/BesselGroups.lean). The identity $|\mathrm{wave}(c)| = 1$ is `New.norm_wave`.

The map $c \mapsto \mathrm{wave}(c)$ is a continuous homomorphism from $(\mathbb{C}, +)$ to the circle. It is trivial on $\mathbb{R}$. At $c = 2\pi i w$ it is $\exp(2\pi i \cdot 2 \operatorname{Re} w)$, which is the character $w \mapsto e^{2\pi i \operatorname{Tr}_{\mathbb{C}/\mathbb{R}}(w)}$ of $\mathbb{C}$.

**Remark (Formalization).** The identity at $c = 2\pi i w$ is `New.Filling.wave_two_pi_I_mul` (New/Spanning/MainTerm/GlobalSieve.lean:233). So $\mathrm{wave}$ is a rescaling of the additive character of the adeles at the infinite places, and not a different character. The register of findings asks this question as Q-68 ([open questions](/chapter/register-of-findings/)) and lists it as open. The lemma above answers it.
