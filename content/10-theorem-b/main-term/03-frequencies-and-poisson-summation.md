---
title: Frequencies and Poisson summation
lean:
  - New/Spanning/MainTerm/Frequencies.lean
  - New/Spanning/MainTerm/GlobalSieve.lean
decls:
  - New.denominator
  - New.sum_absNorm_inv_sq_le
  - New.sum_coset_weight_le
  - New.sum_height_inv_cube_le
  - New.Filling.charOnPlaces
  - New.Filling.globalChar
  - New.Filling.frequencyDecay
  - New.Filling.ratPoint
  - New.Filling.sum_frequencies_le
  - New.Filling.wave_two_pi_I_mul
  - New.Filling.stdAddChar_div_deltaE
  - New.Filling.extendToAdeles
  - New.Filling.sum_ratPoint_le_mul_add_integral_of_fourier_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Frequencies and Poisson summation

The sieve meets two kinds of sums. The first kind is a sum over the frequencies $\xi \neq 0$ of the decay $\beta(\xi)$. The second kind is a sum over lattice points, which one-sided Poisson summation turns into an integral plus the sum of the first kind. This section proves both bounds. Here $E$ is a totally complex field with $f$ infinite places, $\Phi_v$ is the chosen embedding at $v$, and $[E : \mathbb Q] = 2f$.

### Heights of frequencies

**Definition (Denominator).** For $\nu \in E$, the *denominator* $\operatorname{den}\nu$ is the ideal of the $a \in \mathcal O_E$ with $a\nu$ integral.

Lean: `New.denominator` (New/Spanning/MainTerm/Frequencies.lean).

The ideal is not $0$: if $\nu = a/b$ with $a, b \in \mathcal O_E$, $b \neq 0$, then $b \in \operatorname{den}\nu$.

**Lemma (Sum over ideals).** For every finite set $s$ of ideals of $\mathcal O_E$, $\sum_{\mathfrak b \in s} N(\mathfrak b)^{-2} \leq e^{2[E:\mathbb Q]}$.

Lean: `New.sum_absNorm_inv_sq_le` (New/Spanning/MainTerm/Frequencies.lean).

*Proof.* The series $\sum_{\mathfrak b} N(\mathfrak b)^{-2}$ converges to $\zeta_E(2)$, the Euler product at $s = 2$ with all coefficients $1$. Volume 3 bounds the logarithm of an Euler product: $|\log|\zeta_E(2)|| \leq 2[E : \mathbb Q] \cdot 2^{2-2}$ (`New.eulerProd_ne_zero_and_abs_log_norm_le`, [class field theory on finite ideles](/chapter/class-field-theory/)). A finite partial sum of a series of nonnegative terms is at most its sum, and $\zeta_E(2) \leq |\zeta_E(2)| \leq e^{2[E:\mathbb Q]}$. $\square$

**Lemma (One coset).** Let $X \subset E$ be finite, and let any two elements of $X$ differ by an algebraic integer. Then
$$\sum_{\nu \in X} \prod_v \max(1, |\Phi_v \nu|)^{-6} \leq (64 \cdot 38)^f.$$

Lean: `New.sum_coset_weight_le` (New/Spanning/MainTerm/Frequencies.lean).

*Proof.* Cut $\mathbb C$ into the squares $Q_m = [m_1/2, (m_1+1)/2) \times [m_2/2, (m_2+1)/2)$ for $m \in \mathbb Z^2$, with corners $z_m = m_1/2 + i m_2/2$. Each $z$ lies in one square $Q_{m(z)}$, and $|z_{m(z)} - z| < 1$. Hence $\max(1, |z_{m(z)}|) \leq 2\max(1, |z|)$, and
$$\max(1, |z|)^{-6} \leq 64 \max(1, |z_{m(z)}|)^{-6}.$$
Distinct corners have distance at least $1/2$. The packing bound for separated points of [the notation chapter](/chapter/notation/) (Lib/General/Analysis/PackingAndSobolev.lean) gives $\sum_m \max(1, |z_m|)^{-6} \leq (1 + 2 \cdot 1/(1/2))^2 \cdot 3/2 = 37.5 \leq 38$.

Send $\nu \in X$ to its cells $(m(\Phi_v\nu))_v$. This map is injective on $X$. Indeed, if $\nu, \nu'$ have the same cells, then $|\Phi_v(\nu - \nu')| < 1$ for every $v$. The algebraic integer $\nu - \nu'$ has norm $\prod_v |\Phi_v(\nu - \nu')|^2 < 1$, so it is $0$. Hence the sum is at most a sum over distinct tuples of cells, which is at most the product over $v$ of the sums over all cells:
$$\sum_{\nu \in X} \prod_v \max(1, |\Phi_v\nu|)^{-6} \leq \prod_v \sum_m 64 \max(1, |z_m|)^{-6} \leq (64 \cdot 38)^f. \qquad \square$$

**Theorem (Sum over frequencies).** For every finite set $X \subset E$,
$$\sum_{\nu \in X} \prod_v \max(1, |\Phi_v\nu|)^{-6} \cdot N(\operatorname{den}\nu)^{-3} \leq (64 \cdot 38 \cdot e^4)^f.$$

Lean: `New.sum_height_inv_cube_le` (New/Spanning/MainTerm/Frequencies.lean).

*Proof.* Group the $\nu$ by their denominator $\mathfrak b$. The $\nu$ with $\operatorname{den}\nu \supseteq \mathfrak b$ lie in at most $N(\mathfrak b)$ cosets of $\mathcal O_E$. To see this, choose $a \neq 0$ in $\mathfrak b$ and write $(a) = \mathfrak b\mathfrak c$. Then $a\nu \in \mathfrak c$, and its class in $\mathfrak c/\mathfrak b\mathfrak c$, a group of order $N(\mathfrak b)$, is a label. Two numbers with the same label have $a(\nu - \nu') \in (a)$, so $\nu - \nu' \in \mathcal O_E$. By the lemma on one coset, the $\nu \in X$ with $\operatorname{den}\nu = \mathfrak b$ contribute at most $N(\mathfrak b)(64 \cdot 38)^f N(\mathfrak b)^{-3}$. Sum over the denominators with the lemma on ideals:
$$\sum_{\nu} \ldots \leq (64 \cdot 38)^f \sum_{\mathfrak b} N(\mathfrak b)^{-2} \leq (64 \cdot 38)^f e^{2 \cdot 2f}. \qquad \square$$

In the Lean statement, $\max(1, |\Phi_v\nu|)^{-6}$ is the cube of $[\nu]_v^{-1}$ with $[\nu]_v = \max(1, |\nu|_v)^2$, the normalised absolute value at a complex place. The constant is $64 \cdot 38 \cdot e^4 < 64 \cdot 38 \cdot 81 < 1000^3 \leq b^3$, since $e < 3$ and $b \geq 1000$.

### The characters and the decay at $T$

Let $T$ be a finite set of finite places, stable under complex conjugation. Write $\mathcal L_T = \prod_{w \in T} E_w$ for the product of the completions, with integers $\mathcal O$. An element of $E$ or of the finite adeles is *integral off $T$* if it is integral at every finite place outside $T$. Let $\varpi$ be the generator of the different of $E$ from the data, and $\psi_f$ the standard character of the finite adeles ([adeles and Hermitian spaces](/chapter/adeles-hermitian-spaces/)).

**Definition (Characters).** The character $\psi_T$ of $\mathcal L_T$ is $x \mapsto \psi_f(-x/\varpi)$, where $x$ is read as a finite adele by extension by zero. The global character on $\mathbb C^f \times \mathcal L_T$ is $\chi(x) = \prod_v \operatorname{wave}(x_v) \cdot \psi_T(x_T)$.

Lean: `New.Filling.charOnPlaces`, `New.Filling.globalChar` (New/Spanning/MainTerm/GlobalSieve.lean).

At a finite adele $x$ integral off $T$, $\psi_T$ at the components of $x$ at $T$ is $\psi_f(-x/\varpi)$: the difference of $x$ and its extension by zero is integral, and $\psi_f(-\cdot/\varpi)$ is trivial on the integral adeles, since $\varpi^{-1}\hat{\mathcal O}$ is the inverse different.

**Definition (Decay at $T$ and rational points).** For $\xi \in \mathcal L_T$,
$$\beta_T(\xi) = \sqrt{[\mathcal O : \xi\mathcal O]}^{\,k - n^7} \big/ [\mathcal O : \mathcal O \cap \xi^{-1}\mathcal O]^3 \cdot b^{n^9 f}.$$
For scales $l \in \mathbb C^f$ and $t \in E$, the rational point is $\operatorname{pt}_l(t) = ((l_v \Phi_v t)_v, t) \in \mathbb C^f \times \mathcal L_T$.

Lean: `New.Filling.frequencyDecay`, `New.Filling.ratPoint` (New/Spanning/MainTerm/GlobalSieve.lean).

The indices are the generalised index and the denominator index of [congruence subgroups](/chapter/congruence-subgroups/). They are real numbers, and $\xi$ a unit makes the generalised index positive. The exponent $k - n^7$ is a difference of natural numbers. It is the true difference, since $1000 n^9 \leq k$ for admissible data.

**Theorem (Sum of the decays).** Let $1 \leq B$, let $c, x$ be families over the infinite places with $|c_v|^{-1} \leq |x_v| \leq B$, and let $X \subset E$ be a finite set of nonzero elements integral off $T$. Then
$$\sum_{y \in X} \prod_v \ell_k(|c_v\Phi_v y|^{-1}) \cdot \frac{\sqrt{[\mathcal O : y\mathcal O]}^{\,k}}{[\mathcal O : \mathcal O \cap y^{-1}\mathcal O]^3} \leq \prod_v |x_v|^k (bB^2)^3.$$

Lean: `New.Filling.sum_frequencies_le` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* Fix $y$ and put $r_v = |c_v\Phi_v y|^{-1}$. Then $\ell_k(r_v)|\Phi_v y|^k = |c_v|^{-k}\min(1, r_v)^6 \leq |x_v|^k \min(1, r_v)^6$. If $|\Phi_v y| \geq 1$, then $\min(1, r_v) \leq r_v \leq B/|\Phi_v y|$. If $|\Phi_v y| \leq 1$, then $\min(1, r_v) \leq 1 \leq B$. In both cases $\ell_k(r_v)|\Phi_v y|^k \leq |x_v|^k B^6 \max(1, |\Phi_v y|)^{-6}$. Next, $y$ is integral off $T$, so $[\mathcal O : y\mathcal O]$ divides the norm of the part of $y$ at $T$, and $\sqrt{[\mathcal O : y\mathcal O]} \leq \prod_v |\Phi_v y|$. The denominator of $y$ is the preimage of the local denominator, so $N(\operatorname{den} y) \leq [\mathcal O : \mathcal O \cap y^{-1}\mathcal O]$. Together, the term of $y$ is at most $\prod_v |x_v|^k B^6$ times $\prod_v \max(1, |\Phi_v y|)^{-6}\, N(\operatorname{den} y)^{-3}$. Sum over $y$ with the theorem on frequencies, and use $64 \cdot 38 \cdot e^4 \leq b^3$. $\square$

### One-sided Poisson summation

**Lemma (Characters at infinity).** For $w \in \mathbb C$, $\operatorname{wave}(2\pi i w) = e^{2\pi i \cdot 2\operatorname{Re} w}$. For $y \in E$ and an adele $z$, both integral off $T$,
$$\psi(-z\, y/\varpi) = \prod_v \operatorname{wave}\Bigl(\frac{2\pi i}{\Phi_v\varpi}\Phi_v y \cdot z_v\Bigr) \cdot \psi_T(y\, z_T),$$
where $\psi$ is the standard character of the adeles.

Lean: `New.Filling.wave_two_pi_I_mul`, `New.Filling.stdAddChar_div_deltaE` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* $\operatorname{wave}(2\pi i w) = \exp(2\pi i w - \overline{2\pi i w}) = \exp(2\pi i(w + \bar w))$. The standard character at an infinite place is $x \mapsto e^{-2\pi i \cdot 2\operatorname{Re} x}$, since the trace from $\mathbb C$ to $\mathbb R$ is $2\operatorname{Re}$. With $w_v = \Phi_v y/\Phi_v\varpi \cdot z_v$, the infinite part of $\psi(-zy/\varpi)$ is $\prod_v e^{2\pi i \cdot 2\operatorname{Re} w_v}$, which is the product of the waves by the first identity. The finite part is $\psi_f(-yz_f/\varpi)$, and $yz_f$ is integral off $T$, so it is $\psi_T(yz_T)$ by the remark after the definition of $\psi_T$. $\square$

The main tool is the one-sided Poisson summation on the adeles of Volume 4: if $F \geq 0$ on $\mathbb A_E$ is integrable and lower semicontinuous at the points of a finite set of rational points, and $S$ bounds $\sum_{\xi \in Y}|\hat F(\xi)|$ for every finite $Y \subset E$, then the sum of $F$ over the points is at most $S$ (`New.IsDualFamily.sum_le_of_fourier`, [adeles and Hermitian spaces](/chapter/adeles-hermitian-spaces/)). The Haar measure on $\mathbb A_E$ there gives $\mathbb A_E/E$ the volume $1$.

**Definition (Extension to the adeles).** For scales $r > 0$ and $F$ on $\mathbb C^f \times \mathcal L_T$, the function $G$ on $\mathbb A_E$ is $G(z) = F((r_v z_v)_v, z_T)$ if $z_f$ is integral off $T$, and $G(z) = 0$ otherwise.

Lean: `New.Filling.extendToAdeles` (New/Spanning/MainTerm/GlobalSieve.lean).

**Theorem (One-sided Poisson summation at $T$).** Let $r_v > 0$, and let $V$ be a finite set of units of $E$ integral off $T$. Let $F \geq 0$ be integrable on $\mathbb C^f \times \mathcal L_T$ and lower semicontinuous at the points $\operatorname{pt}_r(t)$, $t \in V$. Let $M \geq 0$, and let $|\int \chi(\xi x) F(x)\, dx| \leq \beta(\xi) M$ for every unit $\xi$. Let $\varepsilon$ bound $\sum_{y \in X}\beta(\operatorname{pt}_{s}(y))$ for every finite set $X$ of nonzero elements of $E$ integral off $T$, with the scales $s_v = 2\pi i/(\Phi_v\varpi \cdot r_v)$. Then
$$\sum_{t \in V} F(\operatorname{pt}_r(t)) \leq \frac{\operatorname{vol}\hat{\mathcal O}}{\prod_v r_v^2}\Bigl(\varepsilon M + \int F\Bigr).$$

Lean: `New.Filling.sum_ratPoint_le_mul_add_integral_of_fourier_le` (New/Spanning/MainTerm/GlobalSieve.lean).

*Proof.* Let $G$ be the extension of $F$ and $c = \operatorname{vol}\hat{\mathcal O}/\prod_v r_v^2$.

*The measure.* The map $z \mapsto ((r_v z_v)_v, z_T)$ sends the Haar measure on $\mathbb C^f \times \{z_f \text{ integral off } T\}$ to $c$ times the measure on $\mathbb C^f \times \mathcal L_T$. The scaling has determinant $\prod_v r_v^2$ over $\mathbb R$. The projection of the adeles integral off $T$ to $\mathcal L_T$ sends the measure to $\operatorname{vol}\hat{\mathcal O}$ times the measure of $\mathcal L_T$, because the factor off $T$ is the integral adeles off $T$. Hence $G$ is integrable, and $\int G\, \phi = c\int F\, \phi'$ for the matching functions.

*The transform.* Let $\hat G(y/\varpi) = \int \psi(-zy/\varpi) G(z)\, dz$ for $y \in E$. The function $G$ is invariant under the integral finite adeles that vanish at $T$. If $y$ is not integral off $T$, then $\psi(-\cdot\,y/\varpi)$ is not trivial on that group, and averaging over it gives $\hat G(y/\varpi) = 0$. If $y$ is integral off $T$, the lemma on characters and the change of measure give $\hat G(y/\varpi) = c\int \chi(\operatorname{pt}_s(y)\, x) F(x)\, dx$. For $y = 0$ this is $c\int F$, since $F$ is real and $\geq 0$. For $y \neq 0$ the point $\operatorname{pt}_s(y)$ is a unit, so the modulus is at most $c\beta(\operatorname{pt}_s(y))M$.

*The bound.* Let $Y \subset E$ be finite and $X$ the set of nonzero $y \in Y$ integral off $T$. Then $\sum_{y \in Y}|\hat G(y/\varpi)| \leq c\int F + c\sum_{y \in X}\beta(\operatorname{pt}_s(y))M \leq c(\varepsilon M + \int F)$. The map $y \mapsto y/\varpi$ is a bijection of $E$, so the same bound holds for $\sum_{\xi \in Y}|\hat G(\xi)|$.

*Poisson.* For $t \in V$, $G(t) = F(\operatorname{pt}_r(t))$, since $t$ is integral off $T$. The set of adeles integral off $T$ is open, so $G$ agrees with $F$ composed with a continuous map near $t$ and is lower semicontinuous at $t$. One-sided Poisson summation on $\mathbb A_E$ gives $\sum_{t \in V} G(t) \leq c(\varepsilon M + \int F)$. $\square$

**Remark (Formalization).** The hypotheses on $\varepsilon$ and on the bound $S$ of one-sided Poisson summation are bounds for all finite partial sums. The source never forms the infinite sum over the frequencies, so no junk value of a divergent `tsum` enters. The sign convention is absorbed in $\psi_T(x) = \psi_f(-x/\varpi)$: by the lemma on characters, the adelic transform at $y/\varpi$ is $c$ times the integral against $\chi(\operatorname{pt}_s(y)\, x)$ with no further sign. For $y \neq 0$ the point $\operatorname{pt}_s(y)$ is a unit, because each $\Phi_v y \neq 0$ and $y$ is a unit in each field $E_w$.
