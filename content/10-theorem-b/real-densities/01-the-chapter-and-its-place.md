---
title: The chapter and its place
lean:
  - New/Spanning/Frames/RealPlaceGauge.lean
  - New/Spanning/Frames/RealShells.lean
  - New/Spanning/Frames/RealBandLimits.lean
decls:
  - New.Floors.exists_hasLocalBounds_of_isCutBessel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter belongs to the bounds layer of [the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof) of the proof of Theorem B. It proves the local bounds at one real place. The input is a cut Bessel function $F$ of a Bessel function $W$ on the group $G_1$ of the real place, with the sizes of the real place. The output is a family of forms $J_0, J_1, \dots, J_{\varrho + 1}$ on pairs of lists of nonzero complex numbers, with the bounds that the sieve of [the main term](/chapter/main-term/) reads. [The chapter on Bessel functions at a real place](/chapter/bessel-real-place/) uses the result when it builds the Bessel systems of the data. The chapter is the real half of the local densities. [The chapter on densities at the finite places](/chapter/finite-densities/) is the other half.

The chapter is the place where the general machine of [frames, depth and gains](/chapter/local-frames/) meets the real numbers. That machine works over a general place: a ring $A$ with a measure, a character $\psi$, a modulus and a constant. Its main results take a place datum and a gauge as hypotheses. This chapter builds both at the place $\mathbb C$ and checks their axioms. It then integrates the local gains over the group, shell by shell, and descends from one floor to the next.

### A model case

The central estimate of the chapter is of the following kind. Let $s \geq 0$, let $R > 0$, and consider the integral of $(36/|u|^2)^s$ over the ball $|u|^2 \leq R$ in $\mathbb C^{s + 1}$. The function has a pole at $0$ of order $2s$, and the real dimension is $2s + 2$. So the integral converges. In polar coordinates with $t = |u|^2$, Lebesgue measure on $\mathbb C^{s+1}$ is $\pi^{s+1} t^s/s!\, dt$ times the normalised measure on the sphere. Hence

$$\int_{|u|^2 \leq R} \Bigl(\frac{36}{|u|^2}\Bigr)^s\, du = \int_0^R \Bigl(\frac{36}{t}\Bigr)^s \frac{\pi^{s+1} t^s}{s!}\, dt = \frac{(36\pi)^s\, \pi}{s!}\, R.$$

The factor $(36\pi)^s/s!$ is a term of the series of $e^{36\pi}$, so the integral is at most $\pi e^{36\pi} R$ for every $s$. The bound is linear in $R$ and does not grow with $s$. The source proves the bound $4 \cdot 3^{144} R$ for the same integral, written with the density $\pi^{s+1} t^s/s!$ on $t > 0$ ([Section 3](/chapter/real-densities/#the-gauge-at-the-complex-place)).

The number $36/|u|^2$ comes from a disc. If the products $\langle u, w \rangle$ of $u$ with a set $W$ of short vectors cover a disc of radius $|u|/2$ about $0$, then the inverse area of the set of products is at most $4/(\pi |u|^2) \leq 36/|u|^2$. The general machine needs a function $\varphi$ that bounds such inverse areas and whose power $\varphi^s$ has a controlled integral. The model computation is the reason that such a $\varphi$ exists at $\mathbb C$. The exponent $s$ is the volume exponent of the place datum, and the source makes it large: $s > 10^9 n^3$. A large exponent turns the inverse areas into large gains.

### The setting

The chapter works with one shape $\mathfrak s$ and the following objects. [The data and their sizes](/chapter/data-and-sizes/) fix the sizes, and [the conventions of this volume](/chapter/theorem-b-plan/#conventions-that-change-the-meaning) state the sizes at a real place.

1. The group $G_1$ is the unitary group of the hermitian form on $\mathbb C^r$ with basis $e_a$, $x_i$ ($i \in \kappa$), $z$, $e^*_a$. The $e_a, e^*_a$ form $\varrho$ hyperbolic pairs, the $x_i$ are orthonormal, and $h(z, z) = -1$. Write $n = \varrho + 1$, $k = |\kappa|$ and $r = 2\varrho + k + 1$.
2. The frame is $(e_0, \dots, e_{\varrho - 1}, z)$. For $x \in G_1$ the matrix $Z(x)$ (Lean: `New.realFrameGram`) has the entries $h(f_a, x f_b)$ for the frame vectors $f_a$. The index of $z$ is called `top`.
3. The pair $(e_a, e^*_a)$ has floor $a$, $z$ has floor $\varrho$, and the $x_i$ have floor $\varrho + 1$. The group $\mathsf U$ (Lean: `besselU`) is the unipotent group of the frame. Integrals over $\mathsf U \backslash G_1$ use the measure `New.besselQuotMeasure`.
4. The sizes at a real place are a box radius $\rho$, an exponent $s$ and a base $b$ with $\rho = b^{6n+2} \geq 8r$, $k = s + 3n + 6 \geq n^7$, $s > 10^9 n^3$, $\varrho \geq 10^8$ and $b \geq 2$ (Lean: `New.Floors.RealPlaceSizes`).
5. A finite set $I$ indexes the values: $F$ and $W$ are continuous maps $G_1 \to \mathbb C^I$. A homomorphism `rep` from $U(\kappa)$ to the unitary group of $\mathbb C^I$ is the type of $W$.
6. The function $F$ is a *cut Bessel function* of $W$ ([Section 5](/chapter/real-densities/#cut-bessel-functions-over-shells)): $F$ and $W$ form a cut pair with base $b$ and degree $f$, in the sense of [the cut pair](/chapter/bessel-real-place/#decay-and-the-cut), the sizes at a real place hold, and `rep` is irreducible.
7. The character is $\operatorname{wave}(c) = \exp(c - \bar c)$, and $\operatorname{unitOrOne}(c)$ is $c$ as a unit if $c \neq 0$ and $1$ if $c = 0$.

The forms of the chapter are the forms $\mathcal I_j(p, q; \omega)$ of floor $j$ of [the chapter on frames](/chapter/local-frames/), for the place datum at $\mathbb C$ of [Section 2](/chapter/real-densities/#haar-measure-and-the-floors). Here $p, q : \mathbb N \to \mathbb C^\times$ are lists of units and $\omega$ is a weight on $G_1$ of modulus at most $1$.

### The main result

The result needs three constants. Let $\Theta = \pi^{(2\varrho + 1)k} \operatorname{vol} U(k)/\operatorname{vol} U(r)$ (Lean: `New.Shape.scaledVolumeRatio`), where $\operatorname{vol} U(j)$ is the volume of [the compact unitary group](/chapter/discrete-series/#parameters-and-the-coefficient). Let $\ell_K(t) = t^K \min(1, t)^6$ for $t \in \mathbb R$ (Lean: `New.dampedPower`). For $R \in \mathbb R$, $K, i \in \mathbb N$ and a list $p$, let $\delta_l = p_0 p_1 \cdots p_l$, and let

$$\Lambda_{R, K}(i, p) = \prod_{l < i} \begin{cases} \max(1, |\delta_l|^{-1})^K & \text{if } |\delta_l| \leq R, \\ 0 & \text{otherwise} \end{cases}.$$

This is the *head weight* (Lean: `New.headWeight`). The sieve also needs a vector for each list. Let $c_G = \operatorname{vol} U(k)\, S_k(1)/\operatorname{vol} U(r)$, with $S_k(1) = 2\pi^k/(k-1)!$ (Lean: `New.Shape.openCellConst`). For $\sigma \in G_1$ and a list $p$, the vector $N_\sigma(p) \in \mathbb C^{I \times I}$ (Lean: `New.normalizedOrbitalIntegral`) is

$$N_\sigma(p) = \frac{\sqrt{c_G}\, \sqrt{|p_\varrho|^2 - 1}^{\,k - 1}}{|I|} \prod_{a < \varrho} |p_a|^{k + 1 + 2(\varrho - a - 1)} \cdot \mathcal J_W(w_p \sigma).$$

The tensor $\mathcal J_W$ is defined by:

$$\mathcal J_W(\gamma) = \int_{G_1} W(y) \otimes \overline{W(\gamma^{-1} y)}\, dy.$$

Here $w_p$ is the Weyl element with $e_a \mapsto p_a e^*_a$ and $e^*_a \mapsto e_a/\bar p_a$ for $a < \varrho$, and $\mathcal J_W$ is the orbital integral `New.besselOrbitalIntegral` for Haar measure.

**Definition (Local bounds).** Let $b, \deg \in \mathbb R$, and let $J_i(p, q)$ be complex numbers for $i \in \mathbb N$ and lists $p, q$. The forms $J$ have the *local bounds* for $W$ if the following two conditions hold.

1. $J$ is a sieve system over $\mathbb C$ with $n_{\mathrm{sieve}} = \varrho$, the entries $c \mapsto \operatorname{unitOrOne}(c)$, the map $z \mapsto z^{-1}$ back to $\mathbb C$, the character $\operatorname{wave}$, the bottom bound $(1 + b^{-10})/\deg$, the weights $\Lambda_{b^{60n^2}, n^6}$ and the decay $\beta(\xi) = \Theta\, b^{2000 n^9}\, \ell_{k - n^7}(|\xi|^{-1})$.
2. For every $\sigma$ that fixes the hyperbolic basis vectors and all lists $p, q$ with $Z(\sigma)_{\mathrm{top}, \mathrm{top}} = p_\varrho$ and $q_\varrho = p_\varrho$, the top form is $J_n(p, q) = \langle N_\sigma(p), N_\sigma(q) \rangle$.

Lean: `New.HasLocalBounds` (New/Spanning/Bessel/Basic.lean).

The structure of a sieve system belongs to [the main term](/chapter/main-term/), a later chapter of this volume. It is stated here in full. For a ring $C$ with a measure, a map $u : C \to U$, a map $\iota : U \to C$, a number $N$, forms $J_i$ on lists in $U$, a function $\psi$ on $C$, a number $E$, weights $\Lambda$ and a decay $\beta$, the forms are a *sieve system* if these six conditions hold.

1. $\psi(0) = 1$.
2. For $i \leq N$, lists $p, q$ and $\xi \in C$, let $f(c) = \psi(\xi c)\, J_{i+1}(p[i \mapsto u(c)], q[i \mapsto u(c)])$. Then $f$ is integrable, $\int f = J_i(p, q)$ if $\xi = 0$, and $|\int f| \leq \beta(\xi)\, \Lambda(i, p)\, \Lambda(i, q)$ if $\xi$ is a unit.
3. For every finite family of lists $a_1, \dots, a_m$ with a common entry at position $N$, the matrix $(J_{N+1}(a_i, a_j))_{i,j}$ is positive semidefinite.
4. The top form $J_{N+1}$ is jointly continuous.
5. $|J_0(p, q)| \leq E$ for all $p, q$.
6. For $i < N$, if $\xi = \iota(p_i) - \iota(q_i)$ is a unit, then $|J_{i+1}(p, q)| \leq \beta(\xi)\, \Lambda(i + 1, p)\, \Lambda(i + 1, q)$.

Lean: `New.SieveSystem`, `New.dampedPower`, `New.headWeight` (New/Spanning/MainTerm/SieveSystem.lean).

In condition 2 the integral is over $C = \mathbb C$ with Lebesgue measure. In condition 6 at $\mathbb C$, $\xi = p_i^{-1} - q_i^{-1}$.

**Theorem (Local bounds at a real place).** Let $F$ be a cut Bessel function of $W$ with base $b$ and degree $f$, and let $\deg > 0$. Assume:

1. $\int_{G_1} |\langle W, R(x) W \rangle|^2\, dx \leq |I|^2/\deg$, where $\langle W, R(x) W \rangle = \int_{\mathsf U \backslash G_1} \langle W(y), W(yx) \rangle\, dy$.
2. $\deg \cdot \Theta \leq b^{4r^2}$.
3. For every $T \geq 1$, $\deg \cdot \operatorname{vol}\{g \in G_1 : \|g\| \leq T\} \leq T^{9r^2} b^{99 r^2}$, for the operator norm.
4. $4000 n \leq f$.

Then there are forms $J$ with the local bounds for $F$, with these $b$ and $\deg$.

Lean: `New.Floors.exists_hasLocalBounds_of_isCutBessel` (New/Spanning/Frames/RealBandLimits.lean).

The integrals in hypothesis 1 and 3 are lower integrals in $[0, \infty]$, and the volume is for the Haar measure `volume` of $G_1$. Hypothesis 1 says that $\deg$ plays the part of a formal degree. The forms of the proof are $J_i = c_F\, \mathcal I_i(p, q; 1)$ for $i \leq \varrho$, where $c_F$ is a normalising constant, and $J_i(p, q) = \langle \Xi(p), \Xi(q) \rangle$ for $i > \varrho$, where $\Xi$ is the vector of [Section 6](/chapter/real-densities/#band-limits-and-the-local-bounds).

**Remark (Formalization).** The conclusion is about the cut function $F$, so condition 2 of the local bounds involves the orbital integrals of $F$, not of $W$. The hypotheses 1 to 3 are about $W$ and the group alone. The factor $\sqrt{|p_\varrho|^2 - 1}$ in $N_\sigma(p)$ is the real square root `Real.sqrt`, which is $0$ on negative numbers. Since $k \geq 2$, $N_\sigma(p) = 0$ whenever $|p_\varrho| \leq 1$. In condition 2 this is no junk value: if $\sigma$ fixes the hyperbolic basis vectors, the column $\sigma z$ has $h(\sigma z, \sigma z) = -1$, so $|h(z, \sigma z)| \geq 1$, and the factor $(|p_\varrho|^2 - 1)^{(k-1)/2}$ is $0$ in the textbook sense too when $|p_\varrho| = 1$. For the vector $\Xi(p)$ of Section 6 with $|p_\varrho| < 1$ the value $0$ is a convention of the source. It agrees with the density of the top floor, which is $0$ on the closed unit disc.

### The plan of the proof

The proof has five steps, one for each of the next five sections.

1. *Haar measure and the floors.* The place datum at $\mathbb C$ consists of measures on the floors, a set of close pairs and a box. The product $\mathsf M$ of all floor measures is a multiple $\lambda\, dg$ of Haar measure, with $0 < \lambda < \infty$ and $\lambda \leq \operatorname{vol} U(r)/\operatorname{vol} U(k)$. This is [Section 2](/chapter/real-densities/#haar-measure-and-the-floors).
2. *The gauge.* For each scale $L \geq \rho$ there is a gauge in which size $j$ means modulus at most $L^j$, with loss $L^2$. Its main axiom is a common bound with constant $L^2$. The model case above is its analytic core. This is [Section 3](/chapter/real-densities/#the-gauge-at-the-complex-place).
3. *Lengths and depth.* At $\mathbb C$ the set of stable products with $e_a$ is a disc, and the depth of $e_a$ is a Euclidean quantity divided by $\pi$. A position far from $1$ forces a deep vector. This is [Section 4](/chapter/real-densities/#lengths-and-depth).
4. *Shells.* Every position lies in a dyadic shell. Each shell is a shell in the sense of the general machine, so the integral of a majorant of the form with a gain converges and is bounded. With the gain $(\pi^2/|y|^2)^{k-5}$ this gives a bound for the form of each floor. This is [Section 5](/chapter/real-densities/#cut-bessel-functions-over-shells).
5. *Band limits.* The top form is the Gram form of a continuous vector $\Xi(p)$. The descent from floor $i + 1$ to floor $i$ is a theorem of the general machine. The bottom form is bounded by a split into the position ball and the remote positions. This is [Section 6](/chapter/real-densities/#band-limits-and-the-local-bounds).

### What the chapter uses

The chapter uses the following results of earlier chapters, each stated in one line where it is used.

- The place $\mathbb C$, the floor measures, the fibre measures of the Gram map and the Cartan decomposition, from [the chapter on Bessel functions and the Bruhat cell](/chapter/bessel-bruhat/#places-fibres-and-the-complex-place).
- The Haar measures of the unipotent groups and the measure on $\mathsf U \backslash G_1$, from [the same chapter](/chapter/bessel-bruhat/).
- The volumes $\operatorname{vol} U(j)$ and the normalisation of Haar measure on $G_1$, from [the chapter on the discrete series](/chapter/discrete-series/#parameters-and-the-coefficient).
- Cut pairs, the bound for the inner products of the cut function and the constant $c_G$, from [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/).
- Place data, gauges, shells, the forms $\mathcal I_j$, the descent, the local gains and the shell sum, from [the chapter on frames, depth and gains](/chapter/local-frames/).

The chapter uses one result of a later chapter. The file New/Spanning/Bessel/Basic.lean of [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/) imports New/Spanning/MainTerm/SieveSystem.lean, which this volume places in [the chapter on the main term](/chapter/main-term/). The three files of this chapter import Bessel/Basic.lean, so they import the sieve system through it. They use `New.SieveSystem`, `New.dampedPower` and `New.headWeight`, and the statements above give them in full. No file of this chapter imports a later chapter directly.
