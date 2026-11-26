---
title: The ring A_inf and the map theta
lean:
  - Lib/PadicHodge/PeriodRings/Ainf.lean
  - Lib/PadicHodge/PeriodRings/AxTheorem.lean
decls:
  - New.Period.Ainf
  - New.Period.theta
  - New.Period.FrobGal
  - New.Period.epsPow
  - New.Period.xi_mul_tau
  - New.Period.Witt.dvd_of_mem_of_constantCoeff_dvd
  - New.Period.theta_eq_zero_iff_dvd_of_untilt_dvd
  - New.Period.theta_eq_zero_iff_xi_dvd
  - New.Period.mu_dvd_of_theta_frobEnd
  - New.Period.Ainf.prime_xi
  - New.Period.Ainf.isAdicComplete_span_pair
  - New.Period.Ainf.exists_frobEnd_sub_xi_pow_mul_eq
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The ring A_inf and the map theta

This section defines the ring $A_{\inf}$, Fontaine's map $\theta : A_{\inf} \to O_C$, the actions of Frobenius and of $G_p$, and the elements $\tau$, $\mu$ and $\xi$. Its main result is Fontaine's theorem $\ker\theta = (\xi)$. All later rings are built from $A_{\inf}$.

### The ring and the map

**Definition (The ring A_inf).** Let $O^\flat$ be the tilt of $O_C$, the inverse limit of $O_C/p$ along $x \mapsto x^p$. The ring $A_{\inf}$ is the ring $W(O^\flat)$ of $p$-typical Witt vectors of $O^\flat$. Fontaine's map $\theta : A_{\inf} \to O_C$ is the ring homomorphism with $\theta([x]) = x^\sharp$ for the Teichmüller lift $[x]$ of each $x \in O^\flat$.

Lean: `New.Period.Ainf` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.OFlat`, `New.Period.theta`, `New.Period.theta_teichmuller`.

The ring $O^\flat$ is a perfect valuation domain of characteristic $p$. Every element of $W(O^\flat)$ has a unique expansion $\sum_{n \geq 0} [x_n] p^n$, and $\theta(\sum [x_n] p^n) = \sum x_n^\sharp p^n$. The source proves that $O^\flat$ is absolutely integrally closed: every monic polynomial of positive degree over $O^\flat$ has a root in $O^\flat$ (`New.Period.OFlat.isAbsIntegrallyClosed`). With the same property of $O_C$, this gives that $\theta$ is onto (`New.Period.theta_surjective`, from `New.Variety.fontaineTheta_surjective_of_isAbsIntegrallyClosed`).

**Definition (Frobenius and Galois actions).** Let $\mathrm{FrobGal}$ be the monoid $\mathbb{N} \times G_p$. On each period ring with a Frobenius $\varphi$, the pair $(n, g)$ acts as $\varphi^n \circ g$. On $A_{\inf}$, $g$ acts through its action on $O_C$, hence on $O^\flat$, and $\varphi$ is the Witt vector Frobenius, which comes from $x \mapsto x^p$ on $O^\flat$. The two actions commute, and $\theta(g a) = g\,\theta(a)$.

Lean: `New.Period.FrobGal` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.frobEnd`, `New.Period.FrobGal.smul_def`, `New.Period.theta_smul`, `New.Period.frobEnd_bijective`.

The map $\theta$ does not commute with $\varphi$. This failure is the reason for the next sections. The element $\xi$ below lies in $\ker\theta$, but $\theta(\varphi\xi) = p$.

### The element epsilon

**Definition (A compatible system of roots of unity).** A homomorphism $s \mapsto \varepsilon^s$ from the additive group $\mathbb{Q}$ to the multiplicative monoid of $O^\flat$ such that, for every $s$, the element $(\varepsilon^s)^\sharp$ of $O_C$ is a primitive root of unity whose order is the denominator of $s$. Put $\varepsilon = \varepsilon^1$, so that $\varepsilon^\sharp = 1$, and let $\varepsilon^{1/p}$ be the value at $1/p$.

Lean: `New.Period.epsPow` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.isPrimitiveRoot_untilt_epsPow`, `New.Period.epsTilt`, `New.Period.epsRoot`, `New.Period.untilt_epsTilt`.

The classical choice is a sequence $(1, \zeta_p, \zeta_{p^2}, \ldots)$ with $\zeta_{p^{n+1}}^p = \zeta_{p^n}$, read in $O^\flat$. The source asks for a homomorphism on all of $\mathbb{Q}$. The lemma `New.Period.exists_tilt_lift_of_character` lifts every homomorphism $a$ from $\mathbb{Q}$ to the multiplicative monoid of $\mathbb{C}_p$ with $a(1) = 1$ to $O^\flat$, by the sequence $a(s/p^n)$ reduced modulo $p$.

**Remark (Formalization).** The source takes for $a$ the map $s \mapsto \iota(e^{2\pi i s})$, where $\iota : \mathbb{C} \to \overline{\mathbb{Q}}_p$ is an isomorphism of fields. Such an isomorphism exists because both fields are algebraically closed of characteristic $0$ and of the same uncountable cardinality. The isomorphism is not explicit, and `New.Period.epsPow` is a `choose` of the lifting lemma. The text never uses a property of $\varepsilon$ beyond the one in the definition above, `New.Period.isPrimitiveRoot_untilt_epsPow`. So the choice of $\iota$ does not matter for any later statement. A reader who prefers a fixed sequence $(\zeta_{p^n})$ can read the whole chapter with it.

### The elements tau, mu and xi

Put
$$\tau = [\varepsilon^{1/p}] - 1, \qquad \mu = [\varepsilon] - 1, \qquad \xi = \sum_{i=0}^{p-1} [\varepsilon^{1/p}]^i.$$

**Lemma.** In $A_{\inf}$, $\xi\tau = \mu$ and $\varphi(\tau) = \mu$. Also $\theta(\mu) = 0$, $\theta(\xi) = 0$, $\theta(\tau) \neq 0$, and $\theta(\varphi^{j+1}\xi) = p$ for every $j \geq 0$.

Lean: `New.Period.xi_mul_tau` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.frobEnd_tau`, `New.Period.theta_mu`, `New.Period.theta_xi`, `New.Period.theta_tau_ne_zero`, `New.Period.theta_iterate_frobEnd_xi`.

*Proof.* The first identity is $X^p - 1 = (X - 1)\sum_{i<p} X^i$ at $X = [\varepsilon^{1/p}]$, and the second holds because $\varphi[x] = [x^p]$. The element $\theta[\varepsilon^{1/p}]$ is a primitive $p$-th root of unity $\zeta$, so $\theta(\mu) = 0$, $\theta(\tau) = \zeta - 1 \neq 0$ and $\theta(\xi) = 0$. For $j \geq 0$, $\theta(\varphi^{j+1}\xi) = \sum_{i<p} 1 = p$. $\square$

**Example.** For $p = 2$, $\xi = 1 + [\varepsilon^{1/2}]$, $\theta(\xi) = 1 + (-1) = 0$, and $\theta(\varphi\xi) = \theta(1 + [\varepsilon]) = 2$.

### The kernel of theta

The method of the source is successive approximation. A claim about $W(k)$ is checked modulo $p$, on the zeroth Witt coordinate in $k$, and then lifted.

**Lemma (Lifting divisibility).** Let $k$ be a perfect ring of characteristic $p$, and write $a_0$ for the zeroth Witt coordinate of $a \in W(k)$. Let $I$ be an ideal of $W(k)$ such that $px \in I$ implies $x \in I$. Let $c \in I$, and assume that $c_0$ divides $a_0$ for every $a \in I$. Then $c$ divides every element of $I$.

Lean: `New.Period.Witt.dvd_of_mem_of_constantCoeff_dvd` (Lib/PadicHodge/PeriodRings/Ainf.lean).

*Proof.* Let $x \in I$. An element of $W(k)$ lies in $(p, c)$ if and only if its zeroth coordinate is divisible by $c_0$ (`New.Period.Witt.mem_span_pair_iff`). So $x = bc + py$, and $y \in I$ since $I$ is saturated. Repeat with $y$; the partial sums converge $p$-adically and give $c \mid x$. $\square$

**Theorem (A criterion for the kernel).** Let $c \in A_{\inf}$ with $\theta(c) = 0$, and assume that $c_0^\sharp$ divides $p$ in $O_C$. Then for every $a \in A_{\inf}$, $\theta(a) = 0$ if and only if $c$ divides $a$.

Lean: `New.Period.theta_eq_zero_iff_dvd_of_untilt_dvd` (Lib/PadicHodge/PeriodRings/Ainf.lean).

*Proof.* Apply the lemma to $I = \ker\theta$, which is saturated for $p$. For $x \in \ker\theta$, $p \mid x_0^\sharp$, so $c_0^\sharp \mid x_0^\sharp$, and divisibility in $O^\flat$ can be read on untilts (`New.Variety.untilt_dvd_iff`). So $c_0 \mid x_0$. $\square$

**Theorem (Fontaine).** For $a \in A_{\inf}$, $\theta(a) = 0$ if and only if $\xi$ divides $a$.

Lean: `New.Period.theta_eq_zero_iff_xi_dvd` (Lib/PadicHodge/PeriodRings/Ainf.lean).

*Proof.* We have $\theta(\xi) = 0$, so it remains to show that $\xi_0^\sharp$ divides $p$. The source proves $\xi - [\xi_0] = p u$ with $u$ a unit of $A_{\inf}$ (`New.Period.associated_p_xi_sub_teichmuller`), by reduction to the Witt vectors of the residue field. Then $0 = \theta(\xi) = \xi_0^\sharp + p\,\theta(u)$, so $\xi_0^\sharp$ is $p$ times a unit (`New.Period.untilt_constantCoeff_xi_dvd_p`), and the criterion applies. $\square$

The same method gives a second criterion. It describes the elements that vanish under all the maps $\theta \circ \varphi^j$.

**Proposition.** Let $a \in A_{\inf}$ with $\theta(\varphi^j a) = 0$ for every $j \geq 0$. Then $\mu$ divides $a$. If $\theta(\varphi^j a) = 0$ for every $j \geq 1$, then $\tau$ divides $a$.

Lean: `New.Period.mu_dvd_of_theta_frobEnd` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.tau_dvd_of_theta_frobEnd`.

*Proof.* Let $I = \bigcap_j \ker(\theta \circ \varphi^j)$. It contains $\mu$ and is saturated for $p$. Since $O^\flat$ is a valuation ring, either $\mu_0 \mid a_0$, or $\mu_0 = a_0 c$ with $c$ not a unit. In the second case the source proves by induction that $c^{p^n} \mid \mu_0$ for every $n$, so $\mu_0 = 0$, which is false. So $\mu_0 \mid a_0$, and the lemma gives $\mu \mid a$. For the second claim, $\mu = \varphi\tau$ divides $\varphi a$, and $\varphi$ is bijective. $\square$

A consequence is that $g\tau$ is associated to $\tau$ for every $g \in G_p$, since $g$ commutes with $\theta$ and $\varphi$ (`New.Period.associated_smul_tau`). The same holds for $\xi$, by the theorem of Fontaine.

### Primes, completeness and an equation of Artin-Schreier type

**Proposition.** The elements $p$ and $\xi$ are prime in $A_{\inf}$, and $p$ does not divide $\xi$, $\tau$ or $\mu$.

Lean: `New.Period.Ainf.prime_xi` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.Ainf.prime_p`, `New.Period.not_p_dvd_xi`, `New.Period.not_p_dvd_tau`, `New.Period.constantCoeff_mu_ne_zero`.

*Proof.* $A_{\inf}/p = O^\flat$ and $A_{\inf}/\xi \cong O_C$ are domains, by the theorem of Fontaine and the surjectivity of $\theta$. If $p \mid \tau$, then $\varepsilon^{1/p} = 1$ in $O^\flat$ and $\theta(\tau) = 0$, which is false. If $p \mid \xi$, then $p \mid \xi\tau = \mu$, so $\mu_0 = 0$, which is false. $\square$

**Proposition.** Let $a$ and $c$ be non-units of $A_{\inf}$. Then $A_{\inf}$ is complete and separated for the $(a, c)$-adic topology. In particular it is $(p, \xi)$-adically complete.

Lean: `New.Period.Ainf.isAdicComplete_span_pair` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.Ainf.isAdicComplete_span_singleton`.

*Proof.* The source proves existence of limits directly. For separation, let $x \neq 0$ lie in every power of $(a, c)$, and write $x = p^n y$ with $p \nmid y$. An approximation lemma (`New.Period.dvd_of_forall_exists_sub_mem_span_pow`) shows that $\xi y$ divides $x$, so $\xi \mid p^n$ and $\theta(p^n) = 0$, which is false. $\square$

**Proposition (Artin-Schreier-Witt).** For every $n \geq 0$ and $x \in A_{\inf}$ there is $c \in A_{\inf}$ with $\varphi(c) - \xi^n c = x$.

Lean: `New.Period.Ainf.exists_frobEnd_sub_xi_pow_mul_eq` (Lib/PadicHodge/PeriodRings/Ainf.lean), `New.Period.Witt.artin_schreier_witt`.

*Proof.* Modulo $p$ the equation is $c_0^p - \xi_0^n c_0 = x_0$ in $O^\flat$. It has a solution because $O^\flat$ is absolutely integrally closed. Lift the solution by Teichmüller and correct by successive approximation modulo powers of $p$, as in the lemma on lifting divisibility. $\square$

This equation will give the surjectivity of $\varphi - 1$ in the fundamental exact sequence of Section 4, and the solution of Lang's equation for unramified characters in Section 8.

**Remark (Formalization).** The ring $O^\flat$ is Mathlib's `PreTilt` of $O_C$, and $\theta$ is Mathlib's `fontaineTheta`. The source registers a global instance, of low priority, that makes $W(S)$ an algebra over $W(A)$ for each $A$-algebra $S$ ([Ainf.lean, line 288](lean:Lib/PadicHodge/PeriodRings/Ainf.lean#L288)). No statement of this section depends on it. The register of findings records a related point on global algebra instances on $A_{\inf}$ as F-024, in the comparison files.
