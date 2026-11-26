---
title: The inputs
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/PrimeSums.lean
  - New/Reduction/Data/AdmissibleData.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The inputs

This section recalls the objects and the results that the main inequality combines. Each result is proved in another chapter or volume. The statements here are the exact statements of the source, so that the proofs of Sections 3 and 4 can cite them. The reader who knows [Theorems A, B and C](/chapter/theorems-a-b-c/) and [the prime sums and the total remainder](/chapter/prime-sums/) can go to Section 3.

### The parameters and the data

The parameters $P$ are a modulus $q_0$ and a prime $d$. The modulus is a multiple of $18480 = 16 \cdot 3 \cdot 5 \cdot 7 \cdot 11$. The prime satisfies $d \equiv q_0/2 - 1 \pmod{q_0}$, so $d \equiv 7 \pmod 8$ (see [fields, places and twists](/chapter/fields-places-twists/)). The field $K = \mathbb{Q}(\sqrt{-d})$ has the character $\chi_K = (\cdot / d)$.

The data $D$ for $P$ are the objects that grow with the length $x$ of the prime sum. [The data and its sizes](/chapter/data-and-sizes/) lists all of them. This chapter uses the following.

- Three integer scales $x$, $x_1$ and $b$, with $(\log b)^{100} \leq x$, $x^{10^6} \leq x_1$, $x_1^{10^6} \leq b$, $(\log x_1)^6 \leq \log b$ and $\log \log b \geq 10^{12} C_P$. Here $C_P$ is a bound for the constants that depend on $q_0$ and $d$ only.
- The number $m$ of lifts, a power of $2$ with $\sqrt{x} \leq m \leq 2\sqrt{x}$.
- The long order $a = x b$.
- The number $q_1 = q_0 \cdot \operatorname{towerDeg}(s)$, where $2^s = m^{22}$, a primitive root of unity $\zeta_{q_1}$ of order $q_1$, and the CM field $E = K(\zeta_{q_1})$ (see [fields, places and twists](/chapter/fields-places-twists/)). The field $E$ has $f$ infinite places, and they form a group $\Phi$ isomorphic to $(\mathbb{Z}/q_1)^\times$.
- The $a$-places $\Phi_a$, which are the places $\equiv 1 \pmod{q_0}$, and a set $\Phi_b$ of $b$-places, which are places $\equiv -1 \pmod{q_0}$. The data ask $\operatorname{towerDeg}(s) \leq \#\Phi_b \log b$.

Two counts follow from the structure of $\Phi$. The source proves $\#\Phi_a = \operatorname{towerDeg}(s)$, and $f = \#\Phi_a \cdot \varphi(q_0)$, since the class map $\Phi \to (\mathbb{Z}/q_0)^\times$ is onto and each fibre has $\operatorname{towerDeg}(s)$ elements. (The number $\operatorname{towerDeg}(s) = 3 l_0 2^s$ has only the prime factors $2$ and $3$, and both divide $q_0$.) With the condition on $\Phi_b$ this gives

$$\frac{\#\Phi_a}{\#\Phi_b} \;\leq\; \log b. \tag{2.1}$$

The unit of error is $\mathrm{err}_0 = f a \log^3 b$. The source calls it `errorUnit`. Write $\mathrm{loss} = f a \log^4 b$ for the loss per dimension of the size bound; the source calls it `loss`.

### The target, the source and the lattice

The objects of the method are complex vector spaces of automorphic forms. Volumes 9 to 11 construct them.

- The target is a finite-dimensional complex space $T$ of cusp forms on a unitary group of rank $r$. Its dimension is $d_T = \dim T$.
- The source is a finite-dimensional complex space $\mathrm{src}$ of algebraic forms on a definite unitary group of rank $k = r + 1 - m$.
- A finite group $G$ acts, and for each $g \in G$ there is a linear map $g \mathfrak{p} \colon \mathrm{src} \to T$, the translate by $g$ of one fixed map $\mathfrak{p}$ built from Poincaré series.
- The chain of $m$ theta lifts for the trivial twist is a linear map $\Theta_1$. For an automorphism $\sigma$ of $\mathbb{C}$, $\|\Theta_1 y\|_\sigma^2$ is the squared norm of the conjugate of $\Theta_1 y$ by $\sigma$, taken with a rational Gram matrix. In this chapter $\sigma$ is always an automorphism of $\mathbb{C}$, not a place of $E$; the places are written $\tau$.
- A source form is integral if it is integral at every pair $\iota = (\ell, \iota)$ of a prime $\ell$ and an isomorphism $\iota \colon \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$.
- The target lattice is the twisted lattice of [the lattice of integral target forms](/chapter/integral-target-forms/). For it, a family $y = (y_1, \dots, y_n)$ of target forms has *covolume at most $c$* if for every $\sigma$ the Gram determinant $|\det(\langle \sigma \Theta_1 y_i, \sigma \Theta_1 y_j \rangle)|$ is at most $e^c$. It has *index at most $\delta$* if there are numbers $e(\ell) \geq 0$ with $\sum_\ell e(\ell) \log \ell \leq \delta$ over every finite set of primes, and for each $\iota$ a matrix over the integers of $\bar{\mathbb{Q}}_\ell$, with loss $e(\ell)$, which carries $y$ into the vectors integral at $\iota$ for every allowed twist.

### The two amounts

The *main amount* is $\mathrm{main} = m k \sum_{\tau \in \Phi} (s_\infty(\kappa(\tau)) - s_{\mathrm{fin}}(\kappa(\tau), \tau))$. Here $\kappa$ is the weight, $s_\infty$ is the size of a derivative of a given order and $s_{\mathrm{fin}}$ is a prime sum. The *total remainder* is $\mathrm{rem} = \sum_{\tau \in \Phi_a} (s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}})$, with $s_{\mathrm{main}}$ the expected value of the prime sums. [The prime sums and the total remainder](/chapter/prime-sums/) defines them. Two facts are used here.

**Proposition (Recalled: the main amount is large).** For admissible data, $x^4 f a \leq \mathrm{main}$. In particular $\mathrm{main} \geq 0$.

Lean: `New.Data.le_mainAmount`, `New.Data.mainAmount_nonneg` (New/Reduction/PrimeSums.lean).

**Theorem (Recalled: the identity for the total remainder).** For admissible data,

$$\mathrm{rem} \;=\; a \Big( \#\Phi_b \big( R_{q_0}(x) - R_{q_0}(x_1) \big) + \#\Phi_a \, R_1(x_1) \Big).$$

Lean: `New.Data.totalRemainder_eq` (New/Reduction/PrimeSums.lean).

Here $R_q(y) = \sum_{n \leq y} \lambda_q(n)(1/n - 1/y) - \log y / \varphi(q) - c_q$, with $\lambda_q(n) = \Lambda(n)(1 - \chi_K(n))$ for $n \equiv 1 \pmod q$ and $\lambda_q(n) = 0$ otherwise, and $c_q$ the constant of [the weighted prime remainder](/chapter/weighted-prime-remainder/). So $R_{q_0}$ is the remainder for the class $1 \bmod q_0$, and $R_1$ is the remainder over all integers.

### Theorems A, B and C

The three theorems are proved in Volumes 9, 10 and 11. [Theorems A, B and C](/chapter/theorems-a-b-c/) gives a plan of each proof.

**Theorem (Recalled: Theorem A (a), short forms).** The source $\mathrm{src}$ is spanned by the integral forms $\varphi$ with

$$\|\Theta_1 \, g \mathfrak{p} \, \varphi\|_\sigma^2 \;\leq\; \exp\big( \mathrm{main} - m \cdot \mathrm{rem} + f a \log^4 b \big)$$

for every $g \in G$ and every automorphism $\sigma$ of $\mathbb{C}$.

Lean: `New.Data.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean).

The primes enter here, through the term $-m \cdot \mathrm{rem}$: if $\mathrm{rem}$ is large, the short forms are shorter.

**Theorem (Recalled: Theorem A (b), the index).** Let $\mathcal{G} \subseteq G$ be finite, and let $y_1, \dots, y_n$ be target forms such that each $y_i$ is $g \mathfrak{p} \varphi$ for some $g \in \mathcal{G}$ and some integral $\varphi$. Then $y$ has index at most $\#\mathcal{G} \cdot \dim \mathrm{src} \cdot 2\, \mathrm{err}_0$ in the target lattice.

Lean: `New.Data.indexLe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

**Theorem (Recalled: Theorem B, enough forms).** The target has dimension $d_T \geq 1$, and there is a finite set $\mathcal{G} \subseteq G$ with

$$\#\mathcal{G} \cdot \dim \mathrm{src} \;\leq\; 5 \, d_T \log(1 + 2b^2) \quad\text{and}\quad (1 - 4/b^2)\, d_T \;\leq\; \dim \sum_{g \in \mathcal{G}} g \mathfrak{p}(\mathrm{src}).$$

Lean: `New.Data.enough_forms` (New/Reduction/ShortAndEnough.lean).

**Theorem (Recalled: Theorem C, integral forms are long).** Let $y_1, \dots, y_n$ be linearly independent target forms with $n \geq (1 - 4/b^2) d_T$. If $y$ has index at most $\delta$ and covolume at most $c$ in the target lattice, then

$$d_T \big( \mathrm{main} - 3 f a \log^4 b \big) \;\leq\; c + 2\delta.$$

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

Theorem C is a product formula argument. It completes $y$ to a basis, chooses a twist for each $\iota$, and applies the inequality $\text{covolume} + 2 \cdot \text{index} + \dots \geq 0$ of [twisted lattices](/chapter/twisted-lattices/). The factor $2$ in front of $\delta$ comes from the use of the matrices at $\iota$ and at its complex conjugate. The error $3 f a \log^4 b$ collects three terms: $d_T f a \log^4 b$ from the heights of the single lifts, $d_T b$ from the scalars in the ratio of volumes, and at most $d_T b$ from the completion to a basis. Since $b \leq f a \log^4 b$, the sum is at most $3 d_T f a \log^4 b$.

### Hadamard's inequality

**Lemma (Recalled: Hadamard's inequality).** Let $y_1, \dots, y_n$ be target forms with $\|\Theta_1 y_i\|_\sigma^2 \leq e^h$ for every $i$ and every $\sigma$. Then $y$ has covolume at most $n h$.

Lean: `New.TwistedLattice.covolumeLe_of_normSqAt_le` (New/Reduction/Lattices/TwistedLattice.lean).

This is $|\det(\langle v_i, v_j \rangle)| \leq \prod_i \|v_i\|^2$, applied after each conjugation $\sigma$.

**Remark (Formalization).** In this section the words "Recalled" mark statements whose proofs are in other chapters. The `Lean:` lines name the declarations of the source. The source writes the maps $g \mathfrak{p}$ as `D.normalizedPoincare g`, the source $\mathrm{src}$ as `D.ramifiedSourceForms`, the integral forms as `D.integralRamified`, the group $G$ as `D.chosenGL`, and $d_T$ as `D.targetDim`. The integrality in Theorem A (a) is integrality at every $\iota$, and the bound holds for all $g \in G$ at once, not only for the $g$ of the set $\mathcal{G}$ of Theorem B. The source writes `t` for this set; the book keeps $t$ for $5r$.
