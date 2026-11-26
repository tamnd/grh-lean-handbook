---
title: The seesaw for periods
lean:
  - Lib/Weil/Seesaw.lean
decls:
  - New.Exchange.kernelPair
  - New.Exchange.modLift
  - New.Exchange.modTransposedLift
  - New.Exchange.IsConjKernelPair
  - New.Exchange.isConjKernelPair_kernelPair
  - New.Exchange.IsEdgeFamily
  - New.Exchange.isEdgeFamily_of_paramsCorrespond
  - New.Exchange.IsEdgeFamily.exists_lift_eq_realConv
  - New.Exchange.IsEdgeFamily.petersson_lift_eq_mul_inner_modTransposedLift
  - New.Space.periodPairing
  - New.Exchange.integral_kernel_mul_forms_eq_integral_periodPairing
  - New.Exchange.IsSeesawMatched
  - New.Exchange.seesaw_periods
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The seesaw for periods

Kudla's seesaw compares two theta lifts through one theta kernel. This section states the form of it that the proof of Theorem C uses. The two lifts may come from different dual pairs, and the kernels need to agree only up to weights of moderate growth, on a set of polynomials that spans all polynomials.

### The classical seesaw

Let $W$ be a symplectic space, and let $(G, G')$ and $(H, H')$ be two dual pairs in $\mathrm{Sp}(W)$ with $H \subset G$ and $G' \subset H'$. Let $\theta(\varphi)(g, g')$ be the theta kernel of a datum $\varphi$. It restricts to both pairs. Let $f$ be a form on $H$ and $y$ a form on $G'$. If all integrals converge absolutely, then by Fubini's theorem
$$\int_{[H]} \Big( \int_{[G']} \theta(\varphi)(h, g')\, y(g')\, dg' \Big) f(h)\, dh = \int_{[G']} \Big( \int_{[H]} \theta(\varphi)(h, g')\, f(h)\, dh \Big) y(g')\, dg'.$$
The left side is a period over $H$ of the lift of $y$ to $G$. The right side is a period over $G'$ of the lift of $f$ to $H'$ (Kudla 1984). The standard example in the unitary case is $G = \mathrm{U}(S_1 \oplus S_2)$ and $H = \mathrm{U}(S_1) \times \mathrm{U}(S_2)$, with $G' = \mathrm{U}(T)$ diagonal in $H' = \mathrm{U}(T) \times \mathrm{U}(T)$. The seesaw identities of Section 2 say that the kernel of $S_1 \oplus S_2$ restricted to $H \times G'$ is the product of the two kernels.

The version in this section has two features. First, the identity is not of kernels on a common group. It is an identity $N(g)\, \theta_2(j_N(g), x) = M(x)\, \theta_1(g, j_M(x))$ between kernels of two pairs, read through continuous maps $j_N$, $j_M$ and multiplied by moderate weights $N$, $M$. Second, the identity is asked only for some polynomials $p$ at infinity, and density in the Fock space carries the conclusion to the polynomial of the edge.

### Families over one edge

The seesaw is applied to whole families of characters at once. In this section a character family is a function $a$ that gives an automorphic character $a(n)$ for each rank $n$, and an indexed family $(a_i)$ of these.

**Definition (The pair of type kernels).** For a family $l$ of parameters of the signs $s$, the pair of type kernels is $k_l(\mathrm{false}) = e_l$ and $k_l(\mathrm{true}) = e_{-l}$.

Lean: `New.Exchange.kernelPair` (Lib/Weil/Seesaw.lean).

**Definition (Conjugate pair of cusp kernels).** A pair $k$ of kernels on $G_{S,\infty}$, indexed by $d \in \{\mathrm{false}, \mathrm{true}\}$, is a conjugate cuspidal pair if each $k(d)$ is a cusp kernel of order $0$ and $k(\neg d) = \overline{k(d)}$.

Lean: `New.Exchange.IsConjKernelPair` (Lib/Weil/Seesaw.lean).

**Lemma.** If $\pm l$ has a large gap at every real place, then $k_l$ is a conjugate cuspidal pair.

Lean: `New.Exchange.isConjKernelPair_kernelPair` (Lib/Weil/Seesaw.lean).

*Proof.* A large gap makes the discrete series kernels cusp kernels of order $0$. The conjugate of the discrete series kernel of $l$ is that of $-l$. $\square$

**Definition (Edge family).** Let $(a_i)_{i \in I}$ be a family of character families, $k$ and $k'$ pairs of kernels on $G_{S,\infty}$ and $G_{T,\infty}$, $d$ a sign and $\Phi$ a polynomial. They form an edge family if:

1. $k$ and $k'$ are conjugate cuspidal pairs;
2. there are weights $\gamma, \gamma'$ and tame parts $\psi_i$ such that, for every $i$, the character $a_i(n)$ has weight $\gamma$ and tame part $\psi_i$, and $a_i(n')$ has weight $\gamma'$ and tame part $\psi_i$;
3. the Fock vector of $\Phi$ is an edge for $\Omega_{\gamma,\gamma'}$ from $k(d)$ to $k'(d)$.

Lean: `New.Exchange.IsEdgeFamily` (Lib/Weil/Seesaw.lean).

**Theorem.** Let $s$ and $s'$ be nonempty. Let $\pm l, \pm l'$, with the sign given by $d$, correspond for the weights $\gamma, \gamma'$. If each $a_i(n)$ has weight $\gamma$ and $a_i(n')$ has weight $\gamma'$, both with tame part $\psi_i$, then $(a_i)$, $k_l$, $k_{l'}$, $d$ and the chosen joint harmonic $\Phi_{\pm l, \pm l'}$ form an edge family.

Lean: `New.Exchange.isEdgeFamily_of_paramsCorrespond` (Lib/Weil/Seesaw.lean).

*Proof.* The block rule implies the matching condition, and matching gives the large gaps for $\pm l$ and $\pm l'$. The previous lemma gives 1. Condition 3 is the theorem of Section 4 that joint harmonics are edges. $\square$

**Definition (Lift and transposed lift with a function modulo $\mathfrak{m}$).** Let $a$ be a character family, $P$ a polynomial and $\Psi$ a function on matrices modulo $\mathfrak{m}$. The lift $\mathcal{L}^{S \to T}_{a, P, \Psi}$ from forms of type $e$ on $G_S$ to forms of type $e'$ on $G_T$ is the lift on forms of Section 4 for the kernel $\theta^{S,T}_{a(n), a(n')}$ and the datum $v_P \otimes \Psi \otimes \mathrm{vac}$. The transposed lift is the lift on forms for the swapped kernel and the same datum. It goes from forms of type $e'$ on $G_T$ to forms of type $e$ on $G_S$, and it involves no complex conjugation.

Lean: `New.Exchange.modLift`, `New.Exchange.modTransposedLift` (Lib/Weil/Seesaw.lean).

**Theorem.** Let $(a_i), k, k', d, \Phi$ be an edge family.

1. For every polynomial $Q$ there is one continuous function $\alpha$ of compact support on $G_{T,\infty}$ such that, for all $i$, spaces $S, T$, moduli $\mathfrak{m}$, functions $\Psi$ and forms $y$ of type $k(d)$, the lift of $y$ with $v_Q \otimes \Psi \otimes \mathrm{vac}$ is $\alpha * \mathcal{L}^{S \to T}_{a_i, \Phi, \Psi}\, y$.
2. For every polynomial $Q$ there is one $\kappa \in \mathbb{C}$ such that, for all such data and all forms $y$ of type $k(\neg d)$ and $z$ of type $k'(\neg d)$, the Petersson product of $z$ with the conjugate of the lift of $\bar y$ with $v_Q \otimes \Psi \otimes \mathrm{vac}$ is $\kappa$ times the inner product of the transposed lift of $z$ with $y$.

Lean: `New.Exchange.IsEdgeFamily.exists_lift_eq_realConv`, `New.Exchange.IsEdgeFamily.petersson_lift_eq_mul_inner_modTransposedLift` (Lib/Weil/Seesaw.lean).

*Proof.* Statement 1 is condition 4 of the half edge, for the kernels $\theta^{S,T}_{a_i(n), a_i(n')}$. They have real part $\Omega_{\gamma,\gamma'}$ for every $i$ since the weights do not depend on $i$. Statement 2 is the theorem on the polynomial factor of Section 4, conjugated, combined with the adjointness of the lift on forms. $\square$

### Periods

**Definition (Period pairing).** Let $k$ be a conjugate cuspidal pair on $G_{S,\infty}$, $(M, j)$ a moderate weight from $S$ to $T$, and $r$ a real point of $G_T$. For a form $f$ of type $k(d)$ on $G_S$ and a form $U$ on $G_T$, the period is
$$\mathcal{P}_{M, r}(f, U) = \int_{[S]} M(z)\, f(z)\, U\big(j(z)\,(r, 1)\big)\, dz.$$

Lean: `New.Space.periodPairing` (Lib/Weil/Seesaw.lean).

The integral converges: $f$ is of rapid decay, since $k(d)$ is a cusp kernel, $M$ is moderate, and $U$ is bounded. The period is bilinear in $f$ and $U$. When $S \subset T$ and $j$ is the inclusion, with $M = 1$, it is the usual period of $U$ against $f$ over the subgroup.

In the rest of this section there are four spaces. The first pair lifts from $S$ (signs $s$, $n$ coordinates) to $T$ (signs $t$, $m$ coordinates), with character families $a_o$, kernel pairs $k$ on $S$ and $l$ on $T$, and polynomial $\Phi$. The second pair lifts from $T'$ (signs $t'$, $m'$ coordinates) to $S'$ (signs $s'$, $n'$ coordinates), with character families $a'_o$, kernel pairs $l'$ on $T'$ and $k'$ on $S'$, and polynomial $\Phi'$.

**Lemma (Seesaw for one pair of forms).** Let $k$ and $k'$ be conjugate cuspidal pairs. Let $y$ be a form of type $k(d)$ on $G_S$ and $f$ a form of type $k'(d')$ on $G_{S'}$. Let $N$ be a moderate weight from $S$ to $T'$ and $M$ one from $S'$ to $T$. Let $Q$ and $p$ be polynomials, and $\Psi$ and $\Psi'$ functions modulo $\mathfrak{m}$. Assume:

1. the lift of $y$ with $v_Q \otimes \Psi \otimes \mathrm{vac}$ for $\theta^{S,T}_{a,b}$ equals $\alpha * U$ for a form $U$ on $G_T$ and a function $\alpha$ of compact support on $G_{T,\infty}$;
2. for all $g \in G_S$ and $x \in G_{S'}$,
$$N(g)\, \theta^{T',S'}_{a',b'}[\Psi', p](j_N(g), x) = M(x)\, \theta^{S,T}_{a,b}[\Psi, Q](g, j_M(x)).$$

Then
$$\int_{[S]} \int_{[S']} N(g)\, y(g)\, \theta^{T',S'}_{a',b'}[\Psi', p](j_N(g), x)\, f(x)\, dx\, dg = \int_{G_{T,\infty}} \alpha(r)\, \mathcal{P}_{M, r}(f, U)\, dr.$$

Lean: `New.Exchange.integral_kernel_mul_forms_eq_integral_periodPairing` (Lib/Weil/Seesaw.lean).

*Proof.* Use 2 to replace the kernel of the second pair by $M(x)$ times the kernel of the first pair. Exchange the integrals over $[S]$ and $[S']$ by Fubini's theorem. The function is integrable by the integrability lemma of Section 3, since $y$ and $f$ are rapid and the weights are moderate. The inner integral over $[S]$ is the lift of $y$ with $Q$ at $j_M(x)$, which is $(\alpha * U)(j_M(x))$ by 1. Write the convolution as an integral over $r$, and exchange the integrals over $r$ and $[S']$ by Fubini's theorem again. $\square$

### The seesaw for families

The data of the theorem are indexed by $o \in J$ and $i \in X_o$, with finite sets $W_o \subset X_o$ and coefficients $u_{o,i}$. Let $c = (c_o)$ be a vector in $\mathbb{C}^J$. There are forms $y_{o,i}$ of type $k(d)$ on $G_S$ and $f_{o,i}$ of type $k'(\neg d')$ on $G_{S'}$, moderate weights $N_{o,i}$ from $S$ to $T'$, moduli $\mathfrak{m}_o$, and functions $\Psi'_{o,i}$ modulo $\mathfrak{m}_o$.

**Definition (Matched polynomial).** A polynomial $p$ for the second pair is matched if there are a polynomial $Q$ for the first pair, functions $\Psi_{o,i}$ modulo $\mathfrak{m}_o$ and moderate weights $M_{o,i}$ from $S'$ to $T$ with two properties.

1. Proportional periods: for every real point $r$ of $G_T$ there is $\beta_r \in \mathbb{C}$ with
$$\sum_{i \in W_o} u_{o,i}\, \mathcal{P}_{M_{o,i}, r}\big(f_{o,i},\, \mathcal{L}^{S \to T}_{a_o, \Phi, \Psi_{o,i}}\, y_{o,i}\big) = \beta_r\, c_o \quad \text{for all } o.$$
2. Matched kernels: for all $o$, $i$, $g \in G_S$ and $x \in G_{S'}$,
$$N_{o,i}(g)\, \theta^{T',S'}_{a'_o(m'), a'_o(n')}[\Psi'_{o,i}, p](j_{N_{o,i}}(g), x) = M_{o,i}(x)\, \theta^{S,T}_{a_o(n), a_o(m)}[\Psi_{o,i}, Q](g, j_{M_{o,i}}(x)).$$

Lean: `New.Exchange.IsSeesawMatched` (Lib/Weil/Seesaw.lean).

**Theorem (Seesaw for periods).** Let $(a_o), k, l, d, \Phi$ be an edge family for the pair from $S$ to $T$, and $(a'_o), l', k', d', \Phi'$ an edge family for the pair from $T'$ to $S'$. Assume that the matched polynomials span the space of all polynomials in the variables of $\operatorname{Hom}(T', S')$ at the real places. Let $r$ be a real point of $G_{T'}$. Then there is $\beta \in \mathbb{C}$ with
$$\sum_{i \in W_o} u_{o,i}\, \mathcal{P}_{N_{o,i}, r}\big(y_{o,i},\, \mathcal{L}'^{\,T' \to S'}_{a'_o, \Phi', \Psi'_{o,i}}\, f_{o,i}\big) = \beta\, c_o \quad \text{for all } o \in J,$$
where $\mathcal{L}'$ is the transposed lift from forms of type $k'(\neg d')$ on $G_{S'}$ to forms of type $l'(\neg d')$ on $G_{T'}$.

Lean: `New.Exchange.seesaw_periods` (Lib/Weil/Seesaw.lean).

*Proof.* For a Fock vector $v$ of $\operatorname{Hom}(T', S')$ put
$$L_{o,i}(v) = \int_{[S]} \int_{[S']} N_{o,i}(g)\, y_{o,i}(g)\, \theta\big(\omega(j_{N_{o,i}}(g), x)(v \otimes \Psi'_{o,i} \otimes \mathrm{vac})\big)\, f_{o,i}(x)\, dx\, dg,$$
with the kernel of the second pair. By the moderate growth of the kernel and the rapid decay of the forms, $L_{o,i}$ is a continuous linear functional on the Fock space. Let $L(v) \in \mathbb{C}^J$ be the vector with entries $L(v)_o = \sum_{i \in W_o} u_{o,i} L_{o,i}(v)$. Then $L$ is continuous for the product topology on $\mathbb{C}^J$.

*Step 1.* We show that $L(v) \in \mathbb{C} c$ for every $v$. The line $\mathbb{C} c$ is finite dimensional, hence closed, and $L$ is continuous, so its preimage is a closed subspace. The Fock vectors of polynomials are dense in the Fock space. So it is enough to show $L(v_p) \in \mathbb{C} c$ for all polynomials $p$, and since the preimage is a subspace and the matched polynomials span, it is enough to do this for matched $p$. Let $p$ be matched with $Q$, $\Psi_{o,i}$ and $M_{o,i}$. Put $U_{o,i} = \mathcal{L}^{S \to T}_{a_o, \Phi, \Psi_{o,i}} y_{o,i}$. By statement 1 of the theorem on edge families there is one $\alpha$ such that the lift of $y_{o,i}$ with $Q$ is $\alpha * U_{o,i}$ for all $o, i$. The lemma for one pair of forms gives
$$L_{o,i}(v_p) = \int \alpha(r')\, \mathcal{P}_{M_{o,i}, r'}(f_{o,i}, U_{o,i})\, dr'.$$
Multiply by $u_{o,i}$, sum over $W_o$, and use the proportional periods. This gives $L(v_p)_o = \big(\int \alpha(r') \beta_{r'}\, dr'\big)\, c_o$.

*Step 2.* We identify the left side of the claim. By the definition of an arrow, the transposed lift $\mathcal{L}' f_{o,i}$ is the integral of the kernel against $f_{o,i}$. Its translate by $(r, 1)$ is the lift with the datum moved by $\omega(1, (r, 1))$, by the right translation law. The point $(r, 1)$ is real, so it moves only the real part of the datum, to $\Omega_{\gamma,\gamma'}(r, 1) v_{\Phi'}$. So the period on the left of the claim is $L_{o,i}(\Omega_{\gamma,\gamma'}(r, 1) v_{\Phi'})$. Here $\gamma, \gamma'$ are the weights of the edge family $(a'_o)$, which do not depend on $o$. By Step 1, $L(\Omega_{\gamma,\gamma'}(r, 1) v_{\Phi'}) = \beta c$ for some $\beta$. $\square$

**Remark (Formalization).** The spanning condition is a hypothesis (`h_span`, Seesaw.lean line 663). The theorem does not say for which data the matched polynomials span. The user in the proof of Theorem C, in [grids, paths and turns](/chapter/grids-paths-turns/), supplies this hypothesis at the two calls in New/Determinant/AuxiliaryForms/DiagonalTurns.lean (lines 360 and 383), where the variables split into two blocks of columns and products of polynomials in the two blocks span. The constant $\beta$ comes from an existence statement. It can be $0$, and the theorem says nothing about it beyond the identity. In particular, if $c = 0$, the theorem says only that the sums of periods vanish. The index type $J$ may be infinite. Then $\mathbb{C}^J$ carries the product topology, and the line $\mathbb{C} c$ is still closed.

**Remark (Formalization).** In the classical seesaw both sides are periods of lifts with the same datum. In the theorem the periods of the first pair are with the polynomial $\Phi$ of the first edge, while the kernels are matched with other polynomials $Q$. The bridge is the convolution identity of the first edge family, which is uniform over $o$ and $i$. This is why the theorem asks for edge families, with weights that do not depend on the index, and not only for edges.
