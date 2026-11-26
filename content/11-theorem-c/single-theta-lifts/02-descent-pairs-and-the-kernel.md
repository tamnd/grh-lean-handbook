---
title: Descent pairs and the vector kernel
lean:
  - New/UpperBound/Objects/AuxiliaryPair.lean
  - New/UpperBound/Objects/Rows.lean
  - New/Determinant/Norms/VectorKernel.lean
  - New/Determinant/Norms/AdjointThetaLift.lean
  - Lib/Adelic/AutomorphicForms/PAdicGauge.lean
decls:
  - New.DescentPair
  - New.Data.descentPair
  - New.DescentPair.levelGroup
  - New.DescentPair.levelChar
  - New.DescentPair.FormV
  - New.DescentPair.charW
  - New.DescentPair.charV
  - New.DescentPair.blockDatum
  - New.DescentPair.fockDatum
  - New.DescentPair.conjKernel
  - New.DescentPair.conjKernel_apply
  - New.stdClassSum
  - New.DescentPair.normalizedDescent
  - New.DescentPair.normalizedDescent_apply
  - New.DescentPair.vectorKernel
  - New.DescentPair.gramForm_vectorKernel
  - New.DescentPair.gramForm_vectorKernel_left
  - New.DescentPair.vectorKernel_equivariant
  - New.DescentPair.vectorKernel_rational_mul
  - New.DescentPair.vectorKernel_mul_level
  - New.DescentPair.vectorKernelForm
  - New.DescentPair.vectorKernelForm_apply
  - New.DescentPair.normalizedDescent_eq_inner_vectorKernelForm
  - New.DescentPair.ofAlgForm_vectorKernelForm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Descent pairs and the vector kernel

This section recalls the descent pair and its descent. Then it builds the vector kernel $\theta_W(g, \cdot)$. This kernel is a form on $V$ for each point $g$ of $U(W)(\mathbb{A})$. The descent of a form $\Xi$ is its inner product with the kernel, and Section 3 writes the lift as an integral of the kernel.

### The pair, in brief

The descent pair is defined in [the objects of the upper bound](/chapter/upper-bound-objects/). This subsection gives only what the chapter uses.

**Definition (Descent pair).** A descent pair over a CM field $E$ consists of a hermitian space $W$ of rank $r$ with signs $s$, the standard definite space $V = I_n$ with $n > r$, an embedding $\iota : r \hookrightarrow n$ of index types, a finite family $M$ of chosen places and a finite family $Q$ of places of a twist, a character $\mu$ of $U(1)$ with a weight and a tame part $\psi$, and column counts $k^+$ and $k^-$ at the infinite places. The tame part $\psi_w$ is trivial off $M$ and $Q$.

Lean: `New.DescentPair` (New/UpperBound/Objects/AuxiliaryPair.lean).

**Definition (The $j$-th descent pair).** For the data $D$, a tame character $\vartheta$ and $j \in \mathbb{N}$, the $j$-th descent pair has $W = W_j$ of rank $r$, $V = I_{r+t}$, $\iota$ the inclusion of the first $r$ indices, the character $\mu_j^0\vartheta$ of weight $-\kappa_j$, the chosen places $M$ and the places $Q$ of $\vartheta$.

Lean: `New.Data.descentPair` (New/UpperBound/Objects/Rows.lean).

The column counts of the $j$-th pair come from the target parameter $\varsigma$ and the weight of $\mu_j^0$. The notation chapter [spaces, forms, lattices and normalizations](/chapter/notation/) lists $W_j$, $\varsigma$ and $\mu_j^0$. The rank difference $t = n - r$ of the pair is $\mathrm{rankDiff}$ in Lean.

**Definition (The level and the forms on $V$).** The level $K$ of the pair is the group of integral points $k$ of $U(V)(\mathbb{A}_f)$ such that, at each place of $M$, the reduction of $k$ fixes the basis vectors indexed by $\iota$, and at each place of $Q$, the reduction preserves the span of the other basis vectors. The character $\chi_K$ of $K$ sends $k$ to $\prod_{w \in Q}\psi_w^{-1}(\det k_{w,00})$, where $k_{w,00}$ is the block of the reduction on the rows and columns of $\iota$. The forms on $V$ are the algebraic forms of weight $(\kappa, e)$ on which $K$ acts by $\chi_K$. Here $\kappa = \mathrm{columnCount}$ and $e = \mathrm{detExp}$ are the highest weight and the determinant power given by $k^+$ and $k^-$.

Lean: `New.DescentPair.levelGroup` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.levelChar` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.FormV` (New/UpperBound/Objects/AuxiliaryPair.lean).

Since $V$ is definite, a form on $V$ is a function $\Xi$ on the finite points $U(V)(\mathbb{A}_f)$ with values in a finite dimensional representation $\rho$ of $U(V)(E)$. It satisfies $\Xi(\gamma x k) = \chi_K(k)\,\rho(\gamma)\,\Xi(x)$ for rational $\gamma$ and $k \in K$. Its values are vectors in coordinates indexed by `WeylIndex n κ`, with the Gram form $\langle\zeta, \eta\rangle_G = \zeta^*G\eta$ of the integer Gram matrix $G$ of the Weyl module.

**Definition (The class sum).** For an open compact subgroup $K$ and a function $f$ on the finite points of the standard definite space, the class sum is $\sum_c f(h_c)/\#\mathrm{Aut}(h_c)$, over chosen representatives $h_c$ of the double cosets $c$ in $U(V)(E)\backslash U(V)(\mathbb{A}_f)/K$. Here $\mathrm{Aut}(h_c)$ is the finite group $U(V)(E) \cap h_c K h_c^{-1}$.

Lean: `New.stdClassSum` (Lib/Adelic/AutomorphicForms/PAdicGauge.lean).

The inner product of two forms on $V$ is the class sum of $\langle\Xi'(h), \Xi(h)\rangle_G$. This is the inner product of `O.FormV` in Lean, and the chapter uses it on $V$ throughout.

**Definition (The characters and the datum).** The character of $W$ is $\nu_W = \upsilon^{r_-}$, where $\upsilon$ is the character of the Weil data and $r_-$ is the number of minus signs of $W$. The character of $V$ is $\nu_V = \mu\,\upsilon^{\lfloor n/2\rfloor}$. Both are characters of $[U(1)]$. The finite datum $\Psi_{\mathrm{bl}} \otimes \mathrm{vac}$ on $\mathrm{Hom}(W, V)$ is the block datum at the places of $M$ and $Q$ and the vacuum at the other finite places. For a vector $\xi$ of weight $\kappa$, the full datum is $\phi_\xi = v_{P_\xi} \otimes \Psi_{\mathrm{bl}} \otimes \mathrm{vac}$, with $v_{P_\xi}$ the Fock vector of the polynomial $P_\xi$ at the real places.

Lean: `New.DescentPair.charW` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.charV` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.blockDatum` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.fockDatum` (New/UpperBound/Objects/AuxiliaryPair.lean).

Section 4 writes out the block datum as a function on matrices.

### The conjugate kernel and the descent

**Definition (The conjugate kernel).** For $g$ in $U(W)(\mathbb{A})$ and a finite point $h$ of $U(V)$, the conjugate kernel is the linear form

$$\xi \mapsto \overline{\theta(\omega(g, h)\,\phi_{\bar\xi})}$$

on the vectors of weight $\kappa$. Here $\theta$ is the theta kernel of the pair with the characters $\nu_W$ and $\nu_V$, taken at the point $(g, 1, h)$. The component of $U(V)(\mathbb{A})$ is trivial at the infinite places.

Lean: `New.DescentPair.conjKernel` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.conjKernel_apply` (New/Determinant/Norms/VectorKernel.lean).

The datum of $\bar\xi$ appears so that the form is linear in $\xi$. The map $\xi \mapsto \phi_\xi$ is linear, and conjugation twice gives a linear form.

**Definition (The normalized descent).** For a form $\Xi$ on $V$, the normalized descent $\theta\Xi$ is the function on $U(W)(\mathbb{A})$ with

$$\theta\Xi(g) = \sum_c \frac{\mathrm{ck}(g, h_c)(\Xi(h_c))}{\#\mathrm{Aut}(h_c)},$$

the class sum for the level $K$ of the conjugate kernel $\mathrm{ck}$ at $g$ and $h$, applied to $\Xi(h)$.

Lean: `New.DescentPair.normalizedDescent` (New/UpperBound/Objects/AuxiliaryPair.lean), `New.DescentPair.normalizedDescent_apply` (New/Determinant/Norms/VectorKernel.lean).

The word "normalized" refers to the factor. Volume 9 shows that $\theta\Xi$ is $d_\kappa\,[K_0 : K]$ times the descent of $\Xi$ by the datum of the highest vector, where $d_\kappa$ is the dimension of the Weyl module. This factor comes back in Section 5.

### The vector kernel

The conjugate kernel at $(g, h)$ is a linear form on the vectors of weight $\kappa$. The Gram form $\langle\cdot, \cdot\rangle_G$ is nondegenerate, so the form is the pairing with one vector. That vector is the vector kernel.

**Definition (The vector kernel).** For $g$ in $U(W)(\mathbb{A})$ and a finite point $h$ of $U(V)$,

$$\theta_W(g, h) = G^{-1}\,\bigl(\overline{\mathrm{ck}(g, h)(e_i)}\bigr)_i,$$

where $e_i$ are the coordinate vectors and $G$ is the Gram matrix of the Weyl module over $\mathbb{C}$.

Lean: `New.DescentPair.vectorKernel` (New/Determinant/Norms/VectorKernel.lean).

**Lemma.** For every vector $\zeta$ of weight $\kappa$, $\langle\zeta, \theta_W(g, h)\rangle_G = \theta(\omega(g, h)\,\phi_{\bar\zeta})$, the theta kernel at $(g, 1, h)$. For every $\xi$, $\langle\theta_W(g, h), \xi\rangle_G = \mathrm{ck}(g, h)(\xi)$.

Lean: `New.DescentPair.gramForm_vectorKernel` (New/Determinant/Norms/VectorKernel.lean), `New.DescentPair.gramForm_vectorKernel_left` (New/Determinant/Norms/VectorKernel.lean).

*Proof.* The Gram matrix is positive definite, so its determinant is a unit. Then $\langle\zeta, G^{-1}u\rangle_G = \zeta^* u$. With $u_i = \overline{\mathrm{ck}(g, h)(e_i)}$ this is the conjugate of $\sum_i \zeta_i\,\mathrm{ck}(g, h)(e_i)$, which is $\overline{\mathrm{ck}(g, h)(\zeta)}$ by linearity. The definition of $\mathrm{ck}$ and $\bar{\bar z} = z$ give the first claim. The second claim is the conjugate of the first, since $\langle a, b\rangle_G = \overline{\langle b, a\rangle_G}$. $\square$

**Lemma (Equivariance of the kernel).** For rational $\gamma$ in $U(V)$, $k$ in the level $K$, $g$ in $U(W)(\mathbb{A})$ and finite $x$,

$$\theta_W(g, \gamma x k) = \chi_K(k)\,\rho(\gamma)\,\theta_W(g, x).$$

In particular $\theta_W(g, \gamma x) = \rho(\gamma)\,\theta_W(g, x)$ and $\theta_W(g, x k) = \chi_K(k)\,\theta_W(g, x)$.

Lean: `New.DescentPair.vectorKernel_equivariant` (New/Determinant/Norms/VectorKernel.lean), `New.DescentPair.vectorKernel_rational_mul` (New/Determinant/Norms/VectorKernel.lean), `New.DescentPair.vectorKernel_mul_level` (New/Determinant/Norms/VectorKernel.lean).

*Proof.* The character $\chi_K$ has finite order, so $|\chi_K(k)| = 1$. The representation $\rho$ preserves the Gram form. So $u \mapsto \chi_K(k)\rho(\gamma)u$ preserves the Gram form and is onto. It is enough to pair both sides with vectors $\chi_K(k)\rho(\gamma)v$. On the left, the pairing is $\overline{\mathrm{ck}(g, \gamma x k)(\chi_K(k)\rho(\gamma)v)}$ by the second part of the previous lemma. Volume 9 proves that the conjugate kernel satisfies $\mathrm{ck}(g, \gamma x k)(\chi_K(k)\rho(\gamma)v) = \mathrm{ck}(g, x)(v)$. This comes from the invariance of the theta kernel under rational points and from the action of $K$ on the datum. On the right, the pairing is $\langle v, \theta_W(g, x)\rangle_G$ by unitarity, which is the same conjugate. The two special cases take $k = 1$ and $\gamma = 1$. $\square$

**Definition (The kernel form).** For $g$ in $U(W)(\mathbb{A})$, the kernel form $\theta_W(g, \cdot)$ is the form on $V$ whose value at $h$ is $\theta_W(g, h)$.

Lean: `New.DescentPair.vectorKernelForm` (New/Determinant/Norms/VectorKernel.lean), `New.DescentPair.vectorKernelForm_apply` (New/Determinant/Norms/VectorKernel.lean).

The equivariance lemma gives the two conditions of a form: the law under rational points, and the law $\chi_K$ under the level. Smoothness follows from the law under the open group $K$.

**Theorem (The descent is a pairing with the kernel).** For every form $\Xi$ on $V$ and every $g$, $\theta\Xi(g) = \langle\theta_W(g, \cdot), \Xi\rangle$, the inner product of forms on $V$.

Lean: `New.DescentPair.normalizedDescent_eq_inner_vectorKernelForm` (New/Determinant/Norms/VectorKernel.lean).

*Proof.* By the definition, $\theta\Xi(g)$ is the class sum of $\mathrm{ck}(g, h)(\Xi(h))$. By the lemma above, this is the class sum of $\langle\theta_W(g, h), \Xi(h)\rangle_G$. The inner product of two forms on $V$ is the class sum of the Gram pairings of their values. $\square$

The kernel form also has a direct description on the adelic group of $V$. A form $\Xi$ on the definite space gives a function $\Xi^\natural(h) = \langle v^+, \rho(h_\infty^{-1})\,\Xi(h_f)\rangle_G$ on $U(V)(\mathbb{A})$, where $v^+$ is the highest vector. Lean writes $\Xi^\natural$ as `ofAlgForm`.

**Lemma.** For every $g$ in $U(W)(\mathbb{A})$ and $h$ in $U(V)(\mathbb{A})$, the function $\theta_W(g, \cdot)^\natural$ takes at $h$ the value $\theta(\omega(g, h)\,\phi_{v^+})$, the theta kernel of the datum of the highest vector.

Lean: `New.DescentPair.ofAlgForm_vectorKernelForm` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Write $h = (x, k)$ with $x$ real and $k$ finite. By definition the left side is $\langle v^+, \rho(x^{-1})\,\theta_W(g, k)\rangle_G$. Move $\rho(x^{-1})$ to the left as $\rho(x)$, since $\rho$ preserves the Gram form. By the first part of the lemma on the vector kernel, the pairing is the theta kernel of $\phi_{\overline{\rho(x)v^+}}$ at $(g, 1, k)$. Volume 9 shows that the real point $x$ acts on the datum of the highest vector as $\rho(x)$ acts on $v^+$, and $v^+$ is real. So this is the theta kernel of $\phi_{v^+}$ at $(g, x, k)$. $\square$

**Remark (Formalization).** The vector kernel uses the inverse of the Gram matrix over $\mathbb{C}$. Lean takes the inverse with `⁻¹` on matrices, which is $0$ for a singular matrix. The proof of the first lemma uses the positive definiteness of $G$ (`weylGramOver_posDef`) to show that the determinant is a unit. So the junk value does not occur.
