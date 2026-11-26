---
title: The pair and its kernel
lean:
  - Lib/Weil/DualPair/Defs.lean
  - Lib/Weil/DualPair/WeilAction.lean
  - Lib/Weil/DualPair/KernelLaws.lean
decls:
  - New.Space.hom
  - New.pairWeil
  - New.pairTheta
  - New.pairWeil_of_mem_Gamma
  - New.pairTheta_mul
  - New.pairThetaKer
  - New.pairWeil_integrated
  - New.exists_level_pairWeil
  - New.Modulus
  - New.modDatum
  - New.modKernel
  - New.modKernel_mul_stdLevel_left
  - New.modKernel_sum_right
  - New.modKernel_sum_left
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The pair and its kernel

This section defines the theta kernel of a unitary dual pair. The data live on the space $\operatorname{Hom}(S, T)$, the pair $G_S \times G_T$ acts through the Weil representation of that space, and two characters twist the action. The section then defines the data that the argument uses: a Fock vector at the real places, a function on matrices modulo an ideal $\mathfrak{m}$ at the primes of $\mathfrak{m}$, and the vacuum elsewhere. It ends with the seesaw identities. These say that on a direct sum of spaces the kernel is a product of kernels.

### The space of maps

Let $S$ have Gram matrix $J_S$, point $x_S$ and signs $s$, and let $T$ have $J_T$, $x_T$ and $t$. The classical tensor product $W = S^\vee \otimes T$ carries the hermitian form whose Gram matrix is a Kronecker product. In coordinates it is the following space.

**Definition (The space of maps).** $\operatorname{Hom}(S, T)$ is the space of $n' \times n$ matrices, with coordinates indexed by pairs $(i, j)$ of a row and a column. Its Gram matrix is $J_T \otimes (J_S^{-1})^{\mathsf{T}}$, its point is $x_T \otimes (x_S^{-1})^{\mathsf{T}}$, and the coordinate $(i, j)$ has the sign $t_i s_j$.

Lean: `New.Space.hom` (Lib/Weil/DualPair/Defs.lean).

The pair acts on maps by $\iota(g, h) : x \mapsto h x g^{-1}$. This is a homomorphism $\iota$ from $G_S \times G_T$ to the unitary group of $\operatorname{Hom}(S, T)$ (`New.G.onHom`).

### Characters and the twisted action

Let $\mathrm{U}(1)$ be the norm one torus of $E/F$. An automorphic character of $\mathrm{U}(1)$ is a continuous character $a$ of $\mathrm{U}(1)(\mathbb{A}_F) = \{z \in \mathbb{A}_E^\times : z \bar z = 1\}$ trivial on $\mathrm{U}(1)(F)$. The character $a$ has weight $\gamma$ and tame part $\psi$ if, for each $z$ with integral finite part, $a(z) = \prod_v z_v^{\gamma_v} \prod_w \psi_w(z \bmod w)$, with almost all $\psi_w$ trivial. The weight is the part of $a$ at the real places.

**Definition (The twisted Weil representation and its kernel).** Let $a, b$ be automorphic characters of $\mathrm{U}(1)$. For $(g, h) \in G_S \times G_T$ put
$$\omega_{a,b}(g, h) = a(\det h)\, b(\det g)^{-1}\, \omega(\iota(g, h)),$$
an operator on the data space $\mathcal{S}(\operatorname{Hom}(S, T))$, where $\omega$ is the Weil representation of [the Weil representation from a vacuum](/chapter/weil-representation/). The theta kernel of a datum $f$ is
$$\theta^{S,T}_{a,b}(f)(g, h) = \theta(\omega_{a,b}(g, h) f),$$
with $\theta$ the theta functional of $\operatorname{Hom}(S, T)$.

Lean: `New.pairWeil`, `New.pairTheta` (Lib/Weil/DualPair/Defs.lean).

The scalar $a(\det h) b(\det g)^{-1}$ is `New.pairChar`. It has modulus one, so $\omega_{a,b}$ preserves the inner product of data (`New.dataInner_pairWeil`). For the classical reason of the twist, see the notes: the Weil representation of $\mathrm{U}(W)$ restricted to $\mathrm{U}(S) \times \mathrm{U}(T)$ needs a choice of splitting characters, and $a, b$ play that part here.

**Lemma.** Let $g \in \Gamma_S$ and $h \in \Gamma_T$ be rational points. Then for every datum $f$ and every adelic matrix $x$, read as a vector on pairs of indices,
$$(\omega_{a,b}(g, h) f)(x) = f\big((h^{-1} \otimes g^{\mathsf{T}})\, x\big).$$

Lean: `New.pairWeil_of_mem_Gamma` (Lib/Weil/DualPair/WeilAction.lean).

*Proof.* The point $\iota(g, h)$ is rational, and on rational points the Weil representation acts by substitution. The characters $a, b$ are trivial on the rational determinants. $\square$

**Lemma (Translation law).** For a datum $f$ and points $p, q$ of $G_S \times G_T$,
$$\theta^{S,T}_{a,b}(f)(p q) = \theta^{S,T}_{a,b}(\omega_{a,b}(q) f)(p).$$

Lean: `New.pairTheta_mul` (Lib/Weil/DualPair/WeilAction.lean).

*Proof.* $\omega_{a,b}$ is a homomorphism. $\square$

**Definition (The theta kernel of the pair).** The action $\omega_{a,b}$ and the theta functional $\theta$ of $\operatorname{Hom}(S, T)$ form a theta kernel for $S$ and $T$ on $\mathcal{S}(\operatorname{Hom}(S, T))$, in the sense of [Definition](/decl/New.ThetaKernel/).

Lean: `New.pairThetaKer` (Lib/Weil/DualPair/WeilAction.lean).

The joint continuity is `New.continuous_pairWeil`. The invariance under $\Gamma_S \times \Gamma_T$ follows from the substitution lemma above and the invariance $\theta(\omega(\gamma) f) = \theta(f)$ of the theta functional under rational points of $\mathrm{U}(\operatorname{Hom}(S, T))$, which is Weil's theorem of [the Weil representation from a vacuum](/chapter/weil-representation/).

### The real and the finite part of a datum

At the real places the data space is a Fock space. For a Fock vector $v$ and a datum $f$, the source forms the datum $v \otimes f$ by integrating the Heisenberg action of the real points against $v$ (`New.Space.integrated`). The real points of the pair act on $v$ through the real Weil representation $\Omega_{\gamma, \gamma'}$ of the pair (`New.realPairWeil`). This is the action $\prod_w (\det y_w)^{\gamma_w} (\det x_w)^{-\gamma'_w}$ times the Fock operator of $z \mapsto y z x^{-1}$.

**Lemma.** Let $a$ have weight $\gamma$ and $b$ weight $\gamma'$, with any tame parts. For real points $x \in G_{S,\infty}$ and $y \in G_{T,\infty}$, taken with trivial finite parts, and for a Fock vector $v$ and a datum $f$,
$$\omega_{a,b}((x, 1), (y, 1))(v \otimes f) = (\Omega_{\gamma,\gamma'}(x, y) v) \otimes f.$$

Lean: `New.pairWeil_integrated` (Lib/Weil/DualPair/WeilAction.lean).

*Proof.* At a real point the characters act through their weights, and $\omega$ splits into the real action on $v$ and the trivial action on $f$. $\square$

The finite part $\mathcal{S}_f$ of the data space is the span of the translates of the vacuum under the finite Heisenberg operators.

**Lemma.** Let $f$ lie in $\mathcal{S}_f$. There are open subgroups $K \subset G_{S,f}$ and $K' \subset G_{T,f}$ such that $\omega_{a,b}((1, k), (1, k')) f = f$ for all $k \in K$ and $k' \in K'$.

Lean: `New.exists_level_pairWeil` (Lib/Weil/DualPair/WeilAction.lean).

*Proof.* The character $(k, k') \mapsto a(\det k') b(\det k)^{-1}$ is continuous with values in the circle. The circle has no small subgroups, so the character is trivial on a neighbourhood of $1$. On the finite part, the Weil representation of the finite points fixes $f$ on a neighbourhood of $1$. A neighbourhood of $1$ in the product of the two finite adelic groups contains a product of open subgroups. $\square$

### Data modulo an ideal

The argument chooses its finite data through a modulus.

**Definition (Modulus).** A modulus is a nonzero ideal $\mathfrak{m}$ of $\mathcal{O}_E$ such that no prime $w$ divides $\mathfrak{m}$ together with its conjugate $\bar w$.

Lean: `New.Modulus` (Lib/Weil/DualPair/Defs.lean).

A prime $w$ with $w \neq \bar w$ lies above a prime of $F$ that splits in $E$. So the primes of a modulus lie above split primes of $F$. At such a prime the unitary group is a general linear group, and a function of matrices modulo $\mathfrak{m}$ makes sense as a finite datum. The residue ring is $\mathcal{O}_E/\mathfrak{m}$, and $\mathfrak{m}$ has a finite set of prime divisors (`New.Modulus.places`). A function $\Psi$ on vectors modulo $\mathfrak{m}$ is read on finite adelic vectors $x$ by `New.Modulus.liftFn`: keep the components of $x$ at the primes of $\mathfrak{m}$, and if they are integral, take $\Psi$ of their reduction. Otherwise the value is $0$.

**Remark (Formalization).** The reduction map $\hat{\mathcal{O}}_E \to \mathcal{O}_E/\mathfrak{m}$ that `liftFn` uses is `New.Modulus.reduction`, a `choose` from an existence statement. The statement fixes it as a ring map that extends reduction on $\mathcal{O}_E$ and has kernel $t \hat{\mathcal{O}}_E$ for an integral idele $t$ equal to $1$ off $\mathfrak{m}$. By continuity these properties determine the map, so the choice does not matter. The source does not state this uniqueness, and the statements of this chapter do not need it.

**Definition (The kernel of a polynomial and a function modulo $\mathfrak{m}$).** Let $\mathfrak{m}$ be a modulus, $\Psi$ a function on $n' \times n$ matrices over $\mathcal{O}_E/\mathfrak{m}$, and $v$ a vector of the Fock space of $\operatorname{Hom}(S, T)$ at the real places. The datum $v \otimes \Psi \otimes \mathrm{vac}$ is the datum whose real part is $v$, whose part at the primes of $\mathfrak{m}$ is the lift of $\Psi$, and which is the vacuum at the other finite places. For a polynomial $P$ in variables $X_{w, i, j}$, indexed by a real place $w$, a row $i$ and a column $j$, let $v_P$ be its Fock vector, $P$ times the Gaussian. The kernel is
$$\theta^{S,T}_{a,b}[\Psi, P](g, h) = \theta\big(\omega_{a,b}(g, h)(v_P \otimes \Psi \otimes \mathrm{vac})\big).$$
With the standard characters of the signs of $S$ and $T$ it is written $\theta^{S,T}[\Psi, P]$.

Lean: `New.modDatum`, `New.modKernel`, `New.stdKernel` (Lib/Weil/DualPair/Defs.lean).

The part at the primes of $\mathfrak{m}$ is put in by the Schrödinger operator of a Schwartz-Bruhat function (`New.Space.schrodingerOp`). That operator is a `choose` of a generalized inverse, and its value is arbitrary on other inputs. The lift of $\Psi$ is Schwartz-Bruhat above the primes of $\mathfrak{m}$ (`New.Modulus.isSchwartzBruhat_liftFn`), so the kernel is the intended one.

### Laws of the kernel

The kernel transforms in a simple way under the integral points. Let $K_0 = \mathrm{Stab}(\hat{\mathcal{O}}^n)$ be the standard level of [adeles and Hermitian spaces](/chapter/adeles-hermitian-spaces/), and let $\bar k$ be the reduction of $k \in K_0$ modulo $\mathfrak{m}$.

**Lemma.** For $k$ in the standard level of $G_{S,f}$,
$$\theta^{S,T}_{a,b}[\Psi, P](g (1, k), h) = \theta^{S,T}_{a,b}[\Psi_k, P](g, h), \qquad \Psi_k(x) = b(\det k)^{-1} \Psi(x \bar k).$$
For $k'$ in the standard level of $G_{T,f}$ the same holds on the right, with $\Psi(\bar k'^{-1} y)$ and the factor $a(\det k')$.

Lean: `New.modKernel_mul_stdLevel_left`, `New.modKernel_mul_stdLevel_right` (Lib/Weil/DualPair/KernelLaws.lean).

*Proof.* By the translation law the kernel at $g(1, k)$ is the kernel of the moved datum. An integral point acts on the vacuum by the scalar of the characters, and on the function at $\mathfrak{m}$ by substitution of its reduction (`New.pairWeil_modDatum_stdLevel`). $\square$

The kernel also changes by a scalar under a twist of the characters: $\theta^{S,T}_{a\mu, b\mu'}[\Psi, P](g, h) = \mu(\det h) \mu'(\det g)^{-1} \theta^{S,T}_{a,b}[\Psi, P](g, h)$ (`New.modKernel_twist`).

### The seesaw identities

The seesaw principle starts from a direct sum. If $T = T_1 \oplus T_2$, then $\operatorname{Hom}(S, T) = \operatorname{Hom}(S, T_1) \oplus \operatorname{Hom}(S, T_2)$, and the Weil representation of a direct sum is the tensor product of the Weil representations. So the theta kernel of a product datum on $G_S \times (G_{T_1} \times G_{T_2})$ is the product of the two kernels with the same $g$. This is the key identity of Kudla's seesaw (Kudla 1984, Section 1).

**Theorem (Seesaw identity in the second space).** Let $T \oplus V$ be the orthogonal sum of $T$ and a space $V$ with $n_1$ coordinates. Let $\Psi$ and $\Psi'$ be functions on $n' \times n$ and $n_1 \times n$ matrices modulo $\mathfrak{m}$, and let $P$ and $P'$ be polynomials in the variables of the two blocks of rows. Let $b'$ be a third character. Then for $g \in G_S$, $h \in G_T$ and $h' \in G_V$,
$$\theta^{S, T \oplus V}_{a, b b'}[\Psi \otimes \Psi', P P'](g, h \oplus h') = \theta^{S,T}_{a,b}[\Psi, P](g, h)\, \theta^{S,V}_{a,b'}[\Psi', P'](g, h').$$
Here $(\Psi \otimes \Psi')(x) = \Psi(x_1) \Psi'(x_2)$ for the two blocks of rows $x_1, x_2$ of $x$.

Lean: `New.modKernel_sum_right` (Lib/Weil/DualPair/KernelLaws.lean).

**Theorem (Seesaw identity in the first space).** In the same way, for $S \oplus V$ in the first place, functions $\Psi, \Psi'$ on the two blocks of columns, polynomials $P, P'$ and a third character $a'$,
$$\theta^{S \oplus V, T}_{a a', b}[\Psi \otimes \Psi', P P'](g \oplus g', h) = \theta^{S,T}_{a,b}[\Psi, P](g, h)\, \theta^{V,T}_{a',b}[\Psi', P'](g', h).$$

Lean: `New.modKernel_sum_left` (Lib/Weil/DualPair/KernelLaws.lean).

*Proof of both.* The product datum of the two blocks is the datum of the product function and the product polynomial: the vacuum, the Schrödinger operators and the Fock vectors of polynomials all split over a block decomposition of the coordinates (`New.boxProd_integrated_schrodingerOp_liftFn`). The action $\omega_{a,b}$ and the theta functional are multiplicative for this product of data. The determinant of $h \oplus h'$ is $\det h \det h'$, which turns the character $b b'$ into the product of the two scalars. $\square$

The general form `New.modKernel_block_right` allows any splitting of the coordinates of $T$ compatible with the signs, with a block diagonal point and a block diagonal $h$. The versions with standard characters are `New.stdKernel_sum_right` and `New.stdKernel_sum_left`. Section 5 uses identities of this kind, through the hypothesis that two kernels agree up to weights.
