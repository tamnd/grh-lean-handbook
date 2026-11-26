---
title: Edges and arrows
lean:
  - Lib/Weil/Lift.lean
  - Lib/DiscreteSeries/Theta/BlockRule.lean
decls:
  - New.ParamsCorrespond
  - New.jointHarmonicAt
  - New.jointHarmonic
  - New.isJointHarmonic_jointHarmonicAt
  - New.ParamsCorrespond.prod_eq_smul_jointHarmonic
  - New.IsHalfEdge
  - New.IsEdge
  - New.isEdge_of_isJointHarmonic
  - New.ParamsCorrespond.isEdge_jointHarmonic
  - New.IsArrow
  - New.formLift
  - New.IsEdge.isArrow
  - New.IsEdge.isForm_star_lift_swap
  - New.IsArrow.coe_formLift
  - New.IsArrow.formRep_formLift
  - New.IsArrow.inner_formLift_adjoint
  - New.IsEdge.exists_petersson_lift_eq_mul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Edges and arrows

Section 3 gives a lift $\mathcal{L}_\varphi$ from functions of rapid decay on $G_S$ to functions of moderate growth on $G_T$. This section finds data $\varphi$ for which the lift sends forms of one discrete series type to forms of another type. The real part of $\varphi$ is a product of joint harmonics, from [local theta in the Fock model](/chapter/local-theta/). The finite part is arbitrary.

In this section $e$ and $e'$ are kernels on the real points $G_{S,\infty}$ and $G_{T,\infty}$, and a form of type $e$ is a [form](/decl/New.Space.IsForm/) $y$ with $y * e = y$. For a doubled parameter $l$ of the signs $s$ the kernel of type $l$ is [the type kernel](/decl/New.typeKernel/) $e_l$. It is a product over the real places of formal degrees times conjugate matrix coefficients of discrete series, from [discrete series](/chapter/discrete-series/).

### Corresponding parameters

The local theta correspondence of discrete series with large gaps has a combinatorial shape, the block rule (Li 1990; Paul 1999). Fix a real place $w$, signs $s$ with $n$ entries and $t$ with $n'$ entries, and integers $\gamma, \gamma'$. Write parameters doubled, $l = 2\lambda$, so that all entries are integers. Put $l^\flat_i = l_i - 2\gamma' + n'$ and $l'^\flat_j = l'_j - 2\gamma + n$. For $d \geq 0$ let $[d]$ be the doubled block $\{d - 1, d - 3, \dots, 1 - d\}$.

**Definition (Block rule).** The parameters $l$ of $s$ and $l'$ of $t$ satisfy the block rule for $\gamma, \gamma'$ if:

1. $l$ and $l'$ have gap $500 (n + n')^3$: their entries are distinct, of the right parity, and entries of opposite signs are far apart;
2. if $n \leq n'$, the set of the $l'^\flat_j$ is the set of the $l^\flat_i$ together with the block $[n' - n]$, and symmetrically if $n' \leq n$;
3. if $l^\flat_i = l'^\flat_j > 0$ then $s_i = t_j$, and if $l^\flat_i = l'^\flat_j < 0$ then $s_i = -t_j$.

Lean: `New.IsBlockRule` (Lib/DiscreteSeries/Theta/BlockRule.lean).

**Definition (Corresponding parameters).** Let $\gamma, \gamma'$ be integer weights at the real places, and $l, l'$ families of doubled parameters of $s$ and $t$, one at each real place. They correspond if at every real place $w$ the parameters $l_w$ and $l'_w$ satisfy the block rule for $\gamma_w, \gamma'_w$.

Lean: `New.ParamsCorrespond` (Lib/Weil/Lift.lean).

The relation is symmetric. If $l, l'$ correspond for $s, t$ and $\gamma, \gamma'$, then $-l, -l'$ correspond for $-s, t$ and $n - \gamma, n' - \gamma'$.

At one place the block rule is equivalent to the matching condition of the local chapter, and then there is a joint harmonic: a nonzero polynomial on $n' \times n$ matrices that is harmonic for both groups and highest of the weights of the two lowest $K$-types. A joint harmonic is unique up to a scalar.

**Definition (The chosen joint harmonic).** For each real place $w$ let $\Phi_w$ be a joint harmonic for the oscillator pair with rows of signs $t$, columns of signs $s$ and shifts $\gamma_w, -\gamma'_w$, with parameters $l'_w$ and $-l_w$, if one exists. The chosen joint harmonic is $\Phi_{l,l'} = \prod_w \Phi_w$, each factor in the variables of the place $w$.

Lean: `New.jointHarmonicAt`, `New.jointHarmonic` (Lib/Weil/Lift.lean).

**Lemma.** If $l, l'$ correspond, then each $\Phi_w$ is a joint harmonic. If $P_w$ is any joint harmonic for the same data at each $w$, then $\prod_w P_w = c\, \Phi_{l,l'}$ for some $c \in \mathbb{C}$.

Lean: `New.isJointHarmonic_jointHarmonicAt`, `New.ParamsCorrespond.prod_eq_smul_jointHarmonic` (Lib/Weil/Lift.lean).

*Proof.* The block rule at $w$ gives the matching condition, and matching gives the existence of a joint harmonic. A joint harmonic is determined up to a scalar by its row weight and its harmonicity for both groups. Take the product of the scalars. $\square$

**Remark (Formalization).** `New.jointHarmonicAt` is `Classical.epsilon` of the predicate "is a joint harmonic". When no joint harmonic exists, which is the case when the parameters do not match, the value is an arbitrary polynomial and nothing is known about it. Every statement below that uses $\Phi_{l,l'}$ assumes that $l, l'$ correspond, so the junk value never enters. When they correspond, the choice is fixed only up to a nonzero scalar. All statements below are invariant under such a scalar, since the conditions on an edge are homogeneous.

### Half edges and edges

Let $\Omega$ be an action of $G_{S,\infty} \times G_{T,\infty}$ on a Fock space by bounded operators. A theta kernel has real part $\Omega$ if $\omega((x, 1), (y, 1))(v \otimes f) = (\Omega(x, y) v) \otimes f$ for all real points $x, y$, Fock vectors $v$ and data $f$. By Section 2, the kernel of $\operatorname{Hom}(S, T)$ with characters of weights $\gamma, \gamma'$ has real part $\Omega_{\gamma,\gamma'}$.

**Definition (Half edge).** A Fock vector $\Phi$ is a half edge for $\Omega$ from $e$ to $e'$ if:

1. $e$ is a [cusp kernel](/decl/New.IsCuspKernel/) of order $0$;
2. the zeta integral $\int_{G_{S,\infty}} \langle \Phi, \Omega(x, 1)\Phi \rangle\, \overline{e(x)}/e(1)\, dx$ is not zero;
3. for every theta kernel with real part $\Omega$, every form $y$ of type $e$ and every finite datum $f$, if the lift $\mathcal{L}_{\Phi \otimes f}\, y$ is right invariant under an open subgroup of $G_{T,f}$, then it is a form of type $e'$;
4. for every polynomial Fock vector $v$ there is a continuous function $\alpha$ of compact support on $G_{T,\infty}$ such that, for all theta kernels with real part $\Omega$, all forms $y$ of type $e$ and all $f$,
$$\mathcal{L}_{v \otimes f}\, y = \alpha * \mathcal{L}_{\Phi \otimes f}\, y,$$
the [real convolution](/decl/New.realConv/) of the lift with $\Phi$.

Lean: `New.IsHalfEdge` (Lib/Weil/Lift.lean).

**Definition (Edge).** $\Phi$ is an edge for $\Omega$ from $e$ to $e'$ if it is a half edge from $e$ to $e'$, and also a half edge for $(y, x) \mapsto \Omega(x, y)$ from $\bar e'$ to $\bar e$.

Lean: `New.IsEdge` (Lib/Weil/Lift.lean).

Conditions 3 and 4 quantify over all theta kernels and all spaces with the given signs. So an edge is a local statement at the real places. It does not depend on $S$, $T$, the characters or the finite datum.

**Theorem (Joint harmonics are edges).** Let $s$ and $t$ be nonempty. If $l, l'$ correspond for $\gamma, \gamma'$, then $\Phi_{l,l'}$ is an edge for $\Omega_{\gamma,\gamma'}$ from $e_l$ to $e_{l'}$.

Lean: `New.isEdge_of_isJointHarmonic`, `New.ParamsCorrespond.isEdge_jointHarmonic` (Lib/Weil/Lift.lean).

*Proof sketch.* At each place, $\Omega_{\gamma,\gamma'}$ acts on pure tensors through a pair of commuting oscillator representations, twisted by powers of the determinant. A joint harmonic is a highest vector of the lowest $K$-type for both groups. By [local theta in the Fock model](/chapter/local-theta/), at each place the inner product of $\Phi_w$ with its image under the integrated operator of the local kernel has positive real part. The zeta integral is the product of these local factors divided by a nonzero value of the kernel, which gives 2. For 3 and 4, a convolution on the real points of the lift becomes an integrated operator on the Fock vector, and the proof uses that $\Phi$ is highest of the lowest $K$-type for both groups. The reverse half edge uses $\bar e_l = e_{-l}$ and the same argument with the groups exchanged. $\square$

The proof uses the gap condition in 1 of the block rule to show that the type kernels are cusp kernels of order $0$.

### Arrows

**Definition (Arrow).** A datum $\varphi$ is an arrow from $e$ to $e'$ for a theta kernel if every form $y$ of type $e$ on $G_S$ is of rapid decay and its lift $\mathcal{L}_\varphi y$ is a form of type $e'$ on $G_T$.

Lean: `New.IsArrow` (Lib/Weil/Lift.lean).

**Theorem (Edges give arrows).** Let $\Phi$ be an edge for $\Omega_{\gamma,\gamma'}$ from $e$ to $e'$. Let $a, b$ be automorphic characters of weights $\gamma, \gamma'$, and let $f$ lie in the finite part $\mathcal{S}_f$ of the data space of $\operatorname{Hom}(S, T)$. Then for the kernel $\theta^{S,T}_{a,b}$, the datum $\Phi \otimes f$ is an arrow from $e$ to $e'$, and for the swapped kernel it is an arrow from $\bar e'$ to $\bar e$. In particular, for every form $y'$ of type $e'$ on $G_T$, the descent $\overline{\mathcal{L}'_{\Phi \otimes f}\, \bar y'}$ is a form of type $e$ on $G_S$.

Lean: `New.IsEdge.isArrow`, `New.IsEdge.isForm_star_lift_swap` (Lib/Weil/Lift.lean).

*Proof.* Since $e$ is a cusp kernel, every form of type $e$ is of rapid decay ([automorphic forms](/chapter/automorphic-forms/)). By Section 2, $f$ is fixed by open subgroups $K \subset G_{S,f}$ and $K' \subset G_{T,f}$. The real points act on the real part only, so $\Phi \otimes f$ is fixed by $K$ and $K'$ as well. By the right translation law, the lift of $y$ is right invariant under $K'$. Condition 3 of the half edge then says that the lift is a form of type $e'$. The swapped statement is the same argument with the second half edge, and the descent is the conjugate of a form of type $\bar e$. $\square$

**Definition (The lift on forms).** Let $\mathcal{F}(S, e)$ be the space of forms of type $e$. The lift on forms is the bilinear map $\mathcal{L}^{\mathrm{f}}$ from data and $\mathcal{F}(S, e)$ to $\mathcal{F}(T, e')$ that sends $(\varphi, y)$ to $\mathcal{L}_\varphi y$ whenever $\varphi$ is an arrow from $e$ to $e'$.

Lean: `New.formLift` (Lib/Weil/Lift.lean).

**Lemma.** Let $\varphi$ be an arrow from $e$ to $e'$.

1. $\mathcal{L}^{\mathrm{f}}_\varphi y = \mathcal{L}_\varphi y$ for every form $y$ of type $e$.
2. For finite points $k \in G_{S,f}$ and $k' \in G_{T,f}$, the right translate of $\mathcal{L}^{\mathrm{f}}_\varphi y$ by $k'$ is $\mathcal{L}^{\mathrm{f}}_{\omega((1,k),(1,k'))\varphi}$ of the right translate of $y$ by $k$.
3. If $\varphi$ is also an arrow from $\bar e'$ to $\bar e$ for the swapped kernel, then for forms $y$ of type $e$ and $x$ of type $e'$, $\langle \mathcal{L}^{\mathrm{f}}_\varphi y, x \rangle = \langle y, \overline{\mathcal{L}'^{\mathrm{f}}_\varphi \bar x} \rangle$.

Lean: `New.IsArrow.coe_formLift`, `New.IsArrow.formRep_formLift`, `New.IsArrow.inner_formLift_adjoint` (Lib/Weil/Lift.lean).

*Proof.* 1 holds by construction. 2 is the equivariance lemma of Section 3 with $k$ and $k'$ placed at the finite places. 3 is the adjointness theorem of Section 3, applied to $y$ and $x$, which are of rapid decay. $\square$

**Remark (Formalization).** `New.formLift` is built from left inverses of the inclusions of the rapid functions and of the forms into all functions. These left inverses are chosen and have no meaning off the subspaces. So for a datum $\varphi$ that is not an arrow, $\mathcal{L}^{\mathrm{f}}_\varphi y$ is a form of type $e'$ with no relation to the lift of $y$. Every statement that uses `New.formLift` in this chapter and in its users carries a hypothesis `IsArrow`, and then statement 1 identifies the value. The map is linear in $\varphi$ on all data, but the identity 1 is proved only on arrows.

### Proportionality of periods

Different polynomial Fock vectors give the same Petersson products up to a scalar that does not depend on the global data.

**Theorem (The polynomial factor).** Let $\Phi$ be an edge for $\Omega_{\gamma,\gamma'}$ from $e$ to $e'$. There is a linear functional $\kappa$ on polynomials in the variables $X_{w,i,j}$ with the following property. For all spaces $S, T$ of signs $s, t$, all characters $a, b$ of weights $\gamma, \gamma'$, all $f \in \mathcal{S}_f$, all polynomials $P$ and all forms $y$ of type $e$ and $y'$ of type $e'$,
$$\langle y', \mathcal{L}_{v_P \otimes f}\, y \rangle_T = \kappa(P)\, \langle y', \mathcal{L}_{\Phi \otimes f}\, y \rangle_T,$$
and the same factor $\kappa(P)$ relates $\langle \bar y, \mathcal{L}'_{v_P \otimes f}\, \bar y' \rangle_S$ to $\langle \bar y, \mathcal{L}'_{\Phi \otimes f}\, \bar y' \rangle_S$.

Lean: `New.IsEdge.exists_petersson_lift_eq_mul` (Lib/Weil/Lift.lean).

*Proof.* For a monomial $m$, condition 4 of the half edge gives a function $\alpha_m$ with $\mathcal{L}_{v_m \otimes f}\, y = \alpha_m * \mathcal{L}_{\Phi \otimes f}\, y$ for all data. Move the convolution to $y'$ in the Petersson product. Since $y'$ is a form of type $e'$ and $e'$ is a minimal idempotent, the real translates of $y'$ integrated against $\alpha_m$ give the scalar $c(m) = \int \alpha_m(x)\, \overline{e'(x)}/e'(1)\, dx$ times $y'$ in the product. Define $\kappa$ on the basis of monomials by $\kappa(m) = c(m)$, and extend it linearly. The lift is linear in the polynomial, so the identity holds for all $P$. The second identity follows from the first, since the two products are equal by the transposition theorem of Section 3. $\square$

**Remark (Formalization).** The theorem gives $\kappa$ but says nothing about its values. It does not show that $\kappa(P) \neq 0$ for any $P$, and it does not compute $\kappa$. Users that need a nonzero factor must prove it in another way. The docstring of the file says that the lift is shown to carry forms of one type to forms of another "without Howe duality". So no statement here identifies the lift of an irreducible representation, and the multiplicity one input of the classical theory (Howe 1989) is not used.
