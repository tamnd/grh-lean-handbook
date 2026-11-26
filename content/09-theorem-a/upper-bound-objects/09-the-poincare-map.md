---
title: The Poincaré map
lean:
  - New/UpperBound/Objects/PoincareMap.lean
decls:
  - New.rieszMap
  - New.inner_rieszMap
  - New.Data.isEquivariant_sourceFn
  - New.Data.besselPeriod
  - New.Data.poincareAt
  - New.Data.inner_poincareAt
  - New.Data.poincareAt_smul
  - New.Data.integral_mul_poincareAt
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The Poincaré map

The second map of the proof starts with the Poincaré map $\mathcal{P}$. It sends a source form $\varphi$ on $X_0$ to a principal form on $Y_0$. The form $\mathcal{P}\varphi$ is the vector that represents a Bessel period of $\varphi$ in the Petersson product. The seesaw identity then compares $\iota_\vartheta(\mathcal{P}\varphi)$ with the composite lift of $\varphi$.

### A model case: the Riesz vector

Let $F$ be a finite dimensional complex inner product space, and let $\ell$ be a conjugate linear form on $F$. Then there is a unique $z \in F$ with $\ell(y) = \langle y, z \rangle$ for all $y$. If $\ell$ depends linearly on a parameter $\varphi$, then so does $z$. The Poincaré map is this construction with $F$ the principal forms on $Y_0$ and $\ell_\varphi(y)$ the Bessel period of $\varphi$ against $y$. The space $F$ is finite dimensional, since its forms have a fixed discrete series type and a fixed level.

### The Riesz map

**Definition (Riesz map).** For a linear map $B$ from $M$ to the conjugate linear forms on a finite dimensional inner product space $F$, the Riesz map sends $x$ to the unique $z \in F$ with $B(x)(y) = \langle y, z\rangle$.

Lean: `New.rieszMap` (New/UpperBound/Objects/PoincareMap.lean).

**Lemma.** For all $x$ and $y$, $\langle y, \mathrm{riesz}(B)(x) \rangle = B(x)(y)$.

Lean: `New.inner_rieszMap` (New/UpperBound/Objects/PoincareMap.lean).

*Proof.* The map $z \mapsto \langle \cdot, z\rangle$ from $F$ to its conjugate linear forms is injective, as the product is definite, and the two spaces have the same finite dimension. So it is bijective. The Riesz map is its inverse composed with $B$, and the identity follows. $\square$

### The grading of Y_0

The Bessel period uses a grading of $Y_0$. It is defined in [the first seesaw identity](/chapter/seesaw-identity-1/), whose file comes later in the order of the volume. PoincareMap.lean imports it because the Bessel group of the period is the Bessel group of this grading, while the rest of that chapter uses the objects of this one. The definition is stated here once.

**Definition (Grading of Y_k).** For $k \le 2\varrho + 1$, the grading of $Y_k$ presents $Y_k$ as $X_k$ plus a string of length $2\varrho + 1 - k$, with level $N$ and generic constant $-(j M \delta_E)^{-1}$. Here $j$ is the purely imaginary element of the Weil data and $\delta_E$ generates the different of $E$; the constant does not depend on $k$.

Lean: `New.Data.gradingY` (New/UpperBound/Seesaw/EdgePairEvaluation.lean).

The Bessel group $R_0(\mathbb{A})$ of this grading, its measure on $[R_0] = R_0(F)\backslash R_0(\mathbb{A})$, and the source function $\mathcal{W}_\varphi(uh) = \psi_U(u)\, t(\rho(h_\infty^{-1})\varphi(h_f))$ are from [Bessel periods and one step of unfolding](/chapter/bessel-periods/). Here $u$ is unipotent, $h$ lies in the unitary group of $X_0$, $\psi_U$ is the generic character and $t$ is a linear form on the Weyl module of the values of $\varphi$.

**Lemma.** For a source form $\varphi$, the function $\mathcal{W}_\varphi$ is continuous, left invariant under the rational points, and transforms by $\psi_U$ under the unipotent part.

Lean: `New.Data.isEquivariant_sourceFn` (New/UpperBound/Objects/PoincareMap.lean).

*Proof.* This is the general lemma of [Bessel periods](/chapter/bessel-periods/) for a grading with a string of odd length. Here the length is $2\varrho + 1$. $\square$

### The Bessel period and the map

Fix an archimedean point $g$ of the group $G_0$ of $Y_0$ and a linear form $t$.

**Definition (Bessel period).** For a source form $\varphi$ and a principal form $y$ on $Y_0$,
$$\mathcal{B}(\varphi, y) = \int_{[R_0]} \mathcal{W}_\varphi(r)\, \overline{y(r g)}\, dr.$$
It is linear in $\varphi$ and conjugate linear in $y$.

Lean: `New.Data.besselPeriod` (New/UpperBound/Objects/PoincareMap.lean).

The integral converges, because $\mathcal{W}_\varphi$ is equivariant and $\bar y$ is automorphic; this is the integrability lemma for equivariant functions in the same file.

**Definition (Poincaré map).** The Poincaré map $\mathcal{P} = \mathcal{P}_{g,t}$ is the Riesz map of the Bessel period.

Lean: `New.Data.poincareAt` (New/UpperBound/Objects/PoincareMap.lean).

**Theorem.** For a source form $\varphi$ and a principal form $y$ on $Y_0$,
$$\langle y, \mathcal{P}\varphi \rangle = \int_{[R_0]} \mathcal{W}_\varphi(r)\, \overline{y(r g)}\, dr.$$

Lean: `New.Data.inner_poincareAt` (New/UpperBound/Objects/PoincareMap.lean).

*Proof.* Apply the lemma on the Riesz map, and unfold the Bessel period. $\square$

**Lemma.** For $c \in \mathbb{C}$, $\mathcal{P}_{g, ct} = c\,\mathcal{P}_{g,t}$.

Lean: `New.Data.poincareAt_smul` (New/UpperBound/Objects/PoincareMap.lean).

*Proof.* The source function is linear in $t$. Test both sides against every $y$ with the theorem, and use that the product is conjugate linear in its first slot and linear in its second. $\square$

So a change of the Haar measure on $R_0(\mathbb{A})$, which multiplies the period by a positive constant, can be absorbed in $t$.

**Proposition.** Let $z$ be a form on $G_0$ of the conjugate type, right invariant under a subgroup $J$ of finite index in the chosen level $J_M$. Then
$$[J_M : J \cap J_M] \int_{[G_0]} z \cdot \mathcal{P}\varphi = \sum_{q} \int_{[R_0]} \mathcal{W}_\varphi(r)\, z(r g q)\, dr,$$
with $q$ over chosen representatives of $J_M / (J \cap J_M)$.

Lean: `New.Data.integral_mul_poincareAt` (New/UpperBound/Objects/PoincareMap.lean).

*Proof.* The sum of the translates of $z$ by the representatives has level $J_M$. Its conjugate $y$ is a principal form. Apply the theorem to $y$. On the left, the integral of the sum of translates is $[J_M : J \cap J_M]$ times the integral of $z \cdot \mathcal{P}\varphi$, as $\mathcal{P}\varphi$ has level $J_M$. $\square$

**Remark (Formalization).** The Poincaré map is defined by the Riesz map, not by a Poincaré series. The source does not write $\mathcal{P}\varphi$ as a sum over rational points in this file. The representatives in the proposition are taken by `Quotient.out`. The map depends on $g$, on $t$ and on the measure; for $t = 0$ it is $0$.
