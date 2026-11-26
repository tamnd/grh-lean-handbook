---
title: The restriction map and the first path
lean:
  - New/Determinant/AuxiliaryForms/FirstPath.lean
decls:
  - New.Data.gridChar_detFin_eq_one
  - New.Data.pairWeil_gridChar_modDatum_eq_self
  - New.Data.formRep_transposedChain_eq_self
  - New.Data.triangleRep_weightedChain_eq_self
  - New.Data.integral_transposedChain_mul_weightedChain
  - New.Data.eq_zero_of_weightedChain_triangleLift_eq_zero
  - New.Data.map_transposedChain_le_gridLevelForms
  - New.Data.gridLevelForms_eq_map_transposedChain
  - New.Data.exists_forall_diagonalPeriodForm_ne_zero
  - New.Data.IsFlatRestriction
  - New.Data.exists_isFlatRestriction
  - New.Data.exists_isFlatRestriction_range_eq_top
  - New.Data.IsFlatRestriction.integral_lowerChainUpTo
  - New.Data.exists_isPathDatum_integral_eq
  - New.Data.exists_isPathDatum_first
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The restriction map and the first path

The first path of the grids has the nodes $\tilde Y^m_0, \dots, \tilde Y^0_0$ and $Y_0, \dots, Y_m$. These are the first columns $(z, 0, i)$ of the two grids: $z = $ false gives $Y_i$ and $z = $ true gives $\tilde Y^i_0$. This section builds a map $\mathrm{res}^\flat$ from the forms of level $\mathfrak b$ on the definite space $\tilde Y^m_0$ onto the principal forms on $Y_0$. It then writes the pairing of the chain of lifts of $\mathrm{res}^\flat\varphi$ as a period on the first path.

### Background in one line each

- Grid forms, triangle forms, the moduli $\mathfrak m_0 = \varpi Q$ (for $Y$) and $\mathfrak b = \varpi^b$ (for $\tilde Y$) of a first column, the indices $n_{\mathfrak n}$ that weight each lift, the edge characters $\chi$ and the data $\mathrm{modDatum}$ ([seesaw squares and grid paths](/chapter/seesaw-squares/)).
- The transposed chain $T_i = $ [transposedChain](/decl/New.Data.transposedChain/) $\vartheta\,z\,i$ composes the weighted transposed lifts from node $m$ down to node $i$. The chain $W_i$ = [weightedChain](/decl/New.Exchange.weightedChain/) composes the weighted lifts from node $0$ up to node $i$.
- A pair of finite integral points acts on $\mathrm{modDatum}$ through their reductions modulo $\mathfrak n$ and the two characters on the determinants (`New.pairWeil_modDatum_stdLevel`, [theta kernels and gauges](/chapter/theta-kernels-gauges/)).
- Lifts along an arrow are equivariant, and a lift and its transposed lift are adjoint for the integrals over the quotients ([seesaw squares and grid paths](/chapter/seesaw-squares/)).
- The triangle of the grid of $\tilde Y$ exists ([exists_isTriangle](/decl/New.Data.exists_isTriangle/)), and its weighted chain is injective on the base forms ([IsTriangle.eq_zero_of_weightedChain_eq_zero](/decl/New.Exchange.IsTriangle.eq_zero_of_weightedChain_eq_zero/)).
- From [grids, columns and turns](/chapter/grids-paths-turns/): (a) at every real point $g$ there is a linear map $P_g$ from the forms of level $\mathfrak b$ on $\tilde Y^0_0$ to the principal forms on $Y_0$ with $\langle y, P_g\varphi\rangle = \mathcal P_{\vartheta, g}(\bar y, \varphi)$ for every twist $\vartheta$ and every $y$ of level $\mathfrak m_0$, where $\mathcal P$ is the period `diagonalPeriodForm`; (b) there are a constant $C$ and path data $\Psi_\vartheta$ on the first path with $\mathcal P_{\vartheta, g}(T_0 y', \Theta^\flat\varphi) = C\cdot\mathrm{gridPeriod}(\Psi, g)(\vartheta, y', \varphi)$. This chapter is being written now, so we give only the chapter link.

### Invariance of the chains

**Lemma.** Let $u$ be a finite integral point of a unitary group with $u \equiv 1 \bmod \mathfrak n$, where $\mathfrak n$ is the modulus of the first column of grid $z$. Then the edge character $\chi$ of the edge $(i, i+1)$ has $\chi(\det u) = 1$.

Lean: `New.Data.gridChar_detFin_eq_one` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* The tame part of $\chi$ is trivial at the places outside $\mathfrak n$, which are not chosen places and not places of $Q$. So $\chi(\det u)$ is the character of the tame part at $\det(u \bmod \mathfrak n) = \det 1 = 1$. $\square$

**Lemma.** A pair $(u, u')$ of finite integral points at the nodes $i$ and $i + 1$, both $\equiv 1 \bmod \mathfrak n$, fixes $\mathrm{modDatum}(\Psi, v)$ under the Weil representation times the edge characters.

Lean: `New.Data.pairWeil_gridChar_modDatum_eq_self` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* The pair acts through its reductions, which are $1$, and through $\chi(\det u)$ and $\chi(\det u')$, which are $1$ by the previous lemma. $\square$

**Lemma.** For $i < m$ and a form $\varphi$ at node $m$, right translation by $u \equiv 1 \bmod\mathfrak n$ fixes $T_i\varphi$. For $0 < i \le m$ and a form $y$ at node $0$, right translation by $u \equiv 1 \bmod \mathfrak n$ fixes $W_i y$.

Lean: `New.Data.formRep_transposedChain_eq_self`, `New.Data.triangleRep_weightedChain_eq_self` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* $T_i$ ends with the transposed lift from node $i+1$ to node $i$, and $W_i$ ends with the lift from node $i - 1$ to node $i$. The pair $(u, 1)$, or $(1, u)$, fixes the datum of that edge by the previous lemma. Equivariance of the lift along the arrow gives that $u$ fixes every image. The weight is a scalar and commutes with translation. $\square$

### Transposition

**Lemma (Transposition identity).** For $i \le m$, a triangle form $y$ at node $0$ and a grid form $\varphi$ at node $m$,

$$\int T_i\varphi \cdot W_i y\,d\mu_i = \int T_0\varphi\cdot y\,d\mu_0.$$

Lean: `New.Data.integral_transposedChain_mul_weightedChain` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* Induction on $i$. For $i = 0$ both sides agree. For the step, $W_{i+1}y = n_i\,\theta_i(W_i y)$ and $T_i = n_i\,\theta_i^{\top}\circ T_{i+1}$, with the same weight $n_i$ on the edge. The adjointness of $\theta_i$ and $\theta_i^\top$ moves the lift to the other side:

$$\int T_{i+1}\varphi\cdot n_i\theta_i(W_i y) = \int n_i\theta^\top_i(T_{i+1}\varphi)\cdot W_i y = \int T_i\varphi\cdot W_i y.$$

The induction hypothesis finishes. $\square$

**Lemma.** The weighted chain $W_m$ of the grid of $\tilde Y$, for the trivial twist, is injective on the conjugate forms of level $\mathfrak b$ on $\tilde Y^0_0$.

Lean: `New.Data.eq_zero_of_weightedChain_triangleLift_eq_zero` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* Take the triangle of the grid of $\tilde Y$. Its weighted chain is injective on the base forms. $\square$

**Theorem ($\Theta^\flat$ is onto).** Let $\Theta^\flat = T_0$ for the grid of $\tilde Y$ and the trivial twist, and $\mathcal F_{\mathfrak b}^i$ the forms of level $\mathfrak b$ on $\tilde Y^i_0$. Then $\Theta^\flat(\mathcal F_{\mathfrak b}^m) \subseteq \mathcal F_{\mathfrak b}^0$, and equality holds.

Lean: `New.Data.map_transposedChain_le_gridLevelForms`, `New.Data.gridLevelForms_eq_map_transposedChain` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* The inclusion is the invariance lemma with $i = 0 < m$. For equality, the space $\mathcal F_{\mathfrak b}^m$ is finite dimensional, so the image $I$ is closed and $\mathcal F_{\mathfrak b}^0 = I \oplus (I^\perp \cap \mathcal F_{\mathfrak b}^0)$. Let $z \in I^\perp\cap\mathcal F_{\mathfrak b}^0$. Put $y = \bar z$, a conjugate form of level $\mathfrak b$, $U = W_m y$ and $\varphi = \bar U$. By the invariance lemma, $\varphi \in \mathcal F_{\mathfrak b}^m$. The transposition identity with $i = m$, where $T_m$ is the identity, gives

$$\langle U, U\rangle = \int \varphi\, U = \int y\cdot\Theta^\flat\varphi = \langle z, \Theta^\flat\varphi\rangle = 0.$$

So $U = 0$, and $y = 0$ by injectivity. So $z = 0$. $\square$

### The restriction map

**Lemma.** There is a real point $g_0$ of the unitary group of $\tilde Y^0_0$ such that for every principal form $y \ne 0$ on $Y_0$ some $\varphi \in \mathcal F_{\mathfrak b}^m$ has $\mathcal P_{1, g_0}(\bar y, \Theta^\flat\varphi) \ne 0$.

Lean: `New.Data.exists_forall_diagonalPeriodForm_ne_zero` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* Take $g_0$ from the criterion of Section 6. Suppose all these periods are $0$ for some $y \ne 0$. Every $\psi \in \mathcal F_{\mathfrak b}^0$ is $\Theta^\flat\varphi$ for some $\varphi \in \mathcal F^m_{\mathfrak b}$. The Petersson product $\langle y, \psi((\cdot\oplus 1)g_0)\rangle$ is by definition the period $\mathcal P_{1,g_0}(\bar y, \psi)$, so it is $0$. The criterion gives $y = 0$, a contradiction. $\square$

**Definition (Flat restriction).** A linear map $r : \mathcal F_{\mathfrak b}^m \to$ (principal forms on $Y_0$) is a *flat restriction at $g$* if for every $\varphi$, every twist $\vartheta$ and every form $y$ on $Y_0$ of level $\mathfrak m_0(\vartheta)$,

$$\langle y, r\varphi\rangle = \mathcal P_{\vartheta, g}(\bar y, \Theta^\flat\varphi).$$

Lean: `New.Data.IsFlatRestriction` (New/Determinant/AuxiliaryForms/FirstPath.lean).

**Lemma.** At every real point $g$ there is a flat restriction.

Lean: `New.Data.exists_isFlatRestriction` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* Take $r = P_g\circ\Theta^\flat$, with $P_g$ from (a) of the background. $\Theta^\flat$ maps into $\mathcal F_{\mathfrak b}^0$ by the theorem above. $\square$

**Theorem (res$^\flat$ is onto).** There are a real point $g$ and a flat restriction $r$ at $g$ with range all principal forms on $Y_0$.

Lean: `New.Data.exists_isFlatRestriction_range_eq_top` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* Take $g = g_0$ and $r$ from the previous two lemmas. The target is finite dimensional, so it suffices that $y \perp \mathrm{range}\,r$ gives $y = 0$. If $y \ne 0$, choose $\varphi$ with $\mathcal P_{1, g}(\bar y, \Theta^\flat\varphi) \ne 0$. Principal forms have level $J_M \supseteq$ the level $\mathfrak m_0$ of the trivial twist, so the definition applies with $\vartheta = 1$: $0 = \langle y, r\varphi\rangle = \mathcal P_{1,g}(\bar y, \Theta^\flat\varphi) \ne 0$. This is a contradiction. $\square$

### The period on the first path

**Lemma.** Let $r$ be a flat restriction at $g$, $\vartheta$ a twist, $y'$ a conjugate form on $Y_m$ and $\varphi \in \mathcal F_{\mathfrak b}^m$. Then

$$\int y'\cdot\Theta_\vartheta(r\varphi)\,d\mu = \mathcal P_{\vartheta, g}(T_0y', \Theta^\flat\varphi),$$

with $\Theta_\vartheta$ = `lowerChainUpTo` $\vartheta$ $m$ and $T_0$ the transposed chain of the grid of $Y$ at $\vartheta$.

Lean: `New.Data.IsFlatRestriction.integral_lowerChainUpTo` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* The chain $\Theta_\vartheta$ is the weighted chain $W_m$ of the grid of $Y$, once the weight is written as the order of the group $GL$ modulo the level modulus. The transposition identity with $i = m$ gives $\int y'\cdot W_m(r\varphi) = \int T_0y'\cdot r\varphi$. By the invariance lemma $T_0y'$ is fixed by the points $\equiv 1 \bmod \mathfrak m_0$, so $\overline{T_0y'}$ has level $\mathfrak m_0$. The definition of a flat restriction, applied to $\overline{T_0 y'}$, gives $\int T_0y'\cdot r\varphi = \mathcal P_{\vartheta,g}(T_0y', \Theta^\flat\varphi)$. $\square$

**Theorem (Path datum on the first path).** There are path data $\Psi_\vartheta$ on the first path, with values sums of at most $\mathrm{edgeMatrixCountBound}(\vartheta)^{2m}$ roots of unity ([IsPathDatum](/decl/New.Data.IsPathDatum/)), a constant $\alpha$, a real point $g$ and a map $r$ onto the principal forms such that for all $\vartheta$, $y'$, $\varphi$,

$$\int y'\cdot\Theta_\vartheta(r\varphi)\,d\mu = \alpha\cdot\mathrm{gridPeriod}(\text{first path}, \Psi, g)(\vartheta, y', \varphi).$$

The first part holds with the same $\Psi$ and $\alpha$ for every flat restriction at every $g$.

Lean: `New.Data.exists_isPathDatum_integral_eq`, `New.Data.exists_isPathDatum_first` (New/Determinant/AuxiliaryForms/FirstPath.lean).

*Proof.* Take $C$ and $\Psi$ from (b) of the background and put $\alpha = C$. For a flat restriction at $g$, the previous lemma and (b) give the identity. Take $g$ and $r$ from the theorem that res$^\flat$ is onto. $\square$

**Remark (Formalization).** The map $r$ is not unique. Its pairings with the forms of level $\mathfrak m_0(\vartheta)$ fix it, as these contain the principal forms and the Petersson product is nondegenerate on them. The source gives $r$ by an existential. The constant $\alpha$ may be $0$ as far as this file shows. It is the product of the constants $\kappa_i$ with $n_{\mathfrak m_0}(Y_i) = \kappa_i\cdot\mathrm{levelIndex}$, chosen by `choose` in [grids, columns and turns](/chapter/grids-paths-turns/). The spanning theorem does not need $\alpha \ne 0$.
