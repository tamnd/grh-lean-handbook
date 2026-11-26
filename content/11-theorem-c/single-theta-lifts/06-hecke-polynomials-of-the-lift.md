---
title: Hecke polynomials of the lift
lean:
  - New/Determinant/Norms/AdjointThetaLift.lean
  - New/UpperBound/Objects/AuxiliaryPair.lean
  - New/OneLift/HeckeValues/CharacterLift.lean
  - New/Spanning/Multiplicities/HeckeEigensystems.lean
  - Lib/Weil/Unramified/HeckeTransfer.lean
decls:
  - New.DescentPair.hasHeckePolynomial_thetaLift
  - New.DescentPair.heckePolyOnForms
  - New.DescentPair.heckePolyOnForms_eq_smul
  - New.DescentPair.rankDiff
  - New.DescentPair.liftHeckeRoot
  - New.DescentPair.HasLiftHeckePolynomial
  - New.DescentPair.heckePolyOnForms_liftHeckeRoot_eq_zero
  - New.Data.heckeOperator
  - New.Data.eigenPart
  - New.Data.hasHeckePolynomial_of_mem_eigenPart
  - New.Data.iSup_eigenPart_eq_top
  - New.Data.hasLiftHeckePolynomial_singleLift
  - New.Data.heckePolyOnForms_liftHeckeRoot_singleLift_eq_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hecke polynomials of the lift

This section computes the Hecke polynomials of the lifted forms $\Theta_{j,\vartheta}\,y$ at the split places away from $M$ and $Q$. The result is a factorization. The Hecke polynomial of the lift is a product of $t$ explicit linear factors and a rescaled Hecke polynomial of $y$. One linear factor has a root $x_w$ that does not depend on $y$. So the Hecke polynomial operator at $x_w$ kills every lift. The chapter [the height of one lift determinant](/chapter/lift-volume-height/) uses this to separate the lifts from the other forms on $V_j$.

The input is the transfer theorem for Hecke polynomials through a theta lift, from [Iwahori exponents, Satake and the chain lemma](/chapter/iwahori-satake/) of Volume 5. The section also uses two lemmas from [character lifts and tested forms](/chapter/character-lifts/). They are general facts on descent pairs, and the next chapter states them.

### Hecke polynomials

Recall the notions of Volume 5. Let $w$ be a split finite place of $E$, with $w \neq \bar w$, and let $q = q_w$. On a representation of the finite points of a unitary group of rank $N$, the Hecke operators $T_{w,i}$ are the operators of the double cosets of $\mathrm{diag}(\varpi_w 1_i, 1_{N-i})$. The Hecke polynomial operator is

$$H_w(X) = \sum_{i \leq N}(-X)^i\,q^{i(i-1)/2}\,T_{w,i}.$$

A vector $y$ has the Hecke polynomial $p : \mathbb{C} \to \mathbb{C}$ at $w$ if $y$ is spherical at $w$ and $H_w(X)\,y = p(X)\,y$ for every $X \in \mathbb{C}$. For a sequence $z$ of complex numbers, write $H_z(X) = \sum_{i \leq N}(-X)^i\,q^{i(i-1)/2}\,z_i$ for the scalar polynomial with the eigenvalues $z$.

For a character $c$ of $[U(1)]$ unramified at $w$ and a rank $N$, Volume 5 writes $\alpha_N(c)$ for its Frobenius value at $w$. For the $j$-th descent pair $O$ write

$$\alpha = \alpha_r(\nu_W), \qquad \beta = \alpha_{r+t}(\nu_V).$$

The difference of the ranks of the pair is $t = \dim V - \dim W$.

Lean: `New.DescentPair.rankDiff` (New/UpperBound/Objects/AuxiliaryPair.lean).

### The transfer for a descent pair

**Theorem (Hecke polynomial of the lift of a pair).** Let $l$ fit the pair $O$. Let $w$ be a split place such that $w$ and $\bar w$ are not places of $M$ or $Q$. Let $y$ be a form of type $l$ on $W$ with the Hecke polynomial $p$ at $w$. Then the function of $\Theta_W\,y$ on the finite points of $U(V)$ has the Hecke polynomial

$$X \mapsto \prod_{i < t}(1 - q^i\alpha X)\cdot p\bigl(q^t\alpha\beta^{-1}X\bigr)$$

at $w$.

Lean: `New.DescentPair.hasHeckePolynomial_thetaLift` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The plan is to apply the transfer theorem of Volume 5 (`New.SiegelWeil.hasHeckePolynomial_formLift`). It needs four inputs.

1. The ranks. The rank of $V$ is the rank of $W$ plus $t$. This holds since $r < n$ for a descent pair.
2. The characters are unramified at $w$. For $\nu_W$ this follows from its weight. For $\nu_V$ the tame part is trivial at the places off $M$ and $Q$, and $w$, $\bar w$ are such places.
3. The datum is the vacuum at $w$. The block datum $\Psi_{\mathrm{bl}}$ lives at the places of $\pi_M Q$, and the datum is the vacuum at every other place. The places of the modulus and their conjugates do not meet $\{w\}$. So the projection of $\phi_{v^+}$ to the place $w$ is $\phi_{v^+}$ itself.
4. The datum is an arrow for the theta kernel, by the lemma of Section 3.

The transfer theorem gives the Hecke polynomial of the function of the lift. The passage from the function to the algebraic form (`New.hasHeckePolynomial_toAlgForm_iff`) keeps the Hecke polynomial. $\square$

The first factor $\prod_{i<t}(1 - q^i\alpha X)$ is the Hecke polynomial of a fixed vector of rank $t$, rescaled by $\alpha$. This is the Example on fixed vectors of Volume 5. So the lift adds $t$ Satake parameters that do not depend on $y$ to the $r$ parameters of $y$, which are rescaled. This is the classical shape of the unramified theta correspondence in the stable range.

### The Hecke polynomial on forms on $V$

**Definition (The Hecke polynomial operator on $V$).** Let $w$ be split, with $w$ and $\bar w$ not places of $M$ or $Q$. For $X \in \mathbb{C}$, the operator $H_w(X)$ on the forms on $V$ of the pair is the restriction of the operator $\sum_{i \leq n}(-X)^i\,q^{i(i-1)/2}\,T_{w,i}$ on algebraic forms.

Lean: `New.DescentPair.heckePolyOnForms` (New/UpperBound/Objects/AuxiliaryPair.lean).

The restriction is defined because a form on $V$ is spherical at $w$, and each $T_{w,i}$ keeps the level and the character of the forms on $V$.

**Lemma.** Let $w$ be as in the definition. If the function of a form $y$ on $V$ has the Hecke polynomial $p$ at $w$, then $H_w(X)\,y = p(X)\,y$ for every $X$.

Lean: `New.DescentPair.heckePolyOnForms_eq_smul` (New/UpperBound/Objects/AuxiliaryPair.lean).

*Proof.* The inclusion of the algebraic forms into the functions commutes with the Hecke operators. $\square$

**Definition (The root of a lift).** For a finite place $w$, the root of a lift at $w$ is

$$x_w = \bigl(\alpha\,q^{t-1}\bigr)^{-1}.$$

Lean: `New.DescentPair.liftHeckeRoot` (New/UpperBound/Objects/AuxiliaryPair.lean).

The factor $1 - q^{t-1}\alpha X$ of the first product vanishes at $X = x_w$. This is the factor with $i = t - 1$. It exists because $t \geq 1$.

**Definition (Hecke polynomials of a lift).** Let $z$ assign a sequence $z(w)$ of complex numbers to each finite place $w$. A form $y$ on $V$ has the Hecke polynomials of a lift with eigenvalues $z$ if, at each split $w$ such that $w$ and $\bar w$ are not places of $M$ or $Q$, the function of $y$ has the Hecke polynomial

$$X \mapsto \prod_{i < t}(1 - q^i\alpha X)\cdot H_{z(w)}\bigl(q^t\alpha\beta^{-1}X\bigr),$$

where $H_{z(w)}$ is the scalar polynomial of rank $r$ with the eigenvalues $z(w)$.

Lean: `New.DescentPair.HasLiftHeckePolynomial` (New/UpperBound/Objects/AuxiliaryPair.lean).

**Lemma (The root kills a lift).** Let $w$ be split, with $w$ and $\bar w$ not places of $M$ or $Q$. Let $y$ be a form on $V$ with the Hecke polynomials of a lift, for some eigenvalues $z$. Then $H_w(x_w)\,y = 0$.

Lean: `New.DescentPair.heckePolyOnForms_liftHeckeRoot_eq_zero` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* By the lemma above, $H_w(x_w)\,y = p(x_w)\,y$, where $p$ is the Hecke polynomial of the definition. Write $t = k + 1$. The factor $i = k$ of the first product is $1 - q^k\alpha x_w = 1 - q^k\alpha\,(\alpha q^k)^{-1} = 0$. So $p(x_w) = 0$. $\square$

The lemma uses nothing about $z$. It also uses nothing of the rest of this chapter. This is why the source can state it in the file of the next chapter.

### Eigensystems on the forms of level $J_M$

To apply the lemma to $\Theta_{j,\vartheta}\,y$, the form $y$ must have a Hecke polynomial at $w$. A general form of level $J_M$ is a sum of Hecke eigenforms. The source uses the eigenforms of the Hecke operators away from the level.

**Definition (Hecke operators and eigenparts).** For a finite place $w$ and $i \in \mathbb{N}$, the operator $T_{(w,i)}$ on the forms of level $J_M$ is the Hecke operator $T_{w,i}$ if $w$ is split and neither $w$ nor $\bar w$ is a chosen place, and $0$ otherwise. An eigensystem is a function $p$ from the pairs $(w, i)$ to $\mathbb{C}$. The eigenpart of $p$ is the subspace of the forms $y$ of level $J_M$ with $T_{(w,i)}\,y = p(w, i)\,y$ for every pair $(w, i)$.

Lean: `New.Data.heckeOperator`, `New.Data.eigenPart` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

**Lemma.** Let $y$ lie in the eigenpart of $p$. Let $w$ be split, with $w$ and $\bar w$ not chosen places. Then $y$ is spherical at $w$, and it has the Hecke polynomial $H_{p(w,\cdot)}$ of rank $r$ at $w$.

Lean: `New.Data.hasHeckePolynomial_of_mem_eigenPart` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* A form of level $J_M$ is spherical at each place off $M$. On a spherical vector that is an eigenvector of each $T_{w,i}$, the Hecke polynomial operator acts by the scalar polynomial with the eigenvalues, by Volume 5 (`New.hasHeckePolynomial_of_heckeSplit`). $\square$

**Theorem (The eigenparts span).** Let $V$ be a hermitian space of rank $r$ such that the forms of level $J_M$ on $V$ form a finite dimensional space. Then these forms are the sum of the eigenparts over all eigensystems $p$.

Lean: `New.Data.iSup_eigenPart_eq_top` (New/Spanning/Multiplicities/HeckeEigensystems.lean).

*Proof.* The operators $T_{(w,i)}$ commute, and each is normal for the Petersson product. A commuting family of normal operators on a finite dimensional inner product space is simultaneously diagonalizable. So the space is the span of the joint eigenvectors. Each joint eigenvector lies in the eigenpart of its eigensystem. $\square$

### The Hecke polynomials of the single lift

**Theorem (Hecke polynomials of the single lift).** Let $\vartheta$ be a tame character and let $1 \leq j \leq m$. Let $y$ be a form of level $J_M$ on $W_j$ in the eigenpart of $p$. Then $\Theta_{j,\vartheta}\,y$ has the Hecke polynomials of a lift with the eigenvalues $z(w)_i = p(w, i)$.

Lean: `New.Data.hasLiftHeckePolynomial_singleLift` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* Let $w$ be split, with $w$ and $\bar w$ not places of $M$ or $Q$. Then in particular $w$ and $\bar w$ are not chosen places. By the lemma on eigenparts, $y$ has the Hecke polynomial $H_{p(w,\cdot)}$ at $w$. By Section 3, $\Theta_{j,\vartheta}\,y = \Theta_W\,y$ for the $j$-th pair, and $2\varsigma$ fits that pair. The theorem on the lift of a pair gives the Hecke polynomial of $\Theta_{j,\vartheta}\,y$ at $w$. It is the polynomial of the definition. $\square$

**Theorem (The root kills the single lift).** Let $\vartheta$ be a tame character and let $1 \leq j \leq m$. Let $w$ be split, with $w$ and $\bar w$ not places of $M$ or $Q$. Then for every form $y$ of level $J_M$ on $W_j$,

$$H_w(x_w)\,\Theta_{j,\vartheta}\,y = 0,$$

where $H_w$ is the Hecke polynomial operator on the forms on $V_j$ and $x_w = (\alpha\,q^{t-1})^{-1}$, with $\alpha$ the Frobenius value at $w$ of the character $\nu_W$ of the $j$-th pair.

Lean: `New.Data.heckePolyOnForms_liftHeckeRoot_singleLift_eq_zero` (New/Determinant/Norms/AdjointThetaLift.lean).

*Proof.* The map $y \mapsto H_w(x_w)\,\Theta_{j,\vartheta}\,y$ is linear. On the eigenpart of each $p$ it is $0$, by the theorem on the single lift and the lemma on the root. The forms of level $J_M$ on $W_j$ form a finite dimensional space, so the eigenparts span it by the theorem above. A linear map that is $0$ on a spanning family of subspaces is $0$. $\square$

The theorem holds for every form of level $J_M$, not only for eigenforms. The root $x_w$ depends on $\vartheta$ only through $\alpha$, the Frobenius value of $\nu_W = \mu_j^0\vartheta$ at $w$.

**Example (Rank one).** Take the shape of the formula for a space $W$ of rank $1$. Let $y$ be an eigenform with the eigenvalue $\lambda \neq 0$ of $T_{w,1}$ at a split $w$. Its Hecke polynomial at $w$ is $1 - \lambda X$, since $T_{w,0} = 1$. The lift has the Hecke polynomial

$$\prod_{i<t}(1 - q^i\alpha X)\cdot\bigl(1 - \lambda q^t\alpha\beta^{-1}X\bigr).$$

Its $t + 1$ roots are $(q^i\alpha)^{-1}$ for $i < t$ and $\beta(\lambda q^t\alpha)^{-1}$. The first $t$ roots are the same for every $y$. The theorem uses the last of them, $i = t - 1$. In the argument $r \geq 3$ is large, but the shape is the same: $t$ fixed roots and $r$ roots that depend on $y$.

**Remark (Formalization).** The eigenvalue $p$ of `New.HasHeckePolynomial` is a function $\mathbb{C} \to \mathbb{C}$, as in Volume 5. An eigensystem is any function on the pairs $(w, i)$. The operator $T_{(w,i)}$ is $0$ at the places that are not split or that lie over a chosen place. So the eigenpart of $p$ is $0$ unless $p(w,i) = 0$ at these places. The theorem on spanning needs the finite dimension as a hypothesis. For the forms of level $J_M$ on $W_j$, Lean finds it as an instance.
