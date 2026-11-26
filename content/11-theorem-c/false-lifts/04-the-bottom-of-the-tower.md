---
title: The bottom of the tower
lean:
  - New/OneLift/FalseLifts/BottomOfTower.lean
decls:
  - New.DescentPair.translatedBlockFn
  - New.DescentPair.residueBlockDatum_mul
  - New.DescentPair.translatedBlockFn_leftMul
  - New.DescentPair.exists_leftMul_eq_of_translatedBlockFn_ne_zero
  - New.DescentPair.levelTranslate
  - New.DescentPair.finite_range_levelTranslate
  - New.DescentPair.eq_smul_translatedBlockFn
  - New.DescentPair.translatedBlockFn_eq_one_of_hasIntegralBlockRatio
  - New.DescentPair.descentPairing_translate
  - New.DescentPair.descentPairing_levelTranslate
  - New.DescentPair.exists_pairWeil_blockDatum_eq_smul
  - New.DescentPair.descentPairing_translatedBlockFn_eq_zero
  - New.exists_fixed_forall_linearMap_eq_of_finite
  - New.DescentPair.eventually_descentPairing_eq_zero_of_hasIntegralBlockRatio
  - New.DescentPair.smul_chosenGLRep_eq_apply_of_triangular
  - New.DescentPair.exists_leftMul_eq_and_blockAction_eq
  - New.DescentPair.descentPairing_eq_zero_of_not_hasIntegralBlockRatio
  - New.DescentPair.descentsVanish_of_hyperplaneSumsAnnihilate
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The bottom of the tower

We keep the descent pair $O$, the functional $u$, the polynomial $P$, the point $g$ and the pairing $B(\Psi, y)$ of [the last section](/chapter/false-lifts/#data-and-small-classes). We prove that $B(1_C, y) = 0$ for every small class $C$, first for the points with an integral block ratio at every place of $O$, then for the others.

### The block datum and the level group

The function $\Psi_{\mathrm{bl}}$ of [descent pairs](/chapter/single-theta-lifts/#descent-pairs-and-the-vector-kernel) is read on the reductions at the places of $O$. It vanishes unless $x$ is integral at these places. On integral $x$ it is $0$ unless $\bar x_w = e$ at every chosen place $w$, and then it is $\prod_{w \in Q} \psi_w(\det \bar x_w')$. For $A \in U(W)(\mathbb{A}_f)$ we write $\Psi_A(x) = \Psi_{\mathrm{bl}}(xA)$ (`O.translatedBlockFn A`). It is Schwartz–Bruhat at the places of $O$.

The level group of $O$ consists of the $h$ in the maximal level whose reductions fix $e$ at the chosen places and are block lower triangular at $Q$. Its character is $\chi_O(h) = \prod_{w \in Q} \psi_w(\det \bar h_w')^{-1}$ (`O.levelChar`), where $\bar h_w'$ is the block of the rows and columns $\iota$. The forms in `O.FormV` satisfy $h y = \chi_O(h) y$ for $h$ in the level group. The twisted translation of a function is $(h \cdot \Psi)(x) = \overline{\chi_O(h)}\, \Psi(h^{-1}x)$ (`O.levelTranslate h Ψ`).

**Lemma (The level group and $\Psi_A$).** Let $A \in U(W)(\mathbb{A}_f)$.

1. For $h$ in the level group, $\Psi_A(hx) = \overline{\chi_O(h)}\, \Psi_A(x)$.
2. If $\Psi_A(x) \neq 0$, then $x$ and $h\, e A^{-1}$ have the same components at the places of $O$, for some $h$ in the level group.

Lean: `New.DescentPair.residueBlockDatum_mul`, `New.DescentPair.translatedBlockFn_leftMul`, `New.DescentPair.exists_leftMul_eq_of_translatedBlockFn_ne_zero` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) Since $h$ is in the maximal level, $hxA$ is integral at the places of $O$ if and only if $xA$ is. If not, both sides are $0$. If yes, let $\tau_w = \bar h_w$ and $X_w$ the reduction of $xA$. At a chosen place $\tau_w e = e$, so $\tau_w X_w = e$ if and only if $X_w = e$. At $w \in Q$, $\tau_w$ is block lower triangular, so the upper block of $\tau_w X_w$ is $\tau_w' X_w'$, with determinant $\det \tau_w' \det X_w'$. So $\Psi_{\mathrm{bl}}(\tau X) = \prod_{w \in Q} \psi_w(\det \tau_w') \Psi_{\mathrm{bl}}(X)$, and $\prod_{w\in Q}\psi_w(\det\tau_w') = \overline{\chi_O(h)}$ since the values of $\psi_w$ have modulus $1$.

(2) Let $u_w$ be the component of $xA$ at the place $w$ of $O$. As $\Psi_A(x) \neq 0$, $u_w$ is integral, $\bar u_w = e$ at the chosen places, and $\psi_w(\det \bar u_w') \neq 0$ at $Q$. So $\det u_w'$ is a unit at every place of $O$. By the lemma on completed columns in [Section 2](/chapter/false-lifts/#hyperplane-sums-and-block-ratios), the matrix $\text{completeColumns}\ \iota\ u_w = \begin{pmatrix} u_w' & 0 \\ u_w'' & 1\end{pmatrix}$ is integral with unit determinant. Let $h$ be the element of the maximal level with these components at the places of `O` (`exists_stdLevel_atPlace_eq`). At a chosen place, its reduction sends $e$ to $\bar u_w = e$. At $w \in Q$, its rows $\iota$ are zero outside the columns $\iota$. So $h$ lies in the level group (`mem_levelGroup_of_reduceAt`). Its component $h_w$ satisfies $h_w e = u_w$, so $h_w e A^{-1} = u_w A^{-1}$ is the component of $x$. $\square$

**Lemma (Uniqueness on the orbit).** Let $\Psi_A(z) = 1$. Let $\Psi$ read only the components at the places of $O$, be fixed by every twisted translation $h \cdot$, and vanish where $\Psi_A$ vanishes. Then $\Psi = \Psi(z)\, \Psi_A$.

Lean: `New.DescentPair.eq_smul_translatedBlockFn` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* Let $b = eA^{-1}$. Invariance gives $\Psi(hx) = \overline{\chi_O(h)} \Psi(x)$, and part 1 of the last lemma gives the same rule for $\Psi_A$. If $\Psi_A(x) = 0$, then $\Psi(x) = 0$. Otherwise, by part 2, $x$ agrees with $hb$ at the places of $O$, and both functions read only these components. So with $c = \overline{\chi_O(h)}$, we get $\Psi(x) = c\Psi(b)$ and $\Psi_A(x) = c \Psi_A(b)$. Apply this to $x = z$: $1 = c_z \Psi_A(b)$ and $\Psi(z) = c_z\Psi(b)$, so $\Psi(b) = \Psi(z)\Psi_A(b)$. Hence $\Psi(x) = c\Psi(z)\Psi_A(b) = \Psi(z)\Psi_A(x)$. $\square$

**Lemma (The value $1$).** Let $z$ have an integral block ratio at every place $w$ of $O$, with "chosen" meaning that $w$ is chosen. Let $A$ have the components $(z_w')^{-1}$ at the places of $O$. Then $\Psi_A(z) = 1$.

Lean: `New.DescentPair.translatedBlockFn_eq_one_of_hasIntegralBlockRatio` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* The component of $zA$ at $w$ is $z_w (z_w')^{-1} = \begin{pmatrix} 1 \\ z_w'' (z_w')^{-1}\end{pmatrix}$. It is integral. At a chosen place the lower block is $\equiv 0$, so the reduction is $e$. At $w \in Q$ the upper block is $1$, and $\psi_w(1) = 1$. So $\Psi_{\mathrm{bl}}(zA) = 1$. $\square$

### Moving the pairing

**Lemma (Invariance of the pairing).** Let $\Psi$ be Schwartz–Bruhat at the places of $O$.

1. If $k$ is in the maximal level and $y' = ky$, then $B(\Psi(k^{-1}\cdot), y') = B(\Psi, y)$.
2. If $h$ is in the level group, then $B(h \cdot \Psi, y) = B(\Psi, y)$.

Lean: `New.DescentPair.descentPairing_translate`, `New.DescentPair.descentPairing_levelTranslate` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) The lift is equivariant: the lift of $\overline{\langle u, ky\rangle} = \overline{\langle u, y\rangle}(\cdot\, k)$ by a datum $\phi$ is the lift of $\overline{\langle u, y\rangle}$ by $\omega(k)\phi$. The element $k$ is finite, so $\omega(k)$ fixes $v_P$. It is integral at every place, so it fixes the vacuum, and at the places of $O$ it sends $\Psi$ to $\Psi(k^{-1}\cdot)$. So the lift of $\overline{\langle u, y'\rangle}$ by the datum of $\Psi(k^{-1}\cdot)$ is the lift of $\overline{\langle u, y\rangle}$ by the datum of $\Psi$. (2) Apply (1) with $k = h$ and use $hy = \chi_O(h)y$. Since $B$ is conjugate linear in $y$, $B(\Psi(h^{-1}\cdot), \chi_O(h)y) = \overline{\chi_O(h)} B(\Psi(h^{-1}\cdot), y)$, which is $B(h\cdot\Psi, y)$. $\square$

**Lemma (The translated block datum).** Let $A \in U(W)(\mathbb{A}_f)$ be $1$ off the places of $O$ and their conjugates.

1. There is $c \neq 0$ with $\omega(A)(\Psi_{\mathrm{bl}} \otimes \mathrm{vac}) = c\, \Psi_A \otimes \mathrm{vac}$.
2. If the block descent vanishes for $y$, then $B(\Psi_A, y) = 0$.

Lean: `New.DescentPair.exists_pairWeil_blockDatum_eq_smul`, `New.DescentPair.descentPairing_translatedBlockFn_eq_zero` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) $U(W)$ acts on $\mathrm{Hom}(W, V)$ by $x \mapsto xA$, so $\omega(A)$ sends $\Psi$ to a multiple of $\Psi(\cdot\, A)$. The multiple is $c = \chi(\det A)^{-1}\, \sqrt{|\det A|}^{\,n}$ for the space character $\chi$ and the idele norm, with $\det A$ taken at the places of $O$. It is not zero. Away from the places of $O$ and their conjugates $A = 1$, so the vacuum is fixed.

(2) By equivariance, the lift by $v_P \otimes \Psi_{\mathrm{bl}} \otimes \mathrm{vac}$ at $gA$ is the lift by $\omega(A)(v_P \otimes \Psi_{\mathrm{bl}}\otimes\mathrm{vac})$ at $g$. As $A$ is finite, $\omega(A)$ commutes with the integration against $v_P$. By (1) this is $c\, B(\Psi_A, y)$. It is $0$ by hypothesis, and $c \neq 0$. $\square$

### Case 1: an integral block ratio at every place

**Lemma (The mean of translates).** Let a group $J$ act linearly on $V$, and let $f \in V$ have finitely many translates. There is a $J$-invariant $f_1$ such that $L f_1 = c$ for every linear form $L$ that has the constant value $c$ on the translates of $f$.

Lean: `New.exists_fixed_forall_linearMap_eq_of_finite` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* Let $f_1$ be the mean of the finite set $T$ of translates. Each $\rho(h)$ permutes $T$, so $f_1$ is invariant, and $L f_1 = (\# T)^{-1} \sum_{t \in T} L t = c$. $\square$

**Theorem (Case 1).** Let the block descent vanish for $y$. Let $z$ have an integral block ratio at every place of $O$. Then $B(1_{C_i(z)}, y) = 0$ for all large $i$, with classes at the places of $O$.

Lean: `New.DescentPair.eventually_descentPairing_eq_zero_of_hasIntegralBlockRatio` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* Choose $A \in U(W)(\mathbb{A}_f)$ with the components $(z_w')^{-1}$ at the places of $O$ and $1$ elsewhere (`exists_atPlace_eq`). By the lemma on the value $1$, $\Psi_A(z) = 1$. By part 2 of the lemma on boxes, for large $i$ the function $\Psi_A$ is $1$ on $C = C_i(z)$. Fix such an $i$.

The indicator $1_C$ has finitely many twisted translates (`New.DescentPair.finite_range_levelTranslate`): $\chi_O$ takes finitely many values, and the class of $kz$ depends locally constantly on $k$ in the compact maximal level. Let $\Psi_1$ be the mean of these translates. We check four facts with the lemma on the mean.

1. $B(\Psi_1, y) = B(1_C, y)$, since $B(\cdot, y)$ is constant on the translates by part 2 of the invariance of the pairing.
2. $\Psi_1$ reads only the components at the places of $O$, since $L(\Psi) = \Psi(\mathrm{idem}\cdot x) - \Psi(x)$ is $0$ on the translates.
3. $\Psi_1$ vanishes where $\Psi_A$ vanishes. Let $\Psi_A(x) = 0$. A translate takes at $x$ the value $\overline{\chi_O(h)} 1_C(h^{-1}x)$. If $h^{-1}x \in C$, then $\Psi_A(h^{-1}x) = 1$, and by part 1 of the lemma on the level group $\Psi_A(x) = \overline{\chi_O(h)}^{\,-1} \neq 0$. So every translate vanishes at $x$.
4. $\Psi_1$ is invariant.

By uniqueness on the orbit, $\Psi_1 = \Psi_1(z)\Psi_A$. So $B(1_C, y) = \Psi_1(z) B(\Psi_A, y) = 0$ by the lemma on the translated block datum. $\square$

### Case 2: a place without an integral block ratio

**Lemma (Triangular elements).** Let $\pi$ be a representation of $U(I_n)(\mathbb{A}_f)$ and $y$ a vector with $\pi(h)y = \chi_O(h)y$ for $h$ in the level group. Let $k$ be in the maximal level, with reductions $\tau_w$ at the places of $O$, and let $s_w \in GL_r(k_w)$. Suppose $\tau_w e = e s_w$ at the chosen places and $\tau_w^T e = e s_w^T$ at $Q$. Then

$$\pi(k)y = \Big(\prod_{w \in M \sqcup Q} \psi_w(\det s_w)^{-1}\Big)\, \text{chosenGLRep}\ \pi\ (\bar s)\, y.$$

Lean: `New.DescentPair.smul_chosenGLRep_eq_apply_of_triangular` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* Let $k_0$ be the element of the maximal level with reductions $\mathrm{diag}(s_w, 1)$ at the chosen places and $1$ at $Q$. By definition, $\text{chosenGLRep}\ \pi\ (\bar s)\, y = \prod_{w \in M}\psi_w(\det s_w)\,\pi(k_0)y$. At a chosen place, $\mathrm{diag}(s_w,1)^{-1}\tau_w$ fixes $e$. At $w \in Q$, $\tau_w$ is block lower triangular with first block $s_w$. So $k_0^{-1}k$ lies in the level group, and $\chi_O(k_0^{-1}k) = \prod_{w\in Q}\psi_w(\det s_w)^{-1}$. Hence $\pi(k)y = \pi(k_0)\pi(k_0^{-1}k)y = \prod_{w\in Q}\psi_w(\det s_w)^{-1}\pi(k_0)y$. Insert the expression for $\pi(k_0)y$. $\square$

**Lemma (A shear for each $s$).** Let $j$ be a place of $O$ and $l$ an annihilating row of $z_j$, with "chosen" meaning $j \in M$. Let $s$ lie in the hyperplane group of $\bar\lambda$, the reduction of $l \circ \iota$. Then there is $h$ in the maximal level such that $hz$ and $z$ have the same components at the places of $O$, and $hy = \text{blockAction}(\text{mulSingle}\ j\ s)\, y$.

Lean: `New.DescentPair.exists_leftMul_eq_and_blockAction_eq` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* Write $s = 1 + \bar v\bar\lambda$ and lift $\bar v$ to an integral column $v$. Let $h$ have the component $h_v = \text{rowShear}\ \iota\ v\ l$ at $j$ and $1$ at the other places of $O$. By Section 2, $\det h_v = \det(1 + v\lambda)$, whose reduction is $\det s \neq 0$, so $h_v$ is integral and invertible. Since $lz_j = 0$, $h_v z_j = z_j$. Its reduction satisfies $\bar h_v e = e(1 + \bar v\bar\lambda) = es$. If $j \in Q$, then $\bar\lambda' = 0$, so also $\bar h_v^T e = e s^T$. At the other places the reduction is $1 = $ the block $1$. The lemma on triangular elements, with $\pi$ the action on forms, gives $hy = \text{blockAction}(\text{mulSingle}\ j\ s)\, y$. $\square$

**Theorem (Case 2).** Let $\psi_w \neq 1$ for $w \in Q$, and let the hyperplane sums annihilate $y$. If $z$ has no integral block ratio at a place $j$ of $O$, then $B(1_C, y) = 0$ for the class $C$ of $z$ modulo any idele $t$ at the places of $O$.

Lean: `New.DescentPair.descentPairing_eq_zero_of_not_hasIntegralBlockRatio` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* By the theorem on points without an integral block ratio in Section 2, $z_j$ has an annihilating row $l$, and $\bar\lambda \neq 0$. Let $G_\lambda$ be the hyperplane group of $\bar\lambda$. For $s \in G_\lambda$, take $h$ as in the last lemma and put $y_s = hy$. As $h$ is in the maximal level and fixes $z$ at the places of $O$, it preserves the class $C$, so $1_C(h^{-1}\cdot) = 1_C$. By part 1 of the invariance of the pairing, $B(1_C, y_s) = B(1_C, y)$. Hence

$$\#G_\lambda \cdot B(1_C, y) = \sum_{s \in G_\lambda} B(1_C, y_s) = B\Big(1_C, \sum_{s} \text{blockAction}(\text{mulSingle}\ j\ s)\, y\Big) = B(1_C, 0) = 0,$$

by the one place lemma of Section 2. As $\#G_\lambda \neq 0$, $B(1_C, y) = 0$. $\square$

### The proof of the theorem

*Proof of the bottom of the tower.* The places of $O$ are disjoint from their conjugates (`isConjDisjoint_places`). By the theorem on special data, it suffices to show $B(\Psi, y) = 0$ for all $P$, all $g$ and all Schwartz–Bruhat $\Psi$ at the places of $O$. Let $P_0$ be the kernel of $\Psi \mapsto B(\Psi, y)$. By the theorem on small classes, it suffices that $1_{C_i(z)} \in P_0$ for all large $i$, for every $z$. If $z$ has an integral block ratio at every place of $O$, this is Case 1, with the hypothesis on the block datum. Otherwise Case 2 gives $B(1_{C_i(z)}, y) = 0$ for every $i$. $\square$

**Example.** Take $r = 1$, $n = 2$, one chosen place and no twist place. Then $\Psi_{\mathrm{bl}}$ is the indicator of the integral $x$ with $x \equiv (1, 0)^T$. Case 1 covers the points $z = (z_1, z_2)^T$ with $z_1 \neq 0$ and $|z_2| < |z_1|$. For $A = z_1^{-1}$, the function $\Psi_A$ is the indicator of $z_1\big((1,0)^T + \varpi\mathcal{O}_w \oplus \varpi\mathcal{O}_w\big)$, where $\varpi$ is a uniformiser, and it contains $z$. The other points satisfy $|z_2| \geq |z_1|$. For them the row $l = (-z_2/z_1, 1)$ (or $(1,0)$ if $z_1 = 0$) gives $\bar\lambda \neq 0$, and the hyperplane group of $\bar\lambda$ is the full group $k_w^\times$. The form action of $s$ is $\psi_w(s)$ times the translation by a lift of $\mathrm{diag}(s, 1)$. So the condition "hyperplane sums annihilate" says that the sum of the translates of $y$ by the lifts of $\mathrm{diag}(s,1)$, $s \in k_w^\times$, is zero: $y$ has no component that is invariant under this torus of the residue group.
