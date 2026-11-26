---
title: Data and small classes
lean:
  - New/OneLift/FalseLifts/BottomOfTower.lean
  - Lib/Weil/Periods/DescentVanishing.lean
decls:
  - New.SiegelWeil.DescentsVanish
  - New.SiegelWeil.DescentsVanish.of_schrodingerOp
  - New.DescentPair.descentPairing
  - New.DescentPair.BlockDescentVanishes
  - New.factorialIdele
  - New.factorialBox
  - New.antitone_factorialBox
  - New.cosetIndicator_factorialIdele
  - New.IsSchwartzBruhat.eventually_const
  - New.mem_of_nested_cosets
  - New.IsSchwartzBruhat.mem_of_eventually_coset
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Data and small classes

This section and the next prove the theorem of the bottom of the tower, stated in [Section 1](/chapter/false-lifts/#what-the-chapter-proves). The hypothesis gives the vanishing of the descents of one matrix coefficient for one datum at the finite places, the block datum $\Psi_{\mathrm{bl}}$. The conclusion is the vanishing for all data that are the vacuum off $\Sigma$. This section reduces the conclusion to the indicators of small classes. [The next section](/chapter/false-lifts/#the-bottom-of-the-tower) treats two kinds of points: those with an integral block ratio at every place of $O$, and the others.

### Vanishing descents

Let $W$ and $V$ be hermitian spaces, $a$ a character of $U(1)$, $S$ a set of finite places and $Y$ a function on $U(V)(\mathbb{A})$.

**Definition (Vanishing descents).** The descents of $Y$ to $W$ vanish above $S$ if for every datum $f$ on $\mathrm{Hom}(W, V)$ that is the vacuum at the places of $S$ (that is, $\mathrm{projOn}\ S\ f = f$), the theta lift $g \mapsto \int_{[U(V)]} \theta_f(g, h) Y(h)\, dh$ of $Y$ to $U(W)$, with the kernel twisted by $a(\det h)$, is zero.

Lean: `New.SiegelWeil.DescentsVanish` (Lib/Weil/Periods/DescentVanishing.lean).

We use $S = \Sigma^c$, the complement of $\Sigma$. The data are then the vacuum off $\Sigma$. The lift and the kernel are those of [the Weil representation](/chapter/weil-representation/); the definition is also in [descents and block periods](/chapter/bessel-periods/#descents-and-block-periods). The next fact reduces the test to special data.

**Theorem (Special data suffice).** Let $V$ be definite, $A$ a set of finite places disjoint from its conjugate, and $Y$ automorphic. Suppose that the lift of $Y$ by the datum $v_P \otimes \Psi \otimes \mathrm{vac}$ is zero for every polynomial $P$ and every Schwartz-Bruhat function $\Psi$ of the components at $A$. Here $v_P$ is the Fock vector of $P$ at infinity and $\Psi \otimes \mathrm{vac}$ is `schrodingerOp A Ψ` applied to the vacuum. Then the descents of $Y$ vanish above the complement of the conjugate closure of $A$.

Lean: `New.SiegelWeil.DescentsVanish.of_schrodingerOp` (Lib/Weil/Periods/DescentVanishing.lean).

*Proof.* Fix $g$. Since $Y$ is automorphic, it is rapidly decreasing on the compact quotient of the definite group, and the lift at $g$ is a continuous linear functional $L_g$ of the datum. A datum that is the vacuum off $\Sigma = A \cup \bar A$ is a limit of combinations of data $v_P \otimes \rho(x)\mathrm{vac}$, where $\rho(x)$ is the finite Heisenberg operator of a vector $x$ supported on $\Sigma$. Since $A$ is disjoint from its conjugate, $\rho(x)\mathrm{vac}$ is a multiple of $\Psi\otimes\mathrm{vac}$, where $\Psi$ is the translate by $x$ of the indicator of the integral box at $A$. So $L_g$ vanishes on a dense set of these data, hence on all of them. $\square$

### The descent pairing

Fix a descent pair $O$, a linear functional $u$ on the values of the forms in `O.FormV`, a polynomial $P$ and a point $g$ of $U(W)(\mathbb{A})$. Functions $\Psi$ on $n \times r$ matrices over $\mathbb{A}_f$ are the finite data.

**Definition (The descent pairing).** $B(\Psi, y) = $ `descentPairing u P g Ψ y` is the value at $g$ of the lift to $U(W)$, by the datum $v_P \otimes \Psi \otimes \mathrm{vac}$ at the places of $O$, of $\overline{\langle u, y \rangle}$, the conjugate of the matrix coefficient `algFormCoeff 1 u y`. It is linear in $\Psi$ and conjugate linear in $y$. The block descent vanishes for $y$ (`BlockDescentVanishes u P y`) if the lift by $v_P \otimes \Psi_{\mathrm{bl}} \otimes \mathrm{vac}$ is zero at every $g$.

Lean: `New.DescentPair.descentPairing`, `New.DescentPair.BlockDescentVanishes` (New/OneLift/FalseLifts/BottomOfTower.lean).

### Small classes

To pass from special functions to all Schwartz-Bruhat functions, we use classes modulo the ideles $i!$. One idele serves at all places of $O$ at once.

**Definition (Factorial boxes).** `factorialIdele E i` is the finite idele $i!$. The box $\mathrm{Box}_i$ (`factorialBox m S i`) is the group of vectors $x$ with $(i!)^{-1}x$ integral at the places of $S$. The indicator of the class of $z$ modulo $i!$ at $S$ is $1_{C_i(z)}(y) = 1$ if $y - z \in \mathrm{Box}_i$, and $0$ otherwise.

Lean: `New.factorialIdele`, `New.factorialBox`, `New.cosetIndicator_factorialIdele` (New/OneLift/FalseLifts/BottomOfTower.lean).

**Lemma (Boxes).**

1. If $i \leq j$, then $\mathrm{Box}_j \subseteq \mathrm{Box}_i$.
2. Let $\Psi$ be Schwartz-Bruhat at $S$ and $x$ a vector. For all large $i$, $\Psi$ is constant on $C_i(x)$.

Lean: `New.antitone_factorialBox`, `New.IsSchwartzBruhat.eventually_const` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* (1) $i!$ divides $j!$. (2) $\Psi$ reads only the components at $S$ and is locally constant. So there is $N \geq 1$ such that $\Psi(Nu + x) = \Psi(x)$ for all $u$ that are integral at every finite place. For $i \geq N$, $N$ divides $i!$, so every $y \in C_i(x)$ agrees at $S$ with $x + Nu$ for such a $u$. $\square$

**Lemma (Nested cosets).** Let $U_0 \supseteq U_1 \supseteq \cdots$ be subgroups of an abelian group $X$, $P$ a subspace of the functions $X \to \mathbb{C}$, $F$ a finite set and $i : X \to \mathbb{N}$. Suppose that the indicator of $x + U_{i(x)}$ lies in $P$ for every $x \in F$. Let $\Psi$ be constant on each $x + U_{i(x)}$, $x \in F$, and zero off their union. Then $\Psi \in P$.

Lean: `New.mem_of_nested_cosets` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* Induction on $F$. If $F$ is empty, $\Psi = 0$. Otherwise choose $a \in F$ with $i(a)$ smallest. Then $a + U_{i(a)}$ is the largest coset. For $x \in F$, $x + U_{i(x)}$ lies in a coset of $U_{i(a)}$, so it lies in $a + U_{i(a)}$ or is disjoint from it. Let $C$ be the indicator of $a + U_{i(a)}$. The function $\Psi - \Psi(a) C$ is constant on each coset of $F \setminus \{a\}$, and it vanishes on $a + U_{i(a)}$ and off the union. So it lies in $P$ by induction. Also $\Psi(a)C \in P$. $\square$

**Theorem (Small classes suffice).** Let $P$ be a subspace of the functions on $m$-vectors over $\mathbb{A}_f$. Suppose that for every $x$, $1_{C_i(x)} \in P$ for all large $i$. Then $P$ contains every Schwartz-Bruhat function $\Psi$ at $S$.

Lean: `New.IsSchwartzBruhat.mem_of_eventually_coset` (New/OneLift/FalseLifts/BottomOfTower.lean).

*Proof.* For each $x$ choose $i(x)$ with $1_{C_{i(x)}(x)} \in P$ and $\Psi$ constant on $C_{i(x)}(x)$; this is possible by part 2 of the lemma on boxes. The components at $S$ of the support of $\Psi$ lie in a compact set, and the open sets $C_{i(x)}(x)$ cover it. Take a finite subcover $F$. A point $y$ with $\Psi(y) \neq 0$ agrees at $S$ with a point of the compact set, so it lies in some $C_{i(x)}(x)$, $x \in F$. Now apply the lemma on nested cosets with $U_i = \mathrm{Box}_i$. $\square$

**Remark (Formalization).** The map $x \mapsto i(x)$ is made with `choose`. Its values are not unique; any choice works. The idele $i!$ replaces the powers of a uniformiser at one place. It goes to $0$ at every finite place at the same time, so the source needs no family of uniformisers.

