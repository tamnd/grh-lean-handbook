---
title: Divided lattices
lean:
  - New/OneLift/ComparisonOperator/GluedLattices.lean
decls:
  - New.Rows.DividedSplitting
  - New.LevelPlaces.chosenModulusSq
  - New.DescentPair.genIdele
  - New.Rows.genIdele_apply_of_notMem
  - New.Rows.reduction_levelModulus_eq_zero_iff
  - New.Rows.DividedSplitting.genResidue
  - New.Rows.DividedSplitting.genResidue_smul_eq_inclMatrix_iff
  - New.Rows.DividedLattice
  - New.Rows.DividedLattice.reducedInverse
  - New.Rows.DividedLattice.weilScalar
  - New.Rows.DividedLattice.reduceAt_conj_eq_one
  - New.Rows.DividedLattice.exists_reducedInverse_eq
  - New.Rows.DividedSplitting.congruenceGroup
  - New.Rows.DividedSplitting.mem_congruenceGroup_iff
  - New.Rows.DividedSplitting.exists_congruenceGroup_inv_eq_one_sub
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Divided lattices

The theta datum of the lift from $W$ to $V$ asks for a congruence $x \equiv (1;0)$ modulo $\varpi$ on an $n \times r$ matrix $x$. A product datum asks for two conditions modulo $\varpi^2$, one on each block of $x$. To pass from one to the other we change the lattice $\mathcal{O}^n$ at the chosen places to a lattice $\gamma\mathcal{O}^n$ with $\varpi\mathcal{O}^n \subseteq \gamma\mathcal{O}^n \subseteq \mathcal{O}^n$. This section sets up the ring modulo $\varpi^2$, these lattices and the congruence group $\Gamma$. The background on levels and reductions is in [congruence subgroups](/chapter/congruence-subgroups/). The adelic unitary group $G_f$ is in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/).

### The splitting and the generator

Let $O$ be a descent pair: chosen places $w_i$, twist places, the space $W$ of rank $r$ and an embedding $O.\mathrm{incl} : r \hookrightarrow n$. Let $Q$ be the product of the twist places. Recall that $\mathfrak{m}_c = \varpi^c Q$ is the modulus `levelModulus c` and that `levelModulus c false` is $\varpi^c$.

**Definition (Modulus $\varpi^2$).** The modulus $\varpi^2$ of $O$ is `S.levelModulus 2 false`, the square of the product of the chosen places.

Lean: `New.LevelPlaces.chosenModulusSq` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Definition (Divided splitting).** Let $z : r \hookrightarrow m$. A *divided splitting* $V$ of $O$ is an equivalence $\varepsilon : N \sqcup m \simeq n$ with these data:

1. an embedding $\mathrm{fixedEmb} : r \hookrightarrow N$ with $\varepsilon(\mathrm{inl}(\mathrm{fixedEmb}\,i)) = O.\mathrm{incl}\,i$ for all $i$;
2. an embedding $\mathrm{dividedEmb} : a \hookrightarrow N$;
3. the diagram $O.\mathrm{colsPlus}$ has no column of a height $h$ with $\#N \leq h < \#n$, and $O.\mathrm{colsMinus}$ has none with $\#m \leq h < \#n$.

Lean: `New.Rows.DividedSplitting` (New/OneLift/ComparisonOperator/GluedLattices.lean).

So $N$ indexes $V''$ and $m$ indexes $V^\circ$. The basis vectors $O.\mathrm{incl}\,i$ of the datum lie in $V''$. The map $z$ marks $r$ basis vectors of $V^\circ$. Condition 3 lets the polynomial of $V$ split as a product of a polynomial on $V''$ and one on $V^\circ$ (Section 4).

**Definition (The generator $\varpi$).** The idele $\varpi = O.\mathrm{genIdele}$ is the chosen generator of the modulus `O.levelModulus 1 false`, the product of the chosen places.

Lean: `New.DescentPair.genIdele` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Lemma (The generator off the chosen places).** If $w$ is not a chosen place, then $\varpi_w = 1$.

Lean: `New.Rows.genIdele_apply_of_notMem` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* The generator of a modulus is $1$ at every place that does not divide it. The places of `levelModulus 1 false` are the chosen places. $\square$

**Lemma (Divisibility by $\varpi^c$).** Let $x$ be an integral finite adele and $c \geq 0$. Then $x \equiv 0$ modulo $\varpi^c$ if and only if $\varpi^{-c}x$ is integral.

Lean: `New.Rows.reduction_levelModulus_eq_zero_iff` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* The reduction modulo a modulus $\mathfrak{n}$ with generator $g$ kills $x$ if and only if $g^{-1}x$ is integral. Apply this to $\mathfrak{n} = \varpi^c$. The ideal $\varpi^c$ is the $c$-th power of the ideal $I$ of the chosen places, and $I \neq 0$. So the multiplicity of a prime $w$ in $I^c$ is $c$ times its multiplicity in $I$. Hence the generator of $I^c$ and $\varpi^c$ have the same valuation at each $w$, and $g^{-1}x$ is integral exactly when $\varpi^{-c}x$ is. $\square$

Let $\bar\varpi$ be the class of $\varpi$ modulo $\varpi^2$.

Lean: `New.Rows.DividedSplitting.genResidue` (New/OneLift/ComparisonOperator/GluedLattices.lean).

The ring modulo $\varpi^2 Q$ maps onto the ring modulo $\varpi^2$, since $\varpi^2 Q \subseteq \varpi^2$. The next lemma translates a congruence modulo $\varpi$, written as an equation modulo $\varpi^2$, into conditions in the residue fields.

**Lemma (Multiplication by $\varpi$).** Let $T$ be a $k \times c$ matrix modulo $\varpi^2 Q$ and let $u : c \to k$. Then $\bar\varpi\,\bar T = \bar\varpi\,\iota_u$ modulo $\varpi^2$ if and only if $T$ reduces to the inclusion matrix $\iota_u$ in the residue field at every chosen place $w_i$.

Lean: `New.Rows.DividedSplitting.genResidue_smul_eq_inclMatrix_iff` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Choose an integral matrix $X$ with $T = \iota_u + X$ modulo $\varpi^2 Q$. Then $\bar\varpi\bar T = \bar\varpi\iota_u$ says $\varpi X \equiv 0$ modulo $\varpi^2$. By the last lemma with $c = 2$ this says that $\varpi^{-1}X$ is integral, that is $X \equiv 0$ modulo $\varpi$. The chosen places are distinct and none is conjugate to another. By the Chinese remainder theorem, $X \equiv 0$ modulo $\varpi$ if and only if every entry of $X$ has valuation $< 1$ at every $w_i$. That is the statement that $T = \iota_u + X$ reduces to $\iota_u$ at every $w_i$. $\square$

### Divided lattices

**Definition (Divided lattice).** A *divided lattice* $L$ of $O$ is a point $\gamma \in G_f$ with two properties:

1. $\gamma$ is supported on the chosen places: $\gamma_w = 1$ at every place $w$ such that neither $w$ nor $\bar w$ is chosen;
2. every entry of $\varpi\gamma^{-1}$ is integral.

Lean: `New.Rows.DividedLattice` (New/OneLift/ComparisonOperator/GluedLattices.lean).

Property 2 says $\varpi\mathcal{O}^n \subseteq \gamma\mathcal{O}^n$. At a conjugate place $\bar w_i$ we have $\varpi = 1$, so $\gamma^{-1}$ is integral there. Unitarity relates $\gamma_{w_i}$ to $(\gamma_{\bar w_i}^{-1})^*$, so $\gamma$ is integral at $w_i$. This is the inclusion $\gamma\mathcal{O}^n \subseteq \mathcal{O}^n$. The source records it in the docstring and in the factor $\bar\varpi\gamma$ in the proofs below.

**Definition (Reduced inverse).** The *reduced inverse* $\bar G_L$ of $L$ is the $n \times n$ matrix $\varpi\gamma^{-1}$ modulo $\varpi^2$.

Lean: `New.Rows.DividedLattice.reducedInverse` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Definition (The scalar $c_\gamma$).** Let $\delta$ be the determinant of $\gamma$ at the chosen places, as an idele. Let $\chi$ be the character that $O.\mathrm{charW}$ attaches to a space of rank $r$. Then $c_\gamma = \chi(\delta)/\sqrt{|\delta|}^{\,r}$.

Lean: `New.Rows.DividedLattice.weilScalar` (New/OneLift/ComparisonOperator/GluedLattices.lean).

This is the scalar by which $\gamma$ multiplies the finite datum in the Weil representation. See [the Weil representation](/chapter/weil-representation/) for the action of $\mathrm{GL}$ on the mixed model.

**Lemma (Conjugation kills the congruence).** Let $L$ be a divided lattice with point $\gamma$. Let $j \in K_0 = \mathrm{stdLevel}$ with $j \equiv 1$ modulo $\varpi^2$. Then $\gamma^{-1}j\gamma \in K_0$, and $\gamma^{-1}j\gamma$ reduces to $1$ at every chosen place $w_i$.

Lean: `New.Rows.DividedLattice.reduceAt_conj_eq_one` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* We have $\gamma^{-1}j\gamma - 1 = \gamma^{-1}(j-1)\gamma$. At a chosen place $\gamma$ and $\varpi\gamma^{-1}$ are integral, and $\varpi^2$ divides $j - 1$. So the claim is clear at the chosen places. To treat all places at once we use four facts.

1. For every $k \in K_0$ with $k \equiv 1$ modulo $\varpi^2$, the matrix $\varpi^{-2}(k-1)$ is integral. This is the lemma on divisibility by $\varpi^c$ for $c = 2$, entry by entry.
2. The matrix $\bar\varpi^{-1}(j-1)$ is integral. Indeed $j^{-1} \equiv 1$ modulo $\varpi^2$, so by fact 1 the matrix $\varpi\cdot\varpi^{-2}(j^{-1}-1)$ is integral. Since $j$ is unitary, $j^{-1} = j^*$. Apply the adjoint: the conjugate transpose of $\varpi^{-1}(j^* - 1)$ is $\bar\varpi^{-1}(j-1)$, and the conjugation of adeles preserves integrality.
3. The matrix $\bar\varpi^{-1}\varpi^{-2}(j-1)$ is integral. Fix a place $w$. No chosen place is conjugate to a chosen place. So $w$ or $\bar w$ is not chosen, and $\varpi_w = 1$ or $\varpi_{\bar w} = 1$. In the first case $\bar\varpi_w^{-1}\varpi_w^{-2}(j-1)_w$ equals the $w$-component of fact 2. In the second case it equals the $w$-component of fact 1.
4. The matrix $\bar\varpi\gamma$ is integral. It is the adjoint of $\varpi\gamma^{-1}$, since $\gamma^{-1} = \gamma^*$.

Now the $(a, b)$ entry of $\varpi^{-1}(\gamma^{-1}j\gamma - 1)$ is
$$\sum_{c, d} (\varpi\gamma^{-1})_{ac}\,\bigl(\bar\varpi^{-1}\varpi^{-2}(j-1)\bigr)_{cd}\,(\bar\varpi\gamma)_{db}.$$
Each factor is integral by property 2 of $L$, fact 3 and fact 4. So $\varpi^{-1}(\gamma^{-1}j\gamma - 1)$ is integral. Multiply by $\varpi$: the matrix $\gamma^{-1}j\gamma - 1$ is integral, so $\gamma^{-1}j\gamma$ is integral and unitary, and lies in $K_0$. The reduction at $w_i$ factors through the reduction modulo $\varpi$. By the lemma on divisibility with $c = 1$, the reduction modulo $\varpi$ kills every entry of $\gamma^{-1}j\gamma - 1$. $\square$

**Lemma (Divided lattices with a given reduced inverse).** Let $C$ and $G$ be integral $n \times n$ matrices with $CG = \varpi\cdot 1$. Then some divided lattice $L$ has $\bar G_L = G$ modulo $\varpi^2$.

Lean: `New.Rows.DividedLattice.exists_reducedInverse_eq` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* The matrices $C$ and $\varpi^{-1}G$ are inverse to each other over the finite adeles. Let $e$ be the idempotent adele that is $1$ at the chosen places and $0$ elsewhere. Cut $C$ with $e$: put $c = eC + (1 - e)$, with inverse $c^{-1} = e\varpi^{-1}G + (1-e)$. No chosen place is conjugate to a chosen place, so $e\bar e = 0$. Expand $c^*c$ and $cc^*$: both are the same combination of $C$, $C^*$ and $1$, so $c$ and $c^*$ commute. Put $\gamma = (c^*)^{-1}c$. Then
$$\gamma^*\gamma = c^*c^{-1}(c^*)^{-1}c = c^*(c^*)^{-1}c^{-1}c = 1,$$
since $c^{-1}$ and $(c^*)^{-1}$ commute. So $\gamma \in G_f$. A direct expansion with $e\bar e = 0$ gives
$$\varpi\gamma^{-1} = \varpi c^{-1}c^* = eG + \bar e\,\varpi C^* + (1 - e - \bar e)\varpi.$$
So $\varpi\gamma^{-1}$ is $G$ at the chosen places, $\varpi C^*$ at their conjugates and $\varpi$ elsewhere. All three are integral. At a place that is neither chosen nor conjugate to a chosen place, $e = \bar e = 0$, so $c = 1$ and $\gamma = 1$. Thus $L = \gamma$ is a divided lattice. For the reduction it is enough to compare at the places $w$ of $\varpi^2$, the chosen places. There $e_w = 1$ and $\bar e_w = 0$, so $(\varpi\gamma^{-1})_w = G_w$. $\square$

### The congruence group

**Definition (Congruence group).** The *congruence group* $\Gamma$ of $V$ is the stabiliser of the scalar matrix $\bar\varpi\cdot 1$ in $\mathrm{GL}_r$ modulo $\varpi^2$, for the action by multiplication.

Lean: `New.Rows.DividedSplitting.congruenceGroup` (New/OneLift/ComparisonOperator/GluedLattices.lean).

**Lemma (Membership).** An invertible $A$ modulo $\varpi^2$ lies in $\Gamma$ if and only if $\bar\varpi A = \bar\varpi\cdot 1$.

Lean: `New.Rows.DividedSplitting.mem_congruenceGroup_iff` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* The stabiliser condition is $A\cdot(\bar\varpi 1) = \bar\varpi 1$, and $A\cdot\bar\varpi 1 = \bar\varpi A$. $\square$

By the lemma on multiplication by $\varpi$, $\bar\varpi A = \bar\varpi 1$ says $A \equiv 1$ modulo $\varpi$. So $\Gamma$ is the group of matrices that are $1$ modulo $\varpi$.

**Lemma (Inverses of the form $1 - Y$).** Let $Y$ be an $r \times r$ matrix modulo $\varpi^2$ with $\bar\varpi Y = 0$. Then some $A \in \Gamma$ has $A^{-1} = 1 - Y$.

Lean: `New.Rows.DividedSplitting.exists_congruenceGroup_inv_eq_one_sub` (New/OneLift/ComparisonOperator/GluedLattices.lean).

*Proof.* Choose integral lifts $X_{ij}$ of the entries $Y_{ij}$. The equation $\bar\varpi Y = 0$ says $\varpi X_{ij} \equiv 0$ modulo $\varpi^2$. By the lemma on divisibility, $\varpi^{-1}X_{ij}$ is integral. So $\varpi^{-2}X_{ij}X_{jk}$ is integral, and $X_{ij}X_{jk} \equiv 0$ modulo $\varpi^2$. Hence $Y^2 = 0$. A matrix $1 - Y$ with $Y$ nilpotent is a unit, with inverse $1 + Y$. Its inverse $A$ satisfies $\bar\varpi A = \bar\varpi(1 + Y) = \bar\varpi 1$. So $A \in \Gamma$ and $A^{-1} = 1 - Y$. $\square$

### Example: rank one

Let $n = 1$ and let there be one chosen place $w$. Take $C = \varpi$ and $G = 1$, so $CG = \varpi$. The construction gives $c = \varpi_w$ at $w$ and $1$ elsewhere. Then $\gamma_w = \varpi_w$, and $\gamma_{\bar w}$ is the inverse of the conjugate of $\varpi_w$. The lattice $\gamma\mathcal{O}$ at $w$ is $\varpi_w\mathcal{O}_w$, so the inclusion $\varpi\mathcal{O} \subseteq \gamma\mathcal{O}$ is an equality there. The matrix $\varpi\gamma^{-1}$ is $1$ at $w$, $\bar\varpi$ at $\bar w$, and $1$ elsewhere. So $\bar G_L = 1$. Here $\delta = \varpi_w$ and $c_\gamma = \chi(\varpi_w)\,|\varpi_w|^{-r/2}$. The congruence group for $r = 1$ is the group of units $1 + \varpi t$ modulo $\varpi^2$. It has $q_w$ elements, where $q_w$ is the size of the residue field at $w$.

**Remark (Formalization).** A divided lattice records only the point $\gamma$. The textbook lattice $\gamma\mathcal{O}^n$ does not appear. The inclusion $\gamma\mathcal{O}^n \subseteq \mathcal{O}^n$ is not a field of the structure. The proofs use instead that $\bar\varpi\gamma$ is integral, which follows from property 2 and unitarity. The generator $\varpi$ is the generator that the library chooses for the modulus. Its values off the chosen places are $1$, but at a chosen place it is one uniformiser among many. The results of this chapter do not depend on this choice.
