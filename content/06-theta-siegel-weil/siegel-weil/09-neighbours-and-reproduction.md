---
title: Neighbours and a reproducing formula
lean:
  - Lib/SiegelWeil/NeighbourLattices.lean
  - Lib/SiegelWeil/Reproduction.lean
  - Lib/SiegelWeil/RallisInner/SharpData.lean
decls:
  - New.SiegelWeil.IsNeighbourVector
  - New.SiegelWeil.MapsNeighbour
  - New.SiegelWeil.polarResidue
  - New.SiegelWeil.neighbourResidues
  - New.SiegelWeil.card_neighbourResidues_le_one
  - New.SiegelWeil.card_neighbourResidues_sq_le
  - New.SiegelWeil.IsNeighbourVector.exists_mapsNeighbour
  - New.SiegelWeil.exists_family_mapsNeighbour
  - New.SiegelWeil.exists_isNeighbourVector_mulVec
  - New.SiegelWeil.q_mul_norm_finMultiplier_mul_sq_le
  - New.Rows.polyMatrixCoeff_eq_holMinorsPi_mul_conj
  - New.Rows.prod_variableMinor_mem_holomorphicData
  - New.Rows.realPairWeil_mem_span_pairedDetProd
  - New.Rows.letterPoly_highestVector_mem_holomorphicData
  - New.Rows.realConv_holMinorsPi_eq_zero_of_lift_eq_zero
  - New.Rows.lift_modDatum_eq_zero_of_mem_span
  - New.Rows.reproducing_formula_modKernel
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Neighbours and a reproducing formula

This section treats the two remaining files of Lib/SiegelWeil that belong to this chapter. The first is a step of Kneser's method of neighbours for the standard lattice. The second is a reproducing formula: a holomorphic pairing of an automorphic function is a finite combination of theta lifts to a large definite group. The first file feeds the Rallis series. The second uses the injectivity of the theta lift. The doubling method, the sharp data and the Rallis series are in [the Rallis inner product formula](/chapter/rallis-inner-product/). This section uses one result from there, the injectivity of the theta lift for sharp data, and states it in one line.

### Neighbour vectors

Let $E$ be a CM field with Weil data, let $L = \widehat{\mathcal O}^n$ be the standard lattice with the form $\langle x, z\rangle = \bar x^{\mathsf T} z$, and let $w$ be a finite place of $E$. Let $\varpi$ be the chosen uniformizer at $w$ and $q_w$ the order of the residue field $k_w$.

**Definition (Neighbour vector).** A vector $x$ of finite adeles is a neighbour vector at $w$ if these four conditions hold.

1. The components of $x$ away from $w$ are $0$.
2. Each coordinate has a pole of order at most $1$ at $w$, so $\varpi x \in L$.
3. Some coordinate has a pole of order exactly $1$ at $w$, so $x \notin L$.
4. The norm $\langle x, x\rangle$ is integral.

Lean: `New.SiegelWeil.IsNeighbourVector` (Lib/SiegelWeil/NeighbourLattices.lean)

A neighbour vector defines the neighbour $L_1 = L_0 + \widehat{\mathcal O}x$, where $L_0$ is the lattice of the $z \in L$ with $\langle x, z\rangle$ integral. A unitary element $\rho$ maps the neighbour into $L$, `MapsNeighbour ρ x`, if $\rho L_0 \subseteq L$ and $\rho x \in L$.
Lean: `New.SiegelWeil.MapsNeighbour` (Lib/SiegelWeil/NeighbourLattices.lean)

**Theorem (A quasi-reflection maps the neighbour into $L$).** For a neighbour vector $x$ at $w$, there is a unitary $\rho$ supported on $w$ and its conjugate with $\rho L_0 \subseteq L$ and $\rho x \in L$.
Lean: `New.SiegelWeil.IsNeighbourVector.exists_mapsNeighbour`, `New.SiegelWeil.exists_quasiReflection` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* Let $x_k$ have a pole, and let $y \in L$ be the vector with $\langle y, z\rangle = z_k$ at $w$ and $0$ elsewhere. Let $u = x + y$. For a vector $u$ supported on a set of places and its conjugate, and a scalar $c$ with $c + \bar c = \bar c c \langle u, u\rangle$, the map
$$
z \mapsto z - c\langle u, z\rangle u
$$
is unitary, by `exists_quasiReflection`. Its matrix is $1 - cP$ with $P = u\bar u^{\mathsf T}$, and $P^2 = \langle u, u\rangle P$. The proof takes $c = (x_k + t)^{-1}$, where $t$ has trace $\langle x, x\rangle + \langle y, y\rangle$. Such a $t$ exists by `exists_add_star_eq`, which uses the element of trace $1$ in the Weil data. The reflection then sends $x$ and $L_0$ into $L$. $\square$

### How many reflections are needed

The source shows that a finite family of reflections serves all neighbour vectors at $w$. The family is indexed by a line in $k_w^n$ and a residue class.

**Definition (Polar residue and neighbour residues).** For $s$ in the local field at $w$, the polar residue is the class of $\varpi s$ in $k_w$, or $0$ if $\varpi s$ is not integral. The neighbour residues at $w$ are the polar residues of the finite adeles $s$ that are supported at $w$, have a pole of order at most $1$, and have integral trace $s + \bar s$.
Lean: `New.SiegelWeil.polarResidue`, `New.SiegelWeil.neighbourResidues` (Lib/SiegelWeil/NeighbourLattices.lean)

**Remark (Formalization).** The polar residue has a junk value. It is $0$ when $\varpi s$ is not integral. All the lemmas that use it assume that $s$ has a pole of order at most $1$, so the junk value does not occur in them.

**Theorem (Number of neighbour residues).**

1. If $w$ is split, there is at most one neighbour residue.
2. If $E$ contains a primitive root of unity of order $5040$, then the number $r_w$ of neighbour residues satisfies $r_w^2 \le q_w$.

Lean: `New.SiegelWeil.card_neighbourResidues_le_one`, `New.SiegelWeil.card_neighbourResidues_sq_le` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* For part 1, at a split place the components at $w$ and $\bar w$ are independent. An integral trace of an adele supported at $w$ makes it integral, so the only residue is $0$. For part 2, the root of unity gives an integer $y$ of $E$ with $y - \bar y$ a unit. The map $(r, r') \mapsto r + yr'$ is injective on pairs of neighbour residues, with values in $k_w$. $\square$

**Theorem (A family of reflections).** There is a family $\rho$ of unitary elements supported on $w$ and its conjugate, indexed by pairs of a line in $k_w^n$ and a neighbour residue, such that for every neighbour vector $x$ at $w$ some member of the family maps the neighbour of $x$ into $L$.
Lean: `New.SiegelWeil.exists_family_mapsNeighbour` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* For each line $\ell$ that occurs as the line of $\varpi x$, choose a base vector $b_\ell$ with this line. For a neighbour vector $x$ with line $\ell$, there is a unit $c$ with $cx - b_\ell \in L$. The polar residue of $\langle b_\ell, cx - b_\ell\rangle$ is a neighbour residue. Two vectors with the same line and the same residue are mapped into $L$ by the same reflection, and a unit multiple of $x$ has the same neighbour. $\square$

**Remark (Formalization).** The family is a choice. The base vectors $b_\ell$ and the reflections are chosen by an existential statement, and only their existence is used. The line of $x$, `IsNeighbourVector.line`, is the line of $\varpi x$ in $k_w^n$. The index set of the family has $\#\mathbb{P}(k_w^n) \cdot r_w$ elements, with $r_w \le 1$ at split places and $r_w \le \sqrt{q_w}$ in general.

### One step towards the standard lattice

For a unitary $\gamma$ of the finite adeles, write $\Delta(\gamma)$ for `finMultiplier γ`. Its squared absolute value is the index $[L : L \cap \gamma^{-1}L]$.

**Theorem (A lattice other than $L$ holds a neighbour vector).** If $\gamma$ does not stabilize $L$, there are a finite place $w$ at which $\gamma$ has a nontrivial component and a vector $z \in L$ such that $\gamma z$ is a neighbour vector at $w$.
Lean: `New.SiegelWeil.exists_isNeighbourVector_mulVec` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* Some entry of $\gamma$ has a pole at some place $w$. Take a column $j$ with such a pole, and scale the $j$-th basis vector at $w$ so that the largest pole has order $1$. The norm of $\gamma z$ equals the norm of $z$, which is integral. $\square$

**Theorem (One step lowers the index).** Let $z \in L$, let $\gamma z$ be a neighbour vector at $w$, and let $\rho$ map its neighbour into $L$. Then
$$
q_w \, |\Delta(\rho\gamma)|^2 \le |\Delta(\gamma)|^2.
$$
Lean: `New.SiegelWeil.q_mul_norm_finMultiplier_mul_sq_le` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* Put $H = L \cap \gamma^{-1}L$ and $K = L \cap (\rho\gamma)^{-1}L$. Then $H \le K$. The multiples of $z$ give $q_w$ different classes in $K/H$. So $[L : H] \ge q_w [L : K]$. $\square$

So a step from $L$ to a neighbour towards $\gamma L$ is read as a step from $\gamma L$ to $\rho\gamma L$ towards $L$. This file treats one step. The steps are summed in the weights `stepWeight` of the Rallis series, in [the Rallis inner product formula](/chapter/rallis-inner-product/).

**Remark (Formalization).** In the classical theory of Kneser, two lattices $L$ and $L'$ are $\mathfrak p$-neighbours when $L \cap L'$ has index $N\mathfrak p$ in each. The source names M. Greenberg and J. Voight, Lattice methods for algebraic modular forms on classical groups (2014), section 5, for this. This chapter has not checked that section. The source form is narrower. It treats only the standard lattice over $\widehat{\mathcal O}$ and its translates $\gamma L$ by unitary elements. It defines a neighbour by a vector $x$, not by a pair of lattices. It treats split and inert places by the same step, taken at $w$ or at $\bar w$. It proves an inequality for the index, not an equality.

### Holomorphic Fock vectors

The second file works in the Fock model of a pair of unitary groups with signs $s$ and $s'$ at the infinite places, as in [local theta correspondence](/chapter/local-theta/). A polynomial $P$ in the matrix variables gives a Fock vector $v_P$. The function `holMinorsPi s u` is the product over the infinite places of quotients of minors of weight $u$.

**Theorem (Coefficients of products of minors).** Let $P$ be a polynomial in the variables of sign $1$ that the substitution of $u^{-1}$ multiplies by powers $\nu$ and $c$ of the two principal minors of $u$. Then its coefficient at $(u, 1)$ is its value at $(1, 1)$ times `holMinorsPi s v u` times the conjugate of `holMinorsPi s k u`, for weights $v$ and $k$ given by $\nu$, $c$, the sign counts of $s'$ and the weight $e$ of the character.
Lean: `New.Rows.polyMatrixCoeff_eq_holMinorsPi_mul_conj`, `New.Rows.linSubst_variableMinor` (Lib/SiegelWeil/Reproduction.lean)

*Proof.* The substitution of $u^{-1}$ multiplies the transposed matrix of variables by the block of $u$ on the indices of one sign. Take determinants: a minor of variables is scaled by a principal minor of $u$. Both sides are then products of powers of $\det u$ and of its two principal minors, all nonzero. $\square$

The source gives two families of nonzero holomorphic vectors. The first is a power of the minor of the positive columns, for signs $+1$ on $p$ and $-1$ on $q$ and a definite second space. The second is the polynomial `letterPoly` of a highest weight vector, with a staircase weight.
Lean: `New.Rows.prod_variableMinor_mem_holomorphicData`, `New.Rows.letterPoly_highestVector_mem_holomorphicData` (Lib/SiegelWeil/Reproduction.lean)

**Theorem (Translates of a power of a minor).** Let $Y$ be an invertible matrix over $E$. An element $y$ of the definite second group maps the Fock vector of the $d$-th power of the minor into the span of the Fock vectors of the products `pairedDetProd`. These are products of determinants of rows of $Y$ times the positive columns of variables.
Lean: `New.Rows.realPairWeil_mem_span_pairedDetProd` (Lib/SiegelWeil/Reproduction.lean)

*Proof.* The element $(1, y)$ acts as a scalar times a linear substitution of the variables. Only its effect on the positive columns matters, where it substitutes $y^{\mathsf T}$. As $Y$ is invertible, the rows of $y^{\mathsf T}$ are combinations of the rows of $Y$. The determinant is multilinear in its rows, so each substituted minor is a combination of minors in the rows of $Y$. $\square$

This span condition is the hypothesis (e) of the reproducing formula below.

### Injectivity and the reproducing formula

From [the Rallis inner product formula](/chapter/rallis-inner-product/) the source uses one result: for a sharp datum and rank $\#n' > 2\#n$, if the theta lift of a rapidly decreasing $y$ vanishes, then so does the convolution of $y$ with the matrix coefficient of the Fock vector.
Lean: `New.SiegelWeil.realConv_eq_zero_of_lift_eq_zero`, `New.SiegelWeil.isSharp_vacuumDatum_of_mul_eq_one` (Lib/SiegelWeil/RallisInner/SharpData.lean)

**Theorem (A vanishing lift kills the holomorphic convolution).** Let the order $O$ put the sign $+1$ first, let $u$ be $K$-dominant with `holMinorsPi s u` integrable, let $\mathfrak m = (N)$ have a prime divisor, let $b$ have weight $\gamma$ and trivial tame part, and let $\#n' > 2\#n$. Let $Q_0 \neq 0$ have a holomorphic Fock vector of weight $u$. Let $\psi$ be rapidly decreasing of level $N$. If the lift of $\psi$ by the datum of $Q_0$ and of the indicator of the matrix of $e : n \hookrightarrow n'$ modulo $\mathfrak m$ vanishes, then the convolution of $\psi$ with `holMinorsPi s u` over the real points is $0$.
Lean: `New.Rows.realConv_holMinorsPi_eq_zero_of_lift_eq_zero` (Lib/SiegelWeil/Reproduction.lean)

*Proof.* Let $\varphi$ be the matrix coefficient of $v_0 = v_{Q_0}$. It satisfies $\varphi(h^{-1}) = \overline{\varphi(h)}$, and it is holomorphic. So $\varphi = \langle v_0, v_0\rangle \cdot$ `holMinorsPi s u`. The finite datum of the indicator is sharp for the level $1 \bmod \mathfrak m$, under which $\psi$ is invariant. Injectivity gives that the convolution of $\psi$ with $\varphi$ is $0$. The inner product $\langle v_0, v_0\rangle$ is not $0$, because $Q_0 \neq 0$. $\square$

**Theorem (Reproducing formula).** Let the order $O$ put the sign $+1$ first, and let $S$ be a hermitian space over $E$ of signs $s$. Assume:

1. $\mathfrak m = (N)$ has a prime divisor, and the characters $c$ and $b$ have weights $\gamma'$ and $\gamma$ and trivial tame part;
2. $u$ is $K$-dominant for $O$, and `holMinorsPi s u` is integrable;
3. the definite space of rank $\#n'$ has more than twice the rank of $S$;
4. $Q_0 \neq 0$, and its Fock vector is holomorphic of weight $u$;
5. for each class $p$ of level $N$ of the definite group, the span of the Fock vectors of a finite family $Q_{p,i}$ contains the translates of $v_{Q_0}$ by the real points of that group.

Then for each point $x$ there are constants $a_{p,i}$ such that, for all $\psi$ rapidly decreasing, automorphic and of level $N$,
$$
\int_h \psi(x(h, 1)) \, \mathrm{holMinorsPi}(h) \, dh = \sum_{p, i} a_{p,i} \int_{[G_S]} \psi(g) \, \Theta_{p,i}(g) \, dg,
$$
where $\Theta_{p,i}$ is the theta kernel `modKernelStdSpace` at the class $p$ with polynomial $Q_{p,i}$ and the indicator of the matrix of $e$ modulo $\mathfrak m$.
Lean: `New.Rows.reproducing_formula_modKernel`, `New.Rows.lift_modDatum_eq_zero_of_mem_span` (Lib/SiegelWeil/Reproduction.lean)

*Proof.* Both sides are linear functionals of $\psi$ on the space of rapidly decreasing functions of level $N$. Let $\ell$ be the left side and $L_{p,i}$ the functionals on the right. By linear algebra, $\ell$ is a combination of the $L_{p,i}$ if every $\psi$ in the kernel of all $L_{p,i}$ is in the kernel of $\ell$. Let $\psi$ be such. Every point of the definite group is a rational point times a class representative $p$ times an element of the level times a real point $y$. The datum is fixed by the level, and the lift is invariant under the rational points. The lift by $Q_0$ at such a point is a linear functional of the translate of $v_{Q_0}$ by $y$. By hypothesis 5 this translate is in the span of the $v_{Q_{p,i}}$, on which the functional vanishes. So the lift by $Q_0$ vanishes everywhere, by `lift_modDatum_eq_zero_of_mem_span`. The previous theorem then gives $\ell(\psi) = 0$. $\square$

**Remark (Formalization).** The constants $a_{p,i}$ come from an existence statement in linear algebra. They depend on $x$ and are not computed. Some of them may be $0$. The source names S. Böcherer, Math. Z. 183 (1983), and J.-S. Li, J. Reine Angew. Math. 428 (1992), for the basis problem in the stable range. This chapter has not checked those papers. The classical statement is that holomorphic forms in the stable range are spanned by theta series. The source form is a unitary version at a fixed level. It is stated pointwise, for one holomorphic discrete series coefficient, and it is deduced from injectivity by linear duality. It does not say that the lifts span a space of forms.

The reproducing formula is used for the comparison operator of Theorem C, in [the comparison operator, part 2](/chapter/comparison-operator-2/).
