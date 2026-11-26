---
title: Neighbours and a reproducing formula
lean:
  - Lib/SiegelWeil/NeighbourLattices.lean
  - Lib/SiegelWeil/Reproduction.lean
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

This section treats one step of Kneser's method of neighbours, and a reproducing formula: a holomorphic pairing of an automorphic function is a finite combination of theta lifts to a large definite group.

### Neighbour vectors

Let $E$ have Weil data, let $L = \widehat{\mathcal O}^n$ with $\langle x, z\rangle = \bar x^{\mathsf T} z$, and let $w$ be a finite place with uniformizer $\varpi$ and residue field $k_w$ of order $q_w$.

**Definition (Neighbour vector).** A vector $x$ of finite adeles is a neighbour vector at $w$ if its components away from $w$ are $0$, $\varpi x \in L$, $x \notin L$, and $\langle x, x\rangle$ is integral. Its neighbour is $L_0 + \widehat{\mathcal O}x$, where $L_0 = \{z \in L : \langle x, z\rangle \text{ integral}\}$. A unitary $\rho$ maps the neighbour into $L$ if $\rho L_0 \subseteq L$ and $\rho x \in L$.
Lean: `New.SiegelWeil.IsNeighbourVector`, `New.SiegelWeil.MapsNeighbour` (Lib/SiegelWeil/NeighbourLattices.lean)

**Theorem (A quasi-reflection maps the neighbour into $L$).** For a neighbour vector $x$ at $w$, there is a unitary $\rho$ supported on $w$ and its conjugate with $\rho L_0 \subseteq L$ and $\rho x \in L$.
Lean: `New.SiegelWeil.IsNeighbourVector.exists_mapsNeighbour`, `New.SiegelWeil.exists_quasiReflection` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* If $c + \bar c = \bar c c \langle u, u\rangle$, the map $z \mapsto z - c\langle u, z\rangle u$ is unitary. Take $u = x + y$ with $y \in L$ the vector with $\langle y, z\rangle = z_k$ at $w$, for a coordinate $x_k$ with a pole, and $c = (x_k + t)^{-1}$ with $t + \bar t = \langle x, x\rangle + \langle y, y\rangle$. $\square$

**Definition (Polar residue and neighbour residues).** For $s$ in the local field at $w$, the polar residue is the class of $\varpi s$ in $k_w$, or $0$ if $\varpi s$ is not integral. The neighbour residues at $w$ are the polar residues of the finite adeles $s$ that are supported at $w$, have a pole of order at most $1$, and have integral trace $s + \bar s$.
Lean: `New.SiegelWeil.polarResidue`, `New.SiegelWeil.neighbourResidues` (Lib/SiegelWeil/NeighbourLattices.lean)

**Theorem (A family of reflections).**

1. If $w$ is split, there is at most one neighbour residue.
2. If $E$ contains a primitive root of unity of order $5040$, then the number $r_w$ of neighbour residues satisfies $r_w^2 \le q_w$.
3. There is a family $\rho$ of unitary elements supported on $w$ and its conjugate, indexed by pairs of a line in $k_w^n$ and a neighbour residue, such that for every neighbour vector $x$ at $w$ some member of the family maps the neighbour of $x$ into $L$.

Lean: `New.SiegelWeil.card_neighbourResidues_le_one`, `New.SiegelWeil.card_neighbourResidues_sq_le`, `New.SiegelWeil.exists_family_mapsNeighbour` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* At a split place an adele supported at $w$ with integral trace is integral, so the only residue is $0$. In general the root of unity gives an integer $y$ with $y - \bar y$ a unit, and $(r, r') \mapsto r + yr'$ is injective from pairs of residues to $k_w$. For part 3, fix a base vector $b_\ell$ for each line $\ell$. A unit multiple $cx$ of $x$ has $cx - b_\ell \in L$, and vectors with the same line and the same residue of $\langle b_\ell, cx - b_\ell\rangle$ share a reflection. $\square$

**Remark (Formalization).** The polar residue $0$ for nonintegral $\varpi s$ is a junk value. The lemmas assume a pole of order at most $1$, so it does not occur. The base vectors and the reflections are chosen by an existential statement. The family has $\#\mathbb{P}(k_w^n) \cdot r_w$ members, with $r_w \le 1$ at split places and $r_w \le \sqrt{q_w}$ in general.

Write $\Delta(\gamma)$ for `finMultiplier γ`. Its squared absolute value is $[L : L \cap \gamma^{-1}L]$.

**Theorem (One step towards $L$).** Let $\gamma$ be a unitary element of the finite adeles.

1. If $\gamma$ does not stabilize $L$, there are a finite place $w$ at which $\gamma$ has a nontrivial component and a vector $z \in L$ such that $\gamma z$ is a neighbour vector at $w$.
2. Let $z \in L$, let $\gamma z$ be a neighbour vector at $w$, and let $\rho$ map its neighbour into $L$. Then $q_w \, |\Delta(\rho\gamma)|^2 \le |\Delta(\gamma)|^2$.

Lean: `New.SiegelWeil.exists_isNeighbourVector_mulVec`, `New.SiegelWeil.q_mul_norm_finMultiplier_mul_sq_le` (Lib/SiegelWeil/NeighbourLattices.lean)

*Proof.* For part 1, take a column of $\gamma$ with a pole at $w$ and scale the basis vector so that the largest pole has order $1$. For part 2, put $H = L \cap \gamma^{-1}L \le K = L \cap (\rho\gamma)^{-1}L$. The multiples of $z$ give $q_w$ classes in $K/H$. $\square$

[The Rallis inner product formula](/chapter/rallis-inner-product/) sums these steps from $\gamma L$ to $\rho\gamma L$ towards $L$.

**Remark (Formalization).** Classically, $L$ and $L'$ are $\mathfrak p$-neighbours when $L \cap L'$ has index $N\mathfrak p$ in each. The source names M. Greenberg and J. Voight, Lattice methods for algebraic modular forms on classical groups (2014), section 5, which this chapter has not checked. The source form is narrower: only the translates $\gamma L$ of the standard lattice, a neighbour given by a vector, one step for split and inert places, and an inequality for the index.

### Holomorphic Fock vectors

The second file works in the Fock model of a pair of unitary groups with signs $s$ and $s'$, as in [local theta](/chapter/local-theta/). A polynomial $P$ in the matrix variables gives a Fock vector $v_P$. The function `holMinorsPi s u` is a product of quotients of minors of weight $u$.

First, let $P$ be a polynomial in the variables of sign $1$ that the substitution of $u^{-1}$ multiplies by powers $\nu$ and $c$ of the two principal minors of $u$. Then its coefficient at $(u, 1)$ is its value at $(1, 1)$ times `holMinorsPi s v u` times the conjugate of `holMinorsPi s k u`, for weights $v$ and $k$ given by $\nu$, $c$, the sign counts of $s'$ and the weight $e$ of the character. The substitution scales each minor of variables by a principal minor of $u$. Powers of the minor of the positive columns and the polynomials `letterPoly` give such vectors.
Lean: `New.Rows.polyMatrixCoeff_eq_holMinorsPi_mul_conj`, `New.Rows.prod_variableMinor_mem_holomorphicData`, `New.Rows.letterPoly_highestVector_mem_holomorphicData` (Lib/SiegelWeil/Reproduction.lean)

Second, let $Y$ be an invertible matrix over $E$. Every element $y$ of the definite second group maps the Fock vector of the $d$-th power of the minor into the span of the Fock vectors of the products `pairedDetProd` of determinants of rows of $Y$ times the positive columns of variables. Here $(1, y)$ acts by a scalar times the substitution of $y^{\mathsf T}$ on the positive columns, and the determinant is multilinear in its rows.
Lean: `New.Rows.realPairWeil_mem_span_pairedDetProd` (Lib/SiegelWeil/Reproduction.lean)

### The reproducing formula

**Lemma (A vanishing lift kills the holomorphic convolution).** Assume hypotheses 1 to 4 of the reproducing formula below, without the condition on $c$. Let $\psi$ be rapidly decreasing of level $N$. If the lift of $\psi$ by the datum of $Q_0$ and of the indicator of the matrix of $e : n \hookrightarrow n'$ modulo $\mathfrak m$ vanishes, then the convolution of $\psi$ with `holMinorsPi s u` over the real points is $0$.
Lean: `New.Rows.realConv_holMinorsPi_eq_zero_of_lift_eq_zero` (Lib/SiegelWeil/Reproduction.lean)

*Proof.* The matrix coefficient of $v_0 = v_{Q_0}$ is $\langle v_0, v_0\rangle \cdot$ `holMinorsPi s u`, with $\langle v_0, v_0\rangle \neq 0$. The indicator datum is sharp for the level $1 \bmod \mathfrak m$, so the injectivity of the theta lift for sharp data in [the Rallis inner product formula](/chapter/rallis-inner-product/) applies. $\square$

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

*Proof.* By linear algebra it is enough that the left side vanishes at $\psi$ when all the pairings on the right do. At a point $\gamma p k y$ of the definite group, with $y$ real, the lift by $Q_0$ is a functional of the translate of $v_{Q_0}$ by $y$, which lies in the span of the $v_{Q_{p,i}}$ by hypothesis 5. So that lift vanishes (`lift_modDatum_eq_zero_of_mem_span`), and the lemma gives $\ell(\psi) = 0$. $\square$

**Remark (Formalization).** The constants $a_{p,i}$ come from an existence statement in linear algebra. They depend on $x$, are not computed, and may be $0$. Classically, holomorphic forms in the stable range are spanned by theta series. The source names S. Böcherer, Math. Z. 183 (1983), and J.-S. Li, J. Reine Angew. Math. 428 (1992), which this chapter has not checked.

[The comparison operator, part 2](/chapter/comparison-operator-2/) uses the reproducing formula for Theorem C.
