---
title: The vacuum of the neighbour lattice
lean:
  - New/UpperBound/Seesaw/NeighbourVacuum.lean
decls:
  - New.Seesaw.stdPairSpace
  - New.Seesaw.gluedTranslate
  - New.Seesaw.IsAdmissibleEval
  - New.Seesaw.semichar_eq_one_of_smul_eq
  - New.Seesaw.star_neighbourTranslation_dotProduct_eq_zero
  - New.Seesaw.finHeisenbergOp_neighbourTranslation_add
  - New.Seesaw.finHeisenbergOp_comm_neighbourTranslation
  - New.Seesaw.v_selfOrConj_eq_one
  - New.Seesaw.exists_finHeisenbergOp_vacElem_eq_of_coprime
  - New.Seesaw.finHeisenbergOp_vacElem_eq_smul_arrowTensor
  - New.Seesaw.arrowTensor_doubleLiftGluing
  - New.Seesaw.exists_sum_finHeisenbergOp_neighbourTranslation_eq
  - New.Seesaw.isAdmissibleCombination_finHeisenbergOp_sum_neighbourCosetRep
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The vacuum of the neighbour lattice

Section 2 gave representatives $r(y, q) = n(y) + \tilde q$ of the neighbour lattice $L$ modulo its integral points. This section adds up the translates of the vacuum by these representatives, and reads the sum on the two edges of the pair. The answer is an admissible combination of glued translates, with denominator the number of matrices modulo $\beta$ and size $1$. Section 4 shows that the finite evaluation of a pair produces exactly this kind of sum.

The setting of Section 2 stays fixed: $N$ prime and split as $P$ and $\bar P$, $\pi$ split squarefree for $N$ at $P$, and $\kappa$ a scaling at $M$ for $(N, \beta, \delta)$.

### Spaces and translates

The pair space is $\mathrm{Hom}(X', (X \sqcup \{e\})^- \oplus (X'' \sqcup \{e''\}))$ for the standard definite spaces on $X$, $X'$ and $X''$ with one added basis vector each on the outer spaces. Its coordinates are the matrices of Section 2.

Lean: `New.Seesaw.stdPairSpace` (New/UpperBound/Seesaw/NeighbourVacuum.lean).

Write $\rho(x)$ for the normalised finite Heisenberg operator of a finite adelic matrix $x$, and $\phi_0$ for the vacuum, on any of these spaces ([the Weil representation](/chapter/weil-representation/)). Two facts about $\rho$ are used.

1. *Composition.* $\rho(x)\rho(y) = \psi(\bar\tau\, y^* x)\,\rho(x + y)$, where $\psi$ is the standard additive character `selfDualAddChar` and $\tau$ is the adele `traceOneAdele`. The factor is a root of unity. (Lean: `New.Space.finHeisenbergOp_finHeisenbergOp`.)
2. *Two edges.* The map $\Phi \otimes \Psi \mapsto \Phi \boxtimes \Psi$ (`arrowProduct`) joins data on $\mathrm{Hom}(V, V')$ and $\mathrm{Hom}(V', V'')$ into a datum on $\mathrm{Hom}(V', V^- \oplus V'')$. Its linear extension to the tensor product is `arrowTensor`, which has a left inverse. For a matrix $z$ with blocks $z_1$ (rows in $V$) and $z_2$ (rows in $V''$),
$$\rho(z)(\Phi \boxtimes \Psi) = s(z_1)^2\,\bigl(\rho(\eta z_1^*)\Phi\bigr) \boxtimes \bigl(\rho(z_2)\Psi\bigr),$$
where $s$ is the root of unity $s(x) = \psi(\tau x^*x/2)$ (Lean: `New.Seesaw.finHeisenbergOp_arrowProduct`, `New.stdLattice.semichar`).

The vacuum of the pair space is $\phi_0 \boxtimes \phi_0$. So fact 2 gives the translates of the vacuum on the two edges.

**Lemma (Translates of the vacuum on two edges).** For every matrix $z$ on the pair space,

$$\rho(z)\phi_0 = s(z_1)^2\ \mathrm{arrowTensor}\bigl(\rho(\eta z_1^*)\phi_0 \otimes \rho(z_2)\phi_0\bigr).$$

Lean: `New.Seesaw.finHeisenbergOp_vacElem_eq_smul_arrowTensor`.

**Definition (Glued translate).** For matrices $t_1$ on $\mathrm{Hom}(X \sqcup \{e\}, X')$ and $t_2$ on $\mathrm{Hom}(X', X'' \sqcup \{e''\})$, the glued translate $G(t_1, t_2)$ is the gluing `doubleLiftGluing` applied to $\rho(t_1)\phi_0 \otimes \rho(t_2)\phi_0$.

Lean: `New.Seesaw.gluedTranslate`.

The gluing is defined in [columns and the composite lift](/chapter/upper-bound-objects/): it is the sum over $y : X' \to P \to \mathbb Z/N$ of the translation of the first factor by the pole column $c(y)$, with last column $-y/N$, and of the second factor by the pole row $r(y)$, with last row $-\overline{y/N}$. The glued tensors of the composite lift are built from these vectors.

### The gluing is the sum over the translations $n(y)$

**Lemma (Translations supported at $\bar P$).** If a vector $x$ satisfies $\bar jx = x$, then $s(x) = 1$.

Lean: `New.Seesaw.semichar_eq_one_of_smul_eq`.

*Proof.* $x^*x = (\bar jx)^*(\bar jx) = j\bar j\,x^*x = 0$, since $\bar{\bar j} = j$ and $j\bar j = 0$. So $s(x) = \psi(0) = 1$. $\square$

**Theorem (The gluing on the pair space).** For every tensor $t$ of finite data on the two edges,

$$\mathrm{arrowTensor}(\mathrm{Glue}\ t) = \sum_{y} \rho(n(y))\,\mathrm{arrowTensor}(t).$$

Lean: `New.Seesaw.arrowTensor_doubleLiftGluing`.

*Proof.* Both sides are linear in $t$, so let $t = \Phi \otimes \Psi$. Apply fact 2 with $z = n(y)$. The first block of $n(y)$ has the single nonzero row $\eta\,\overline{y/N}$ at $e$. So $\eta\, n(y)_1^*$ has the single nonzero column $\eta\bar\eta\,(y/N) = -y/N$ at $e$, which is the pole column $c(y)$. The second block of $n(y)$ is the row $-\overline{y/N}$ at $e''$, which is the pole row $r(y)$. The first block is supported at $\bar P$, so $s(n(y)_1) = 1$ by the lemma. Hence $\rho(n(y))(\Phi \boxtimes \Psi) = (\rho(c(y))\Phi) \boxtimes (\rho(r(y))\Psi)$. Sum over $y$. $\square$

**Corollary (The glued sum of one translate).** Let $z$ be a matrix with $\mathrm{selfOrConj}(\beta)_b\,z_{b,a}$ integral away from $n$. Then there are a root of unity $\zeta$ and matrices $t_1$, $t_2$, with $\bar\beta t_1$ and $\bar\beta t_2$ integral away from $n$, such that

$$\sum_{y}\rho(n(y))\rho(z)\phi_0 = \zeta\ \mathrm{arrowTensor}\bigl(G(t_1, t_2)\bigr).$$

Lean: `New.Seesaw.exists_sum_finHeisenbergOp_neighbourTranslation_eq`.

*Proof.* Take $t_1 = \eta z_1^*$, $t_2 = z_2$ and $\zeta = s(z_1)^2$. The lemma on two edges and the theorem give the identity. The first block of $z$ has $\beta z_1$ integral away from $n$, so $\bar\beta t_1 = \eta\,\overline{\beta z_1}^{\mathsf T}$ is integral there. The second block has $\bar\beta z_2$ integral there, and $t_2 = z_2$. $\square$

### Commutation with translations away from $N$

**Lemma (Orthogonality).** If $x$ vanishes above $N$, then $n(y)^*x = 0$. Hence $\rho(n(y) + x) = \rho(n(y))\rho(x)$ and $\rho(x)\rho(n(y)) = \rho(n(y))\rho(x)$.

Lean: `New.Seesaw.star_neighbourTranslation_dotProduct_eq_zero`, `New.Seesaw.finHeisenbergOp_neighbourTranslation_add`, `New.Seesaw.finHeisenbergOp_comm_neighbourTranslation`.

*Proof.* $n(y)$ is fixed by the idempotent $\epsilon$ of the places above $N$, and $\epsilon x = 0$. So $n(y)^*x = (\epsilon n(y))^*x = n(y)^*(\epsilon x) = 0$. By the composition law, $\rho(n(y))\rho(x) = \psi(\bar\tau\,x^*n(y))\rho(n(y) + x)$, and $x^*n(y) = \overline{n(y)^*x} = 0$. The commutator of $\rho(x)$ and $\rho(n(y))$ is a value of $\psi$ at a multiple of $n(y)^*x$, so it is $1$. $\square$

### Removing the part above $N$

The data of the tower are translates of the vacuum by matrices with denominators at the places of $\beta$. The next lemma removes their part above $N$, which costs only a root of unity.

**Lemma.** If $\kappa$ is a scaling at $M$, then $\mathrm{selfOrConj}(\beta)_b$ is a unit at every place above $N$.

Lean: `New.Seesaw.v_selfOrConj_eq_one`.

*Proof.* $\beta$ is a unit above $N$ by condition (3) of the scaling. The conjugate of a place above $N$ lies above $N$, so $\bar\beta$ is a unit there too. $\square$

**Proposition (Translates away from $N$).** Let $n$ be prime to $N$, and let $W$ be a hermitian space on matrices with two blocks of rows. Let $y$ have $\mathrm{selfOrConj}(\beta)\,y$ integral away from $n$. Then there are a root of unity $\zeta$ and a matrix $y'$, with the same property, vanishing above $N$, such that $\rho(y)\phi_0 = \zeta\,\rho(y')\phi_0$.

Lean: `New.Seesaw.exists_finHeisenbergOp_vacElem_eq_of_coprime`.

*Proof.* Let $l = \epsilon y$ be the part of $y$ above $N$. The places above $N$ are prime to $n$, so $\mathrm{selfOrConj}(\beta)\,y$ is integral there. By the lemma $\mathrm{selfOrConj}(\beta)$ is a unit there, so $l$ is integral. It also has the denominator property, since it is $0$ elsewhere. Put $y' = y - l$, which vanishes above $N$ and has the property. Translation of the vacuum by the integral vector $-l$ gives a root of unity times the vacuum translated by the sum (Lean: `New.Seesaw.exists_finHeisenbergOp_add_vacElem`). So $\rho(y)\phi_0 = \zeta\rho(y - l)\phi_0$. $\square$

### The main theorem

**Definition (Admissible evaluation).** A map $\mathcal L$ from data on a pair space $\mathrm{Hom}(V', V^- \oplus V'')$ to tensors of finite data on the two standard edges is an admissible evaluation for $(N, P, \beta)$ with weights $d$ if there is a constant $C$ with the following property. For every $n$ prime to $N$, every proposition $p$, and every $y$ with $d_b\,y_{b,a}$ integral away from $n$, the vector $\mathcal L(\rho(y)\phi_0)$ is an admissible combination of the vectors $C\,G(t_1, t_2)$, over $\bar\beta t_1$ and $\bar\beta t_2$ integral away from $n$, with denominator $\#\bigl(\hat{\mathcal O}/(\beta)\bigr)^{\mathrm{PairIndex}\times X'}$ away from $n$ and size $1$ under $p$.

Lean: `New.Seesaw.IsAdmissibleEval`.

The constant $C$ is an existential and may be $0$. With $C = 0$ every vector $G(t_1, t_2)$ is multiplied by $0$, so only $0$ is a combination. The proofs below give a specific $C$, and Section 4 records it.

**Theorem (The sum over the neighbour lattice).** Let $x$ vanish above $N$, with $\mathrm{selfOrConj}(\beta)\,x$ integral away from $n$. Let $K$ be the order of the away quotient $Q$. Let $p$ be any proposition. Then the left inverse of arrowTensor applied to

$$\rho(x)\sum_{(y, q)}\rho\bigl(r(y, q)\bigr)\phi_0$$

is an admissible combination of the vectors $K\cdot G(t_1, t_2)$, over $\bar\beta t_1$ and $\bar\beta t_2$ integral away from $n$, with denominator $\#\bigl(\hat{\mathcal O}/(\beta)\bigr)^{\mathrm{PairIndex}\times X'}$ away from $n$ and size $1$ under $p$.

Lean: `New.Seesaw.isAdmissibleCombination_finHeisenbergOp_sum_neighbourCosetRep`.

*Proof.* Split the sum over $(y, q)$ as a sum over $q$ of sums over $y$. The representative $\tilde q$ vanishes above $N$. By the orthogonality lemma, $\rho(r(y, q)) = \rho(n(y))\rho(\tilde q)$, and $\rho(x)$ commutes with $\rho(n(y))$. So the vector is $\sum_q T_q$ with

$$T_q = \sum_y \rho(n(y))\,\rho(x)\rho(\tilde q)\phi_0 = \xi_q\sum_y\rho(n(y))\,\rho(x + \tilde q)\phi_0,$$

where $\xi_q = \psi(\bar\tau\,\tilde q^*x)$ is a root of unity by the composition law. The matrix $x + \tilde q$ has $\mathrm{selfOrConj}(\beta)(x + \tilde q)$ integral away from $n$: for $x$ by hypothesis, and for $\tilde q$ by the corollary on weighted translations of Section 2. By the corollary on the glued sum, $T_q = \xi_q\zeta_q\,\mathrm{arrowTensor}(G(t_{1,q}, t_{2,q}))$ with $\bar\beta t_{i,q}$ integral away from $n$. Apply the left inverse:

$$\sum_q \xi_q\zeta_q\,G(t_{1,q}, t_{2,q}) = \sum_q \frac{1}{K}\,\xi_q\zeta_q\,\bigl(K\cdot G(t_{1,q}, t_{2,q})\bigr).$$

Let $D$ be the number of matrices modulo $\beta$. By the proposition on the order of the away quotient, $K \mid D$, so $D/K$ is an integer and lies in $\mathcal O_{(n)}$. The absolute values $|\sigma(1/K)|$ add up to $K \cdot 1/K = 1$ over the $K$ classes. So the combination with coefficients $1/K$ is admissible with denominator $D$ and size $1$, by the lemma on finite sums of [admissible combinations](/chapter/seesaw-identity-1/). Multiplying each vector by the root of unity $\xi_q\zeta_q$ keeps it admissible, by `New.Seesaw.IsAdmissibleCombination.of_eq_isOfFinOrder_smul`. $\square$

**Remark (Formalization).** The proposition `boundHyp` is arbitrary in the Lean statement, so the size bound holds with no hypothesis. The representatives $\tilde q$ are `Quotient.out` choices, and the theorem holds for this choice. The number $K$ is the order of a finite group, so $K \geq 1$, and the division by $K$ in the proof is a genuine inverse.
