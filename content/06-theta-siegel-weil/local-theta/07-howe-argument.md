---
title: Howe's argument
lean:
  - Lib/DiscreteSeries/Theta/LocalCorrespondence.lean
  - Lib/DiscreteSeries/Theta/FockDualPair.lean
decls:
  - New.Fischer.polyDegreeLE
  - New.Fischer.glOp_mem_polyDegreeLE
  - New.Fischer.perpInDegree
  - New.Fischer.eq_zero_of_mem_perpInDegree
  - New.Fischer.perpInDegree_ne_bot
  - New.Fischer.mapsTo_perpInDegree
  - New.Fischer.fockLaplacian_eq_zero
  - New.Fischer.isLaplaceHarmonic_of_isKHighest
  - New.Fischer.fockLaplacian_eq_zero_of_pderiv_eq_zero
  - New.IsMatch.centredParam_lt_or_lt
  - New.IsMatch.pderiv_eq_zero_of_lt_centredParam
  - New.HCParam.exists_highest_vector
  - New.HCParam.rootCone
  - New.IsJointHarmonic.howe_argument
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Howe's argument

This section proves the algebraic theorem behind the smoothing statement of Section 8. Let $\Phi$ be a joint harmonic. A space $G$ of polynomials that is stable under the column action, contains $\Phi$, and contains three kinds of images of the row operators, is the space of all polynomials. In Section 8, $G$ is the space of polynomials $P$ such that $\pi(e_\lambda)P$ is a smoothing of $\pi(e_\lambda)\Phi$. The three kinds of images are exactly what $\pi(e_\lambda)$ kills.

The proof is an induction on the degree. If $G$ misses a polynomial of degree $j$, the Fischer orthogonal complement of $G$ in degree $j$ is not zero. It contains a highest vector $Q$ for the columns. The hypotheses on $G$ pass to $Q$ by adjunction, and they make $Q$ a pre-joint harmonic. By the uniqueness theorem of Section 5, $Q$ is a multiple of $\Phi \in G$. So $Q$ is orthogonal to itself, and $Q = 0$, a contradiction.

The source calls this "Howe's argument" and cites Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989). The induction on the degree with the Fischer inner product is the classical method for harmonic polynomials. The source applies it to one joint harmonic, not to a full decomposition of the Fock space.

Throughout this section, the inner product is the Fischer inner product of Section 5. All the spaces are spaces of complex polynomials in the variables $X_{rc}$.

### Degree and orthogonal complements

**Definition.** For an integer $j$, let $\mathcal{P}_{\leq j}$ be the space of polynomials of total degree at most $j$. For a subspace $G$, let $G^\perp_j$ be the space of the polynomials of $\mathcal{P}_{\leq j}$ that are orthogonal to $G \cap \mathcal{P}_{\leq j}$.

Lean: `New.Fischer.polyDegreeLE` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The second is `New.Fischer.perpInDegree`.

For $j < 0$ the space $\mathcal{P}_{\leq j}$ is $0$. Each $\mathcal{P}_{\leq j}$ is finite dimensional.

**Lemma.** Let $\eta$ be the signs of the variables. If $P \in \mathcal{P}_{\leq j}$, then $\omega(E_{ab})P \in \mathcal{P}_{\leq i}$ whenever $j + \eta_a \leq i + \eta_b$.

Lean: `New.Fischer.glOp_mem_polyDegreeLE` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* The raising operator of a variable of sign $\eta$ changes the degree by $\eta$, and the lowering operator changes it by $-\eta$. $\square$

In particular, a compact matrix unit of the row action, with $\varepsilon_a = \varepsilon_b$, keeps the degree, and a Laplacian lowers it by $2$.

**Lemma.**
1. If $P \in G^\perp_j$ and $P \in G$, then $P = 0$.
2. If $\mathcal{P}_{\leq j} \not\subseteq G$, then $G^\perp_j \neq 0$.

Lean: `New.Fischer.eq_zero_of_mem_perpInDegree` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The second part is `New.Fischer.perpInDegree_ne_bot` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* In part 1, $P$ is orthogonal to itself. In part 2, $\mathcal{P}_{\leq j}$ is finite dimensional, so it is the orthogonal sum of $\mathcal{P}_{\leq j} \cap G$ and $G^\perp_j$. If $G^\perp_j = 0$, then $\mathcal{P}_{\leq j} \subseteq G$. $\square$

**Lemma.** Let $\varepsilon_a = \varepsilon_b$, and let $N$, $G$ be subspaces with $\rho(E_{ba})N \subseteq G$. Then $\rho(E_{ab})$ maps $G^\perp_j$ into $N^\perp_j$.

Lean: `New.Fischer.mapsTo_perpInDegree` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* For $\varepsilon_a = \varepsilon_b$ the operators $\rho(E_{ab})$ and $\rho(E_{ba})$ keep the degree, and they are adjoint for the Fischer inner product, by the formula of Section 4 for compact matrix units and the adjointness of $X$ and $\partial$. If $P \in G^\perp_j$ and $n \in N \cap \mathcal{P}_{\leq j}$, then $\langle n, \rho(E_{ab})P\rangle = \langle\rho(E_{ba})n, P\rangle = 0$. $\square$

### Fischer's step

**Theorem (Fischer's step).** Let $G \supseteq \mathcal{P}_{\leq k}$ for all $k < j$. Let $P \in G^\perp_j$, let $\varepsilon_a \neq \varepsilon_b$, and let $Q = \Delta_{ab}P$ be the Laplacian. Suppose that $Q \in G$ implies $\rho(E_{ba})Q \in G$. Then $Q = 0$.

Lean: `New.Fischer.fockLaplacian_eq_zero` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* The Laplacian $\Delta_{ab}$ is the sum of the operators $\omega(E_{(a,c)(b,c)})$ over the columns $c$ with $\eta_{ac} = -1$. For these columns $\eta_{bc} = 1$, and each term is $-\partial_{ac}\partial_{bc}$. So $Q$ has degree at most $j - 2$, and $Q \in G$ by the hypothesis on $G$. Put $A_c = \omega(E_{(b,c)(a,c)})Q$. The row action of $E_{ba}$ on $Q$ is $\sigma\sum_c A_c$, so $\sum_c A_c \in G$. Each $A_c$ has degree at most $j$. So $\sum_c A_c$ is orthogonal to $P$. Now compute $\langle Q, Q\rangle = \sum_c\langle Q, -\partial_{ac}\partial_{bc}P\rangle$. For a column with $\eta_{ac} = -1$, adjointness gives $\langle Q, -\partial_{ac}\partial_{bc}P\rangle = -\langle X_{ac}X_{bc}Q, P\rangle = -\langle A_c, P\rangle$. For a column with $\eta_{ac} = 1$, the term $A_c$ is $-\partial_{ac}\partial_{bc}Q$, of degree at most $j - 4$, so it lies in $G$ and is orthogonal to $P$. In total $\langle Q, Q\rangle = -\langle\sum_c A_c, P\rangle = 0$. $\square$

**Theorem.** Let $P$ be $K$-highest of weight $\nu$ for the row action and $l$. Suppose that for all rows $a$, $b$ with $\varepsilon_a \neq \varepsilon_b$, if $\Delta_{ab}P$ is $K$-highest of weight $\nu + e_a - e_b$, then $\Delta_{ab}P = 0$. Then $P$ is Laplace harmonic.

Lean: `New.Fischer.isLaplaceHarmonic_of_isKHighest` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* The Laplacians form a tensor operator under the compact matrix units: by the canonical commutation relations, $[\rho(E_{xz}), \Delta_{ab}]$ is a combination of $\Delta_{xb}$ and $\Delta_{az}$. Each $\Delta_{ab}P$ is a weight vector of weight $\nu + e_a - e_b$. Suppose that some $\Delta_{ab}P$ is not zero. Choose such a pair with $l_b - l_a$ extremal. A compact raising operator $E_{xz}$ kills $P$, and its commutator with $\Delta_{ab}$ involves only $\Delta_{xb}$ with $l_a < l_x$ and $\Delta_{az}$ with $l_z < l_b$. These vanish on $P$ by the choice of the pair. So $\Delta_{ab}P$ is $K$-highest, and the hypothesis gives $\Delta_{ab}P = 0$, a contradiction. The source writes this as an induction on $l_b - l_a$. $\square$

### Pure rows

**Lemma.** Let $\varepsilon_a \neq \varepsilon_b$. If row $b$ of $Q$ has no variable of sign $1$, or row $a$ of $Q$ has no variable of sign $-1$, then $\Delta_{ab}Q = 0$.

Lean: `New.Fischer.fockLaplacian_eq_zero_of_pderiv_eq_zero` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* Each term of the Laplacian is $-\partial_{ac}\partial_{bc}Q$ with $\eta_{ac} = -1$ and $\eta_{bc} = 1$, and one of the two derivatives is $0$. $\square$

**Lemma.** Let $l$ and $l'$ match and let $l_b \leq l_a$. Then $n' - n < -\xi_b$ or $n' - n < \xi_a$.

Lean: `New.IsMatch.centredParam_lt_or_lt` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* Here $\xi_b \leq \xi_a$. If row $a$ is matched with $c$, then $\eta_{ac}\xi_a > |n - n'|$, which gives the second or the first inequality, by the sign of $\eta_{ac}$ and $\xi_b \leq \xi_a$. If row $a$ is free, then $|\xi_a| < n - n'$, so $\xi_a > n' - n$. $\square$

**Lemma.** Let $l$ and $l'$ match. Let $Q$ be $K$-highest of weight $\Lambda$ for the row action, and let the Laplacians of the columns kill $Q$. If $n' - n < s\,\xi_r$, then $\partial_{rc}Q = 0$ for every column $c$ with $\eta_{rc} = -s$.

Lean: `New.IsMatch.pderiv_eq_zero_of_lt_centredParam` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* The sign lemma of Section 3 gives $s\,w_r \geq 0$. The theorem on $D^s_{rr}$ of Section 5 applies. $\square$

### The theorem

Two more tools are needed.

**Proposition.** Let $W$ be a nonzero finite dimensional space that is stable under the compact matrix units $E_{ab}$, $\varepsilon_a = \varepsilon_b$, of a module of $\mathfrak{gl}_n$. Then $W$ contains a nonzero weight vector that is compact primitive for $l$.

Lean: `New.HCParam.exists_highest_vector` (Lib/DiscreteSeries/Rigidity/HighestVectorsAndFiltration.lean).

*Proof.* The weights of $W$ form a finite nonempty set. Take one with the largest pairing with $l$. A compact raising operator sends a weight vector to a weight with a larger pairing, so it kills the weight vectors of that weight. $\square$

**Definition (Cone of positive roots).** The *cone of the positive roots* of $l$ is the set of integer vectors $\beta$ with $o \cdot \beta \leq 0$ for every integer vector $o$ that strictly reverses the order of $l$, that is, $l_j < l_i$ implies $o_i < o_j$.

Lean: `New.HCParam.rootCone` (Lib/DiscreteSeries/Rigidity/RepresentationsAndCasimirs.lean).

The source describes the cone by duality. A root $e_a - e_b$ with $l_b < l_a$ pairs with such an $o$ to $o_a - o_b < 0$, so sums of these roots lie in the cone. Pairing with $o = -l$ shows: if $e_a - e_b$ lies in the cone, then $l_b \leq l_a$.

**Theorem (Howe's argument).** Let $\Phi$ be a joint harmonic for $T$, $l$, $l'$, and let $\Lambda$ be the lowest $K$-type of $l$. Let $G$ be a space of polynomials that is stable under the column action and contains $\Phi$. Suppose that $G$ contains the following.
1. The polynomials $\rho(Y)P$, for every matrix $Y$ and every $P$ that is $K$-highest of a weight $\nu$ for the row action, with $\nu - \Lambda$ not in the cone of the positive roots of $l$.
2. The polynomials $\rho(E_{ba})P$, for every $P$ and all rows with $\varepsilon_a = \varepsilon_b$ and $l_b < l_a$.
3. The polynomials $\rho(E_{aa})P - \Lambda_aP$, for every $P$ and every row $a$.

Then $G$ is the space of all polynomials.

Lean: `New.IsJointHarmonic.howe_argument` (Lib/DiscreteSeries/Theta/LocalCorrespondence.lean).

*Proof.* It suffices to show $\mathcal{P}_{\leq j} \subseteq G$ for every $j$, by strong induction on $j$. For $j < 0$ the space is $0$. Let $j \geq 0$, assume the claim below $j$, and suppose that $\mathcal{P}_{\leq j} \not\subseteq G$. Then $G^\perp_j \neq 0$. The space $G$ is stable under the compact column operators, so $G^\perp_j$ is stable under them, by the adjunction lemma for the swap with $N = G$. The proposition gives $Q \neq 0$ in $G^\perp_j$ that is compact primitive for the column action and $l'$.

*$Q$ has weight $\Lambda$.* By hypothesis 3, $\rho(E_{aa})$ maps $G$ into $G$. The adjunction lemma with $a = b$ shows that $\rho(E_{aa})Q \in G^\perp_j$. So $\rho(E_{aa})Q - \Lambda_aQ$ lies in $G^\perp_j$, and it lies in $G$ by hypothesis 3. So it is $0$.

*$Q$ is compact primitive.* Let $\varepsilon_a = \varepsilon_b$ and $l_b < l_a$. By hypothesis 2, $\rho(E_{ba})$ maps every polynomial into $G$. The adjunction lemma with $N$ the whole space shows that $\rho(E_{ab})Q$ is orthogonal to all of $\mathcal{P}_{\leq j}$. It lies in $\mathcal{P}_{\leq j}$, so it is $0$.

*The Laplacians of the columns kill $Q$.* Apply Fischer's step to the swap. Its hypothesis holds because $G$ is stable under the column action.

*The Laplacians of the rows kill $Q$.* Apply the theorem on $K$-highest polynomials. Let $\varepsilon_a \neq \varepsilon_b$ and let $\Delta_{ab}Q$ be $K$-highest of weight $\Lambda + e_a - e_b$. If $e_a - e_b$ is in the cone, then $l_b \leq l_a$. By the lemma on centred parameters, $n' - n < -\xi_b$ or $n' - n < \xi_a$. In the first case row $b$ of $Q$ has no variable of sign $1$, and in the second case row $a$ has none of sign $-1$, by the last lemma of the subsection on pure rows. So $\Delta_{ab}Q = 0$. If $e_a - e_b$ is not in the cone, then hypothesis 1 applies to $\Delta_{ab}Q$, and $\rho(E_{ba})\Delta_{ab}Q \in G$. Fischer's step gives $\Delta_{ab}Q = 0$.

*Conclusion.* $Q$ is a pre-joint harmonic. So is $\Phi$, by Section 5. By uniqueness, $Q = c\Phi$ for a scalar $c$. Then $Q \in G$, and $Q \in G^\perp_j$, so $Q = 0$. This contradicts $Q \neq 0$. $\square$

The proof shows why the source proves uniqueness for pre-joint harmonics. The vector $Q$ is compact primitive for the columns, but its column weight is not known. Termwise harmonicity is not known either. Only the Laplace conditions come out of Fischer's step.

**Remark (Formalization).** The statement uses the Lean form `G ∈ (T.swap.oscRows Y).invtSubmodule` for every matrix $Y$ for the stability of $G$ under the column action. Hypothesis 1 asks for all complex matrices $Y$, not only the matrix units. The weight $\nu$ in hypothesis 1 is an integer vector, and the cone is a set of integer vectors. The theorem is stated for one joint harmonic. It does not decompose the Fock space, and it does not say that $G$ is irreducible or that the column action on a quotient is irreducible.

### Example

For $U(1,1) \times U(1)$ with row 1 matched, $\Phi = X_1^k$ and $\Lambda = (\gamma + k, \gamma - 1)$. The polynomial ring is $\mathbb{C}[X_1, X_2]$. The column action is spanned by $E' = X_2\partial_2 - X_1\partial_1 + \gamma' + 1$, so stability under it means stability under $X_1\partial_1 - X_2\partial_2$. The two rows have opposite signs, so there are no compact matrix units off the diagonal, and hypothesis 2 is empty. Hypothesis 3 puts $(X_1\partial_1 - k)P$ and $(X_2\partial_2)P$ into $G$, up to signs, for every $P$. So $G$ contains every monomial $X_1^iX_2^m$ with $i \neq k$ or $m \neq 0$. Together with $X_1^k \in G$, this gives all polynomials. Here the conclusion follows from hypothesis 3 alone. In the general case the Laplacians and hypothesis 1 are needed, as monomials with the right weight are not unique.
