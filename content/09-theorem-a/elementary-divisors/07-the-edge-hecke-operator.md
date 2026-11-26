---
title: The edge Hecke operator
lean:
  - New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean
decls:
  - New.EdgeCoordinates
  - New.FrobeniusCycle.edgeHeckeOperator
  - New.FrobeniusCycle.edgeHeckeOperator_apply
  - New.regroup
  - New.regroup_surjective
  - New.edgewise
  - New.edgewise_mulVec
  - New.pairingMap
  - New.nearInverse
  - New.pairingMap_mul_nearInverse_apply
  - New.FrobeniusCycle.IsEdgePairing.transpose_mul_diagonal_mul
  - New.FrobeniusCycle.IsEdgePairing.edgeHeckeOperator_regroup
  - New.FrobeniusCycle.IsEdgePairing.pairingMap_mul_nearInverse_one
  - New.FrobeniusCycle.IsEdgeCondition.pow_dvd_mul_sub_smul_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The edge Hecke operator

This section defines the operator of the theorem in coordinates, and writes it as a product of two matrices: the restriction to edges, and a pairing map. Then it builds a near inverse of the pairing map from the averaging map of Section 6. Section 8 uses these two facts and nothing else about the operator.

Throughout, $\rho = \mathrm{letterRep}(n)$, $D = \mathrm{depthScaling}(k, n, r)$ is diagonal with entries $w^{\mathrm{depth}\,\beta}$, and $D^2 = \mathrm{depthPower}(k, n, r)$ has entries $p^{\mathrm{depth}\,\beta}$ (Sections 2 and 3). Write $\mathcal C$ for the set of cosets $\mathrm{ParahoricCosets}(W, k, r)$ of the parahoric subgroup $P_r$ with blocks $r$ and $k - r$.

### Edges in coordinates

The model is this. A group $\Gamma$ acts freely, with finitely many orbits, on pairs of a $W$-lattice of rank $k$ and a free $O$-module with basis indexed by $H$. The set $X$ is a set of orbit representatives, each with a basis of its lattice and of its module. The edges into $x$ are the sublattices of a fixed type, so they are indexed by $\mathcal C$. The origin of the edge $e = (x, b)$ is $\delta$ times a representative, for one $\delta \in \Gamma$. Only the coordinates of this picture enter the Lean statement.

**Definition (Edge coordinates).** Edge coordinates for $X$ and $H$ consist of maps

- $\mathrm{origin} : X \times \mathcal C \to X$;
- $\mathrm{originBasisChange} : X \times \mathcal C \to \mathrm{GL}_k(W)$;
- $\mathrm{terminusBasisChange} : \mathcal C \to \mathrm{GL}_k(W)$;
- $\mathrm{transition} : X \times \mathcal C \to \mathrm{GL}_H(O)$,

such that $(\mathrm{terminusBasisChange}\,b)^{-1}$ represents the coset $b$ for every $b$, and two edges $e, e'$ are equal if $\mathrm{origin}(e) = \mathrm{origin}(e')$ and $\mathrm{originBasisChange}(e)^{\mathsf T}\,(\mathrm{originBasisChange}(e')^{\mathsf T})^{-1} \in P_r$.

Lean: `New.EdgeCoordinates` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

In the model, $\delta^{-1} = \mathrm{originBasisChange}(e)\,\mathrm{diag}(p^{-1}, \dots, p^{-1}, 1, \dots, 1)\,\mathrm{terminusBasisChange}(b)$ with $r$ entries $p^{-1}$, and $\mathrm{transition}(e)$ is the matrix of $\delta$ on the modules. The last condition is where the action has to be free. The group $\Gamma$, the prime and $\delta$ are not part of the structure.

**Definition (Edge Hecke operator).** Let $J : I \simeq \mathrm{Exp} \times H$. The edge Hecke operator is the $O$-linear map on $X \to O^I$ with

$$(AF)(x) = \sum_{b \in \mathcal C} \Big(\big(\rho(\mathrm{originBasisChange}(x,b))\,D^2\,\rho(\mathrm{terminusBasisChange}(b))\big)^{\mathsf T} \otimes \mathrm{transition}(x,b)\Big)_{J,J}\, F(\mathrm{origin}(x,b)).$$

Lean: `New.FrobeniusCycle.edgeHeckeOperator` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

The subscript $J, J$ reindexes the Kronecker product by $I$. Entry by entry, $(AF)(x)_i = \sum_b\sum_j \mathrm{transition}(x,b)_{(Ji)_2,(Jj)_2}\,M_b{}_{(Jj)_1,(Ji)_1}\,F(\mathrm{origin}(x,b))_j$, where $M_b$ is the product of three matrices in the definition (`New.FrobeniusCycle.edgeHeckeOperator_apply`). The values of $F$ are coefficients in the basis $(n!^N/\beta!)z^\beta$. In this basis the substitution $h \mapsto h \circ g$ has matrix $\rho(g)^{\mathsf T}$. So, in terms of forms, $A$ is $p^{Nn/2}$ times the sum over the edges into $x$ of the values at the origins, each carried to $x$ by the $\delta$ of its edge.

### Regrouping and the pairing map

The map $\mathrm{regroup}(J)$ reads a vector indexed by $(H \times X) \times \mathrm{Exp}$ as a function $X \to O^I$: $\mathrm{regroup}(J)(F)(x)(i) = F(((Ji)_2, x), (Ji)_1)$. It is onto, with inverse $G \mapsto ((h, x), l) \mapsto G(x)(J^{-1}(l, h))$ (`New.regroup`, `New.regroup_surjective`).

For a set $E_d$ of edges, a vector indexed by $(H \times E_d) \times \mathrm{Exp}$ is a function on edges with values in $O^H \otimes O^{\mathrm{Exp}}$. For $u : E_d \to M_H(O)$ and a matrix $B$ on $O^{\mathrm{Exp}}$, $\mathrm{edgewise}(u, B) = \mathrm{blockDiagonal}(u) \otimes B$ acts at the edge $e$ by $u(e) \otimes B$ (`New.edgewise`). At $x = (h', e)$ the value of $\mathrm{edgewise}(u, B)\psi$ is $B\sum_h u(e)_{h'h}\,\psi((h, e), \cdot)$ (`New.edgewise_mulVec`).

**Definition (Pairing map and near inverse).** Let $u : E_d \to \mathrm{GL}_H(O)$ and $b, b' : \mathrm{Exp} \to O$. For a matrix $Q'$ with rows indexed by $(H \times E_d) \times \mathrm{Exp}$, and $R'$ of the transposed shape,

$$\mathrm{pairingMap}(u, b, Q') = Q'^{\mathsf T}\,\mathrm{edgewise}(u, \mathrm{diag}\,b), \qquad \mathrm{nearInverse}(u, \mathrm{Av}, b', R') = \mathrm{edgewise}(u^{-1}, \mathrm{Av}\,\mathrm{diag}\,b')\,R'^{\mathsf T}.$$

Lean: `New.pairingMap`, `New.nearInverse` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

So the pairing map sends a function on edges to its pairings with the columns of $Q'$: by $u(e)$ on $O^H$, and by $\langle h, h'\rangle_b = h' \cdot (b \ast h)$ on forms.

**Lemma.** For all $i, j$,

$$\big(\mathrm{pairingMap}(u, b, Q')\,\mathrm{nearInverse}(u, \mathrm{Av}, b', R')\big)_{ij} = \sum_{x \in H \times E_d} \mathrm{col}_i(x) \cdot \big(b \ast \mathrm{Av}(b' \ast \mathrm{row}_j(x))\big),$$

where $\mathrm{col}_i(x) = Q'((x, \cdot), i)$ and $\mathrm{row}_j(x) = R'(j, (x, \cdot))$.

Lean: `New.pairingMap_mul_nearInverse_apply` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Edgewise matrices multiply factor by factor. Since $u(e)u(e)^{-1} = 1$, the middle product is $1 \otimes B$ with $B = \mathrm{diag}(b)\,\mathrm{Av}\,\mathrm{diag}(b')$. This matrix is block diagonal over $H \times E_d$, and $Bv = b \ast \mathrm{Av}(b' \ast v)$. $\square$

### The factorization

**Lemma.** Let $(b, b')$ be an edge pairing and $g, \gamma \in \mathrm{GL}_k(W)$. Then

$$(D\rho(\gamma))^{\mathsf T}\,\mathrm{diag}(b)\,D\rho(g^{\mathsf T}) = \big(\rho(g)\,D^2\,\rho(\gamma)\big)^{\mathsf T}\,\mathrm{diag}(b).$$

Lean: `New.FrobeniusCycle.IsEdgePairing.transpose_mul_diagonal_mul` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* The adjoint property of the edge pairing (Section 3) reads $\mathrm{diag}(b)\,\rho(g^{\mathsf T}) = \rho(g)^{\mathsf T}\mathrm{diag}(b)$. Diagonal matrices commute, and $w^2 = p$, so $D\,\mathrm{diag}(b)\,D = D^2\,\mathrm{diag}(b)$. Then $\rho(\gamma)^{\mathsf T}(D\,\mathrm{diag}(b)\,D)\rho(g^{\mathsf T}) = \rho(\gamma)^{\mathsf T}D^2\rho(g)^{\mathsf T}\mathrm{diag}(b)$, which is the right side. $\square$

The edge set for the factorization is $E_d = X \times \mathcal C$, and a pair $(h, (x, b)) \in H \times E_d$ has two origins. For the restriction it has origin $(h, \mathrm{origin}(x,b))$ with basis change $\mathrm{originBasisChange}(x,b)^{\mathsf T}$. For the dual edge it has origin $(h, x)$ with basis change $\mathrm{terminusBasisChange}(b)$. Write $\mathcal R$ and $\mathcal R'$ for the two matrices $\mathrm{edgeRestriction}$ of Section 3 with these data.

**Theorem (Factorization).** Let $(b, b')$ be an edge pairing, $J : I \simeq \mathrm{Exp} \times H$ and $\mathcal E$ edge coordinates. For every $F$ on $(H \times X) \times \mathrm{Exp}$,

$$A\big(\mathrm{regroup}(J)(b \ast F)\big) = \mathrm{regroup}(J)\big(\mathrm{pairingMap}(\mathrm{transition}, b, \mathcal R')\,\mathcal R\,F\big),$$

where $(b \ast F)(y) = b_{y_2}F(y)$.

Lean: `New.FrobeniusCycle.IsEdgePairing.edgeHeckeOperator_regroup` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Fix $x$ and $i$. Let $\psi = \mathcal R F$ and $\varphi = \mathrm{edgewise}(\mathrm{transition}, \mathrm{diag}\,b)\psi$. Write $M_q = \rho(\mathrm{originBasisChange}(x,q))D^2\rho(\mathrm{terminusBasisChange}(q))$.

Step 1. By the definition of $\mathrm{edgeRestriction}$, $\psi((h, x, q), \cdot) = D\rho(\mathrm{originBasisChange}(x,q)^{\mathsf T})\,F((h, \mathrm{origin}(x,q)), \cdot)$.

Step 2. By the lemma on $\mathrm{edgewise}$ and the previous lemma, with $\gamma = \mathrm{terminusBasisChange}(q)$ and $g = \mathrm{originBasisChange}(x,q)$:

$$(D\rho(\gamma))^{\mathsf T}\varphi((h, x, q), \cdot) = \sum_{h'} \mathrm{transition}(x,q)_{hh'}\,M_q^{\mathsf T}\,\mathrm{diag}(b)\,F((h', \mathrm{origin}(x,q)), \cdot).$$

Step 3. Expand the left side of the theorem with the entry formula for $A$. Reindex the sum over $j \in I$ by $J$ as a sum over $(\alpha, h') \in \mathrm{Exp} \times H$. The term for $q$ is $\sum_{h'}\sum_\alpha \mathrm{transition}(x,q)_{(Ji)_2 h'}\,(M_q)_{\alpha (Ji)_1}\,b_\alpha F((h', \mathrm{origin}(x,q)), \alpha)$. This is the $(Ji)_1$ entry of the right side of Step 2 for $h = (Ji)_2$.

Step 4. The pairs $e$ whose dual origin is $(h, x)$ are exactly the $(h, x, q)$ for $q \in \mathcal C$. So $\sum_q (D\rho(\mathrm{terminusBasisChange}(q)))^{\mathsf T}\varphi((h, x, q), \cdot)$ is the value of $\mathcal R'^{\mathsf T}\varphi$ at $((h, x), \cdot)$. By definition $\mathcal R'^{\mathsf T}\varphi = \mathrm{pairingMap}(\mathrm{transition}, b, \mathcal R')\,\mathcal R F$. Read this at $(((Ji)_2, x), (Ji)_1)$; that is $\mathrm{regroup}(J)$ at $(x, i)$. $\square$

Section 8 uses one consequence: the image of $A$ contains $\mathrm{regroup}(J)$ of the image of the matrix $\mathrm{pairingMap}(\mathrm{transition}, b, \mathcal R')\,\mathcal R$. The weights $b$ need not be inverted for this.

### The near inverse

**Lemma.** Let $(b, b')$ be an edge pairing, $u : E_d \to \mathrm{GL}_H(O)$ and $R'Q' = 1$. Then

$$\mathrm{pairingMap}(u, b, Q')\,\mathrm{nearInverse}(u, 1, b', R') = p^{Nc_0}\cdot 1.$$

Lean: `New.FrobeniusCycle.IsEdgePairing.pairingMap_mul_nearInverse_one` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* By the entry formula with $\mathrm{Av} = 1$, the $(i, j)$ entry is $\sum_x \mathrm{col}_i(x)\cdot(b \ast b' \ast \mathrm{row}_j(x))$. As $b_\beta b'_\beta = p^{Nc_0}$, this is $p^{Nc_0}\sum_x\sum_\beta R'(j, (x,\beta))\,Q'((x,\beta), i) = p^{Nc_0}(R'Q')_{ji}$. $\square$

**Theorem (Near inverse).** Let $(C, S, \mathrm{Av})$ be an edge condition for $(r, c, \theta, b)$ (Section 6), $(b, b')$ an edge pairing, $u : E_d \to \mathrm{GL}_H(O)$, $R'Q' = 1$, and let every column of $Q'$ have all its values in $\mathrm{allEdgesForms}(k, n, r)$. Then for all $i, j$,

$$w^c \;\Big|\; \big(\mathrm{pairingMap}(u, b, Q')\,\mathrm{nearInverse}(u, \mathrm{Av}, b', R') - p^{2Nc_0}\cdot 1\big)_{ij}.$$

Lean: `New.FrobeniusCycle.IsEdgeCondition.pow_dvd_mul_sub_smul_one` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Let $a = p^{Nc_0}$. By the lemma, $p^{2Nc_0}\cdot 1 = a\cdot\mathrm{pairingMap}(u, b, Q')\,\mathrm{nearInverse}(u, 1, b', R')$. By the entry formula, applied twice, the $(i,j)$ entry of the difference is

$$\sum_x \Big(\mathrm{col}_i(x)\cdot\big(b \ast \mathrm{Av}\,v_x\big) - a\,\mathrm{col}_i(x)\cdot(b \ast v_x)\Big), \qquad v_x = b' \ast \mathrm{row}_j(x).$$

Each $\mathrm{col}_i(x)$ lies in $\mathrm{allEdgesForms}$. So the edge condition makes each term divisible by $w^c$. $\square$

Only one property of the edge condition enters here. It involves neither $C$, $S$ nor $\theta$. The other properties enter in Section 8, where the values of $\mathrm{nearInverse}$ must lie in $C$; they do, since $\mathrm{Av}$ maps into $C$.
