---
title: The proof of the theorem
lean:
  - New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean
  - New/Reduction/Lattices/Colength.lean
decls:
  - New.exists_elementary_divisors_mod_summand
  - New.valuedIn
  - New.card_add_card_le_mul_finrank
  - New.smul_top_le_of_le_sup_smul_top
  - New.exists_finset_card_le_smul_top_le_sup_span
  - New.colengthDvd_mul_mul_of_smul_top_le
  - New.FrobeniusCycle.IsEdgeCondition.exists_finset_smul_top_le_range_sup_span
  - New.FrobeniusCycle.exists_colengthDvd_range_pairingMap_mul_edgeRestriction
  - New.EdgeCoordinates.surjective_origin_originBasisChange
  - New.FrobeniusCycle.elementary_divisors
  - New.FrobeniusCycle.elementary_divisors_length
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The proof of the theorem

The proof has three steps. First, a near inverse whose values satisfy the edge conditions shows that the image of the pairing map, plus few further vectors, contains $p^{2Nc_0}$ times everything (Nakayama's lemma). Second, both ends of the factorization of Section 7 have small colength (Section 4). Third, colengths multiply along the chain. Throughout, $O$ is a valuation domain, and all matrices have finite index sets.

### Linear algebra of a near inverse

**Lemma.** Let $RQ = 1$, with $Q$ of shape $K \times E$, and let $A$ have the shape of $Q$. There are $U \in \mathrm{GL}_K(O)$ and $t : K \to O$ such that $R\,U_{\cdot j} = 0$ whenever $t_j \ne 0$, and

$$\mathrm{im}\,Q + \mathrm{im}\,A = \mathrm{im}\,Q + \mathrm{span}\{t_j U_{\cdot j}\}.$$

Lean: `New.exists_elementary_divisors_mod_summand` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Take a Smith form $(A - QRA)R = U\,\mathrm{diag}(t)\,P$ with $U, P$ invertible ([Fitting ideals](/chapter/fitting-ideals/#lengths-and-determinants)). Since $RQ = 1$, $R(A - QRA) = 0$, so $R\,U\mathrm{diag}(t) = 0$; this gives $t_j R U_{\cdot j} = 0$. Next $A = Q(RA) + U\mathrm{diag}(t)(PQ)$, so $\mathrm{im}\,A \subseteq \mathrm{im}\,Q + \mathrm{span}\{t_jU_{\cdot j}\}$. Conversely $t_jU_{\cdot j} = A\eta - Q(RA\eta)$ for $\eta = RP^{-1}e_j$. $\square$

**Remark (Formalization).** Over a valuation domain every matrix has a Smith form (`New.IsValuationPair.smith_normal_form`, Lib/General/LinearAlgebra/IntegralLattices.lean). The ring need not be noetherian. This is why the chapter works with valuation domains.

For $C \subseteq O^I$, $\mathrm{valuedIn}(X, C)$ is the module of $\varphi$ on $X \times I$ with $\varphi(x, \cdot) \in C$ for all $x$ (`New.valuedIn`).

**Lemma (Count).** Let $RQ = 1$, $U$ invertible and $R U_{\cdot j} = 0$ for $j \in J$. If the columns of $Q$ and the columns $U_{\cdot j}$, $j \in J$, have all their values in $S$ modulo the maximal ideal, then $|E| + |J| \le |X|\dim S$.

Lean: `New.card_add_card_le_mul_finrank` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* The rows of $R$ and of $U^{-1} - U^{-1}QR$ times the columns of $Q$ and $U_{\cdot J}$ give a block matrix $\begin{pmatrix}1 & 0\\ 0 & 1\end{pmatrix}$ on $E \sqcup J$, because $RU_{\cdot j} = 0$. So the $|E| + |J|$ columns are independent modulo the maximal ideal, and the lemma on dual rows of Section 3 applies. $\square$

**Lemma (Nakayama).** Let $w$ lie in the maximal ideal, $aw \mid u$ and $a\,O^E \subseteq G + u\,O^E$. Then $a\,O^E \subseteq G$.

Lean: `New.smul_top_le_of_le_sup_smul_top` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* $u\,O^E \subseteq \mathfrak m\,(a\,O^E)$, and $a\,O^E$ is finitely generated. Apply Nakayama's lemma. $\square$

**Theorem (Few generators).** Let $RQ = 1$, $w \in \mathfrak m$, $aw \mid u$, and $u \mid (AB - a\cdot 1)_{ij}$ for all $i, j$. Let the images of $Q$ and $B$ lie in $\mathrm{valuedIn}(X, C)$, and let $u h \in C$ imply that the reduction of $h$ lies in $S$. Then there is a finite set $s$ with $|E| + |s| \le |X|\dim S$ and $a\,O^E \subseteq \mathrm{im}(AQ) + \mathrm{span}\,s$.

Lean: `New.exists_finset_card_le_smul_top_le_sup_span` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Apply the first lemma to $Q$ and $B$. Let $J = \{j : t_j \ne 0,\ t_j \mid u\}$ and $s = \{AU_{\cdot j} : j \in J\}$. In a valuation ring $u \mid t_j$ for $j \notin J$.

Count. $u\,Q_{\cdot j}$ and, for $j \in J$, $u\,U_{\cdot j} = (u/t_j)\,t_jU_{\cdot j}$ lie in $\mathrm{valuedIn}(X, C)$, because $t_jU_{\cdot j} \in \mathrm{im}\,Q + \mathrm{im}\,B$. So their values reduce into $S$, and the count lemma gives $|E| + |J| \le |X|\dim S$.

Span. Let $G = \mathrm{im}(AQ) + \mathrm{span}\,s$. By the first lemma, $A(\mathrm{im}\,Q + \mathrm{im}\,B) \subseteq G + u\,O^E$: $A t_jU_{\cdot j}$ is in $G$ for $j \in J$ and in $u\,O^E$ otherwise. For $\eta \in O^E$, $a\eta = AB\eta - uY\eta$ for a matrix $Y$. So $a\,O^E \subseteq G + u\,O^E$, and Nakayama ends the proof. $\square$

**Lemma (Chain).** If $a\,O^E \subseteq \mathrm{im}\,A + \mathrm{span}\,s$, then for every $z$ the colength of $\mathrm{im}(d'Ad) + z\,O^E$ in $O^E$ divides $\det d' \cdot a^{|E|}\cdot\det d\cdot z^{|s|}$.

Lean: `New.colengthDvd_mul_mul_of_smul_top_le` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* The colength of $\mathrm{im}\,B$ divides $\det B$. The chain is $O^E \supseteq \mathrm{im}\,A + \mathrm{span}\,s \supseteq \mathrm{im}(Ad) + \mathrm{span}\,s \supseteq \mathrm{im}(Ad) + zO^E$, with factors $a^{|E|}$, $\det d$ (push $\det d$ forward by $A$) and $z^{|s|}$. Push the result forward by $d'$ and multiply by $\det d'$. The colengths multiply (`New.ColengthDvd.trans`, `New.ColengthDvd.map`). $\square$

### The middle of the chain

**Theorem.** Let $p$ not be a unit of $O$, $k \ge 2$, $(C, S, \mathrm{Av})$ an edge condition for $(r, c, \theta, b)$ with $c = 5Nc_0$, and $(b, b')$ an edge pairing. Let $Q, Q'$ have rows indexed by $(H \times E_d) \times \mathrm{Exp}$ and columns by $V \times \mathrm{Exp}$, with left inverses $R, R'$ and images in $\mathrm{valuedIn}(H \times E_d, \mathrm{allEdgesForms})$. Let $|H \times E_d| = |V|\,[\mathrm{GL}_k(W) : P_r]$. Then there is $s$ with $|s| \le \theta|V||\mathrm{Exp}|$ and

$$p^{2Nc_0}\,O^{V \times \mathrm{Exp}} \subseteq \mathrm{im}\big(\mathrm{pairingMap}(u, b, Q')\,Q\big) + \mathrm{span}\,s.$$

Lean: `New.FrobeniusCycle.IsEdgeCondition.exists_finset_smul_top_le_range_sup_span` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Let $c_2 = 2Nc_0$. As $Nc_0 \ge 2$, $2c_2 + 1 \le c - 1$, so $p^{c_2}w \mid w^{c-1}$. Apply the theorem on few generators with $A = \mathrm{pairingMap}(u, b, Q')$, $B = \mathrm{nearInverse}(u, \mathrm{Av}, b', R')$, $a = p^{c_2}$, $u = w^{c-1}$. The near inverse theorem of Section 7 gives $w^{c-1} \mid (AB - a)_{ij}$. The image of $Q$ is valued in $\mathrm{allEdgesForms} \subseteq C$. The values of $B$ are $\mathrm{Av}$ of something, so they lie in $C$. The space $S$ has the needed property. Then $|V||\mathrm{Exp}| + |s| \le |V|\,[\mathrm{GL}_k(W) : P_r]\dim S \le |V|(1 + \theta)|\mathrm{Exp}|$. $\square$

**Remark (Formalization).** $O$ need not be discrete, so $u$ cannot be "$w^c$ divided by a uniformizer". The proof uses $u = w^{c-1}$ and needs $p^{c_2}w \mid u$. As $p^{c_2}w = w^{2c_2+1}$, this needs $4Nc_0 + 2 \le c$, which holds for $c = 5Nc_0$ because $Nc_0 \ge 2$.

### The colength of the factored operator

**Theorem.** Let $p$ not be a unit, let the size conditions hold for $(k, n, r, \theta)$ and let $(b, b')$ be an edge pairing. Let $\mathrm{src}, \mathrm{src}' : H \times E_d \to V$ and $g, g'$ be such that both $e \mapsto (\mathrm{src}\,e, g(e)^{-1}P_r)$ and $e \mapsto (\mathrm{src}'\,e, g'(e)^{-1}P_r)$ are onto $V \times \mathcal C$, and $|H \times E_d| = |V|[\mathrm{GL}_k(W) : P_r]$. For every $m$ there is $l \le (3c_{\mathrm{div}} + \theta m)|V||\mathrm{Exp}|$ such that the colength of

$$\mathrm{im}\big(\mathrm{pairingMap}(u, b, \mathrm{edgeRestriction}(\mathrm{src}', g'))\,\mathrm{edgeRestriction}(\mathrm{src}, g)\big) + p^m O^{V\times\mathrm{Exp}}$$

divides $p^l$.

Lean: `New.FrobeniusCycle.exists_colengthDvd_range_pairingMap_mul_edgeRestriction` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* Let $\Delta = \lfloor c_{\mathrm{div}}|\mathrm{Exp}|\rfloor$. Section 4 gives $Q, R, d$ for $(\mathrm{src}, g)$ and $Q', R', d'$ for $(\mathrm{src}', g')$, with $Qd = \mathrm{edgeRestriction}(\mathrm{src}, g)$ and $\det d \mid w^{|V|\Delta}$, and the same for $d'$. So $\det d'^{\mathsf T}\det d \mid p^{|V|\Delta}$. The images of $Q$, $Q'$ are origin functions, so their values lie in $\mathrm{allEdgesForms}$ (Section 3). Section 6 gives an edge condition, and the previous theorem gives $s$. Since $\mathrm{pairingMap}(u, b, Q'd') = d'^{\mathsf T}\mathrm{pairingMap}(u, b, Q')$, the matrix is $d'^{\mathsf T}\,(\mathrm{pairingMap}(u, b, Q')Q)\,d$. The chain lemma with $z = p^m$ gives the divisor $p^l$ with $l = |V|\Delta + c_2|V||\mathrm{Exp}| + m|s|$. Finally $\Delta \le c_{\mathrm{div}}|\mathrm{Exp}|$, $c_2 \le 2c_{\mathrm{div}}$ (Section 2) and $|s| \le \theta|V||\mathrm{Exp}|$. $\square$

### Assembly of the proof

**Lemma.** For edge coordinates on finite sets, $e \mapsto (\mathrm{origin}\,e, (\mathrm{originBasisChange}(e)^{\mathsf T})^{-1}P_r)$ is onto $X \times \mathcal C$.

Lean: `New.EdgeCoordinates.surjective_origin_originBasisChange` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* The map is injective by the last axiom of edge coordinates, and $X \times \mathcal C$ is finite. $\square$

Now the theorem of Section 1: $Y \circ f = f \circ A$ implies $\mathrm{IsOntoUpToColength}(p, \mathrm{im} f, m, Y, (3c_{\mathrm{div}} + \theta m)|X||I|)$.

*Proof of the theorem.* Section 3 gives an edge pairing $(b, b')$, since $n < q$. Take $V = H \times X$ and $E_d = X \times \mathcal C$. For the restriction, $\mathrm{src}(h, e) = (h, \mathrm{origin}\,e)$ and $g(h, e) = \mathrm{originBasisChange}(e)^{\mathsf T}$; this is onto by the lemma. For the dual edges, $\mathrm{src}'(h, x, q) = (h, x)$ and $g' = \mathrm{terminusBasisChange}(q)$; this is onto as $\mathrm{terminusBasisChange}(q)^{-1}$ represents $q$. The count is $|H||X||\mathcal C|$. The previous theorem, with $u = \mathrm{transition}$, gives $l$ and the colength bound for the matrix $\mathcal A$ of Section 7.

Let $\pi = f \circ \mathrm{regroup}(J)$. As $\mathrm{regroup}(J)$ is onto, $\pi(O^{V\times\mathrm{Exp}}) = L = \mathrm{im} f$. $Y$ keeps $L$, since $Y(fF) = f(AF)$. By the factorization theorem, $\pi(\mathcal AF) = f(A(\mathrm{regroup}(J)(b \ast F))) = Y(\pi(b \ast F))$, so $\pi(\mathrm{im}\,\mathcal A) \subseteq Y(L)$. Also $\pi(p^m O^{V\times\mathrm{Exp}}) = p^mL$. So $\pi$ pushes the colength bound forward to $L$ and $Y(L) + p^mL$ (`New.ColengthDvd.map`). Finally $|V||\mathrm{Exp}| = |X||I|$ through $J$. $\square$

**Corollary (Lengths).** Let $O$ be a discrete valuation ring of characteristic zero, with the other hypotheses of the theorem. Then $Y(L) \subseteq L$, and there is $l \le (3c_{\mathrm{div}} + \theta m)|X||I|$ with $\mathrm{length}\,L/(Y(L) + p^mL) \le l \cdot \mathrm{length}(O/p)$.

Lean: `New.FrobeniusCycle.elementary_divisors_length` (New/UpperBound/ElementaryDivisors/ElementaryDivisorTheorem.lean).

*Proof.* $L$ is finitely generated. Over a discrete valuation ring a colength dividing $p^l$ gives this length bound (`New.IsOntoUpToColength.exists_relLength_le`). $\square$
