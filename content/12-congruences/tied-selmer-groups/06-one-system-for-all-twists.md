---
title: One system for all twists
lean:
  - New/Congruences/Selmer/OneSystem.lean
decls:
  - New.Selmer.map_mk_smul
  - New.Selmer.universalChar
  - New.Selmer.aeval_universalChar
  - New.Selmer.eval_universalChar
  - New.Selmer.aeval_sub_one_universalChar
  - New.Selmer.IsTiedPrimes.universalChar_eq_one_add_X
  - New.Selmer.IsTiedPrimes.universalChar_frob
  - New.Selmer.IsTiedPrimes.universalChar_tame_gen
  - New.Selmer.finite_selmerModule
  - New.Selmer.mapRel_single
  - New.Selmer.mapRel_mapRel
  - New.Selmer.mapRel_image_cocycleRelations
  - New.Selmer.relationMatrix
  - New.Selmer.relationMatrix_apply
  - New.Selmer.sum_mapDomain_smul_eq_relEval
  - New.Selmer.mem_matrixKernel_relationMatrix
  - New.Selmer.eq_zero_of_forall_hom_zmod_eq_zero
  - New.Selmer.exists_openNormalSubgroup_forall_apply_eq_apply_one
  - New.Selmer.exists_openNormalSubgroup_forall_eq_zero
  - New.Selmer.exists_matrix_selmerModule_equiv
  - New.Selmer.pointTwist
  - New.Selmer.pointTwist_smul_eq_self
  - New.Selmer.selmerAtPoint
  - New.Selmer.exists_matrix_selmerAtPoint_equiv
  - New.Selmer.exists_isLeast_length_selmerAtPoint
  - New.Selmer.exists_sharp_polynomial
status: drafted
drafted_by: writer@claude-opus-5-5
---
## One system for all twists

The [twisting theorem](/chapter/twisting-theorem/) needs the lengths of the Selmer groups of all twists by characters $\prod_j \zeta_j^{h_j}$ at once. One matrix over a polynomial ring computes them all, so each length is a least valuation of values of fixed polynomials. All results are in [OneSystem.lean](lean:New/Congruences/Selmer/OneSystem.lean#L1).

Background used:

- Relations $f : G \to_0 M_n(O)$, the module $\mathrm{Obey}(L, B)$ of functions $c$ with $\sum_g f(g) c(g) = 0$ for $f \in L$, the cocycle relations, and $\mathrm{mapRel}$, which applies a ring map to the entries (`New.obeying`, `New.cocycleRelations`, `New.mapRel`, [relations and cocycles](/chapter/fitting-ideals/#relations-and-cocycles)).
- The kernel of a matrix $\bar A$ over a discrete valuation ring on $(O/\mathrm{ev}(a))^k$ has as length the least valuation of an image of a maximal minor of $(A, a)$ (`New.Selmer.isLeast_length_matrixKernel`, [lengths and determinants](/chapter/fitting-ideals/#lengths-and-determinants)).
- Over a number field, the continuous cocycles with values in a finite discrete module that are unramified outside a finite set form a finite set (`New.finite_cocycles_unramified_outside`, [Selmer groups and the Greenberg-Wiles formula](/chapter/local-duality/#selmer-groups-and-the-greenberg-wiles-formula)).

### The textbook form

In the textbook, $H^1$ of a finite quotient is computed by a finite complex of free modules, and the cohomology at a point $x : \Lambda \to O'$ is that of the specialised complex. The source does not use complexes. It writes the cocycle rule, the unramified conditions and the local relations as one linear system on a finite quotient of $G$, and reads the length from its maximal minors.

### The universal twist

**Definition (Universal twist).** For homomorphisms $h_j : G \to \mathbb{Z}/q$, $j \in \sigma$, put
$$\psi_X(g) = \prod_{j \in \sigma} (1 + X_j)^{h_j(g)} \in R[X_j : j \in \sigma],$$
with the exponent $h_j(g)$ taken in $[0, q)$.

Lean: `New.Selmer.universalChar` (New/Congruences/Selmer/OneSystem.lean).

**Lemma.** The value of $\psi_X(g)$ at a point $x$ is $\prod_j (1 + x_j)^{h_j(g)}$. If $\zeta_j^q = 1$ for all $j$, the value at $x_j = \zeta_j - 1$ is the character $\prod_j \zeta_j^{h_j(g)}$.

Lean: `New.Selmer.aeval_universalChar`, `New.Selmer.eval_universalChar`, `New.Selmer.aeval_sub_one_universalChar` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Evaluation is a ring map. The power $\zeta^k$ depends only on $k$ modulo $q$, so the character $\prod_j \zeta_j^{h_j}$ is well defined and equals the value. $\square$

**Remark (Formalization).** For $q = 0$ the ring $\mathbb{Z}/0$ is $\mathbb{Z}$ and the exponent is $|h_j(g)|$. The chapter uses only $q = \ell^N$. At a point $x$ with $(1 + x_j)^q \neq 1$ the function $g \mapsto \psi_x(g)$ is not a homomorphism. The statements below hold at every point, as statements about a module of functions.

**Lemma.** Let $(J, d)$ be tied primes with $N \neq 0$, and take $\sigma = J$ and $h_w = \chi_w$, the characters of the data. If $\chi_v(g) = 1$ and $\chi_w(g) = 0$ for $w \neq v$, then $\psi_X(\iota_b(g)) = 1 + X_v$ for both $b$. So $\psi_X(\iota_b(\gamma_v)) = 1 + X_v$ for $v \in J$, and $\psi_X(\iota_b(\varphi_v)) = 1 + X_{P_0}$ for $v \in J \setminus \{P_0\}$.

Lean: `New.Selmer.IsTiedPrimes.universalChar_eq_one_add_X`, `New.Selmer.IsTiedPrimes.universalChar_frob`, `New.Selmer.IsTiedPrimes.universalChar_tame_gen` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* The characters are anticyclotomic, so $\chi_w(\iota_b(g)) = \chi_w(g)$. In the product only the factor at $v$ survives, with exponent $1$, since $\ell^N > 1$. The values at $\gamma_v$ and at $\varphi_v$ are conditions of tied primes, from [Selmer data, tied Selmer groups and Sah's lemma](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma). $\square$

### Finiteness

**Theorem.** Let $\rho$ be locally constant modulo $\ell^M$, $S$ finite, $a \mid \ell^M$ with $O/a$ finite, and $L$ any set of relations. Then $\mathrm{Sel}(\rho, S, L, O/a)$ is finite.

Lean: `New.Selmer.finite_selmerModule` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* The ring $O/\ell^M$ acts on $O/a$, so $\rho$ acts on $(O/a)^n$ through its reduction, which is locally constant. So $(O/a)^n$ is a finite discrete module. The Selmer module lies in the set of continuous cocycles unramified outside $S$, which is finite by the background result. $\square$

**Lemma.** A matrix over $O$ acts on $(O/a)^n$ as its reduction modulo $a$ does.

Lean: `New.Selmer.map_mk_smul` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Compare coordinates. $\square$

### Relations as a matrix

**Lemma.** $\mathrm{mapRel}$ sends a single relation $g \mapsto m$ to $g \mapsto \mathrm{ev}(m)$, satisfies $\mathrm{mapRel}_{\mathrm{ev}} \circ \mathrm{mapRel}_e = \mathrm{mapRel}_{\mathrm{ev} \circ e}$, and carries the cocycle relations of $\rho$ onto those of $g \mapsto \mathrm{ev}(\rho(g))$.

Lean: `New.Selmer.mapRel_single`, `New.Selmer.mapRel_mapRel`, `New.Selmer.mapRel_image_cocycleRelations` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* The cocycle relation for $(g, h)$ has coefficient $1$ at $gh$, $-1$ at $g$ and $-\rho(g)$ at $h$. Applying $\mathrm{ev}$ gives the relation for $\mathrm{ev} \circ \rho$. The other claims are entrywise. $\square$

**Definition (Relation matrix).** For a map $\pi : \Gamma \to \mathcal{G}$ to a finite set and a set $R$ of relations, the relation matrix has rows $R \times n$, columns $\mathcal{G} \times n$, and entry $(\pi_* f)(c)_{i j}$ at $((f, i), (c, j))$. Here $\pi_* f$ adds the matrices $f(g)$ over each fibre of $\pi$.

Lean: `New.Selmer.relationMatrix`, `New.Selmer.relationMatrix_apply` (New/Congruences/Selmer/OneSystem.lean).

**Lemma.** For $w : \mathcal{G} \times n \to B$, $\bar A w = 0$ for the relation matrix with $\mathrm{ev}$ applied if and only if $g \mapsto w(\pi(g), \cdot)$ obeys the relations $\mathrm{mapRel}_{\mathrm{ev}}(R)$.

Lean: `New.Selmer.sum_mapDomain_smul_eq_relEval`, `New.Selmer.mem_matrixKernel_relationMatrix` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Row $(f, i)$ of $\bar A w$ is $\sum_c \mathrm{ev}((\pi_* f)(c))_{i \cdot} w(c, \cdot) = \sum_g \mathrm{ev}(f(g))_{i \cdot} w(\pi(g), \cdot)$, which is coordinate $i$ of the relation $f$ applied to the pulled back function. Check this for single relations and extend by additivity. $\square$

### One finite quotient

**Lemma.** In an abelian group $B$ killed by $m \neq 0$, an element killed by every homomorphism $B \to \mathbb{Z}/m$ is $0$.

Lean: `New.Selmer.eq_zero_of_forall_hom_zmod_eq_zero` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Homomorphisms to $\mathbb{Q}/\mathbb{Z}$ separate points, and on $B$ they all factor through $\frac{1}{m}\mathbb{Z}/\mathbb{Z} \cong \mathbb{Z}/m$. $\square$

**Lemma.** Finitely many locally constant functions on an open subgroup $G'$ are constant on an open normal subgroup $G'' \subseteq G'$ of $G$.

Lean: `New.Selmer.exists_openNormalSubgroup_forall_apply_eq_apply_one` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* The set where all of them equal their value at $1$ is a neighbourhood of $1$. A profinite group has a basis of open normal subgroups at $1$. $\square$

**Lemma (One quotient for all coefficients).** Let $G'$ be open, $m \neq 0$ and $S$ finite. There is an open normal subgroup $G''$ such that for every abelian group $B$ killed by $m$, each locally constant $z : G \to B$ that is additive on $G'$ and vanishes on inertia above the primes outside $S$ vanishes on $G''$.

Lean: `New.Selmer.exists_openNormalSubgroup_forall_eq_zero` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Let $F$ be the fixed field of $G'$ and $Y$ the set of continuous homomorphisms $G' \to \mathbb{Z}/m$ unramified outside the places of $F$ over $S$. These places are finite in number, so $Y$ is finite, and by the last lemma all $y \in Y$ are constant on some $G''$. Given $B$ and $z$, for each $\chi : B \to \mathbb{Z}/m$ the function $\chi \circ z$ restricted to $G'$ lies in $Y$. So $\chi(z(g)) = \chi(z(1)) = 0$ for $g \in G''$. By the first lemma, $z(g) = 0$. $\square$

The point of the lemma is that $G''$ does not depend on $B$. This is what makes one matrix work for all twists and all rings $O'$.

**Theorem (One matrix).** Let $\rho : G \to M_n(\Lambda)$, $L$ relations over $\Lambda$, $G'$ open, $m \neq 0$ and $S$ finite. There is a matrix $A$ over $\Lambda$ with finitely many columns $k$ such that for every ring map $\mathrm{ev} : \Lambda \to O'$ and every $O'$-module $B$ killed by $m$ on which $G'$ acts trivially through $\mathrm{ev} \circ \rho$,
$$\mathrm{Sel}(\mathrm{ev} \circ \rho, S, \mathrm{mapRel}_{\mathrm{ev}}(L), B) \cong \ker(\bar A \text{ on } B^k).$$

Lean: `New.Selmer.exists_matrix_selmerModule_equiv` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Take $G''$ from the last lemma, $\mathcal{G} = G/G''$ and $\pi$ the quotient map. Let $R$ be the union of the cocycle relations of $\rho$, the relations $[g]$ for $g$ in inertia above primes outside $S$, and $L$. Let $A$ be the relation matrix of $\pi$ and $R$, with $k = \mathcal{G} \times n$. A member $z$ of the Selmer module is additive on $G'$, since $G'$ acts trivially, so it vanishes on $G''$, and the cocycle rule gives $z(g g'') = z(g)$. So $z$ factors through $\mathcal{G}$. Conversely a function that factors through $\mathcal{G}$ is locally constant. By the last lemma of the previous part and the lemma on $\mathrm{mapRel}$, pulling back along $\pi$ is an injective map from $\ker \bar A$ onto the Selmer module. $\square$

**Remark (Formalization).** The rows of $A$ are indexed by $R \times n$, and $R$ is infinite, since it contains a relation for every element of inertia outside $S$. Only the columns must be finite for the result on maximal minors.

### The twists

**Definition.** For a point $x$ over $O'$ and $e : O \to O'$, the twisted matrices are $\psi_x(g)\, e(\rho(g))$, and $\mathrm{Sel}(x) = \mathrm{Sel}(\psi_x\, e(\rho), S, \mathrm{mapRel}_e(L), O'/\ell^M)$.

Lean: `New.Selmer.pointTwist`, `New.Selmer.selmerAtPoint` (New/Congruences/Selmer/OneSystem.lean).

**Lemma.** If all $h_j(g) = 0$ and $\rho(g) \equiv 1 \bmod \ell^M$, the twisted matrix at $g$ acts trivially on $(O'/\ell^M)^n$.

Lean: `New.Selmer.pointTwist_smul_eq_self` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Then $\psi_x(g) = 1$, and the reduction of $e(\rho(g))$ modulo $\ell^M$ is the image of the reduction of $\rho(g)$, which is $1$. $\square$

**Theorem.** Let the $h_j$ be locally constant, $\rho$ locally constant modulo $\ell^M$, and $S$ finite. There is a matrix $A$ over $O[X_j]$ with finitely many columns $k$ such that for every $e : O \to O'$ and every point $x$, $\mathrm{Sel}(x) \cong \ker(A(x) \text{ on } (O'/\ell^M)^k)$.

Lean: `New.Selmer.exists_matrix_selmerAtPoint_equiv` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Let $G'$ be the intersection of the kernels of the $h_j$ and of $\rho \bmod \ell^M$. It is open. Apply the theorem on one matrix with $\Lambda = O[X_j]$, $\rho_X(g) = \psi_X(g) \rho(g)$, the relations $\mathrm{mapRel}_C(L)$ and $m = \ell^M$. Evaluation at $x$ over $e$ sends $\rho_X$ to the twisted matrices, and the last lemma says $G'$ acts trivially. $\square$

**Theorem (Lengths of all twists).** Under the same hypotheses there is a set $\mathcal{M}$ of polynomials over $O$ such that for every discrete valuation ring $O'$ of characteristic $0$, every $e$ and every $x$,
$$\mathrm{len}\, \mathrm{Sel}(x) = \min_{P \in \mathcal{M}} v(P(x)).$$

Lean: `New.Selmer.exists_isLeast_length_selmerAtPoint` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Take the matrix $A$ of the last theorem and let $\mathcal{M}$ be the maximal minors of $(A, \ell^M)$. Lengths are invariant under isomorphism, and $\ell^M \neq 0$ in $O'$ since $O'$ has characteristic $0$. The background theorem on maximal minors gives the claim. $\square$

**Theorem (A sharp polynomial).** For each point $x_0$ over such a ring $O_0$ there is one polynomial $P$ with $v(P(x_0)) = \mathrm{len}\, \mathrm{Sel}(x_0)$ and $v(P(x)) \geq \mathrm{len}\, \mathrm{Sel}(x)$ at every point $x$ over every such ring.

Lean: `New.Selmer.exists_sharp_polynomial` (New/Congruences/Selmer/OneSystem.lean).

*Proof.* Take $P \in \mathcal{M}$ where the minimum at $x_0$ is attained. At other points $v(P(x))$ is in the set whose least element is the length. $\square$

**Remark (Formalization).** The valuations take values in $\mathbb{N}^\infty$, and $v(0) = \infty$. If every minor vanishes at $x$, the length is $\infty$. This cannot happen here, since $\mathrm{Sel}(x)$ is a submodule of functions on the finite set $\mathcal{G} \times n$ with values in $O'/\ell^M$, but the theorem does not need this.
