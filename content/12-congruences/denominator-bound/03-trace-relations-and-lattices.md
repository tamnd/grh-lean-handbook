---
title: Trace relations and lattices
lean:
  - New/Congruences/FirstOrder/TraceRelations.lean
decls:
  - New.Selmer.ribetCocycles.apply_eq_zero
  - New.Selmer.ribetCocycles.mem_selmerModule
  - New.Selmer.isTraceIdeal_withConjInv
  - New.Selmer.restrictToCoeffRing
  - New.Selmer.IsTraceIdeal.of_isLatticeIn
  - New.Selmer.summandRep_some_apply
  - New.Selmer.summandCoordIndexEquiv
  - New.Selmer.blockDiagonal'_summandRep
  - New.Selmer.exists_blockDiagonal_lattice
  - New.Selmer.exists_blockDiagonal_lattices
  - New.Selmer.IsTwistedLattice.twistRep_apply_eq_of_eq_one
  - New.Selmer.IsTwistedLattice.twistRep_eq_one_of_mem_inertiaAbove
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Trace relations and lattices

Ribet's method in [Ribet elements](/chapter/ribet-elements/) works with a family of Galois representations $u_x$, $x \in Y$, over $\overline{\mathbb{Q}}_\ell$, and with cocycles that obey the linear relations of the family. Before the method runs, three things must be in place. The cocycles must be Selmer classes, so that their length is bounded. The relations at the tame places must hold for the conjugate places too. And the lattices of the $u_x$ must split as a block for the main summand and one block for each character. This section proves the three facts.

Throughout, $G = G_E$ is the absolute Galois group `AbsGal D`, $c$ is complex conjugation, and $\chi = \mathrm{cyclotomicInv}$ is the inverse cyclotomic character. The module $\mathrm{Coc}(\rho, b)$ of [cocycles of a family](/chapter/main-summands/#cocycles-relations-and-selmer-lengths) is the set of $\rho$-cocycles $z : G \to (O/b)^r$ with $\sum_g \theta_g z(g) = 0$ for every finitely supported $\theta$ with $\sum_g \theta_g (u_x(g) - 1) = 0$ for all $x$.

### Ribet's cocycles are Selmer classes

**Lemma (Vanishing on the kernel).** Let $z \in \mathrm{Coc}(\rho, b)$ for the family $u$. If $u_x(g) = 1$ for all $x \in Y$, then $z(g) = 0$.

Lean: `New.Selmer.ribetCocycles.apply_eq_zero` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Take $\theta = \delta_g$, the function with value $1$ at $g$ and $0$ elsewhere. Then $\sum_h \theta_h (u_x(h) - 1) = u_x(g) - 1 = 0$ for all $x$. So $z(g) = \sum_h \theta_h z(h) = 0$. $\square$

**Lemma (Ribet's cocycles are Selmer classes).** Let $Y$ be finite. Let the $u_x : G \to M_n(O)$ be continuous, and let $u_x(g) = 1$ for every $x$ and every $g$ in an inertia group above a place outside a set $S$. Let $b \neq 0$, let $z \in \mathrm{Coc}(\rho, b)$, and let $z$ obey a set $L$ of relations. Then $z$ lies in the Selmer module $\mathrm{selmerModule}(\rho, S, L, O/b)$: it is locally constant, it is $0$ on the inertia groups outside $S$, and it obeys $L$.

Lean: `New.Selmer.ribetCocycles.mem_selmerModule` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* The ring $O$ is noetherian. By [the graph of a cocycle](/chapter/main-summands/#cocycles-relations-and-selmer-lengths) (`New.Selmer.ribetCocycles.exists_graph_subrepresentation`, proved by the Artin-Rees lemma) there are $k$ and a module $W$ such that the first projection is injective on $W$ and $((u_x(g) - 1)_x + b^k v,\ z(g)) \in W$ for all $g$ and $v$.

Let $g, g' \in G$ with $u_x(g') \equiv u_x(g) \pmod{b^k}$ for all $x$. Write $u_x(g') - 1 = u_x(g) - 1 + b^k v_x$. The two pairs $((u_x(g') - 1)_x + b^k \cdot 0,\ z(g'))$ and $((u_x(g) - 1)_x + b^k v,\ z(g))$ lie in $W$ and have the same first coordinate. So $z(g') = z(g)$. Thus $z(g)$ depends only on the reductions of the $u_x(g)$ modulo $b^k$. These reductions form a continuous map to a discrete finite set, since each $u_x$ is continuous and $Y$ is finite. So $z$ is locally constant.

For $g$ in an inertia group outside $S$, $u_x(g) = 1$ for all $x$, and $z(g) = 0$ by the previous lemma. The cocycle rule and the relations $L$ hold by hypothesis. $\square$

The lemma is the bridge between the automorphic side and the Galois side. A cocycle that the congruences produce obeys the relations of the family, and so it inherits continuity and the ramification of the family. No separate argument for continuity is needed.

### The trace relations for the conjugate places

[The trace ideal hypothesis](/chapter/ribet-elements/) asks that an $S$-module $\mathcal{J}$ contain $p$ times the traces and the traces of the relations that tie $\tau_j$ to $\varphi_j$ through a variable $X_j$ and a polynomial $H_j$. The relations come from the places $w_j$. The method also needs them at the conjugate places $\bar w_j$, through [the doubled family](/chapter/first-order-deformations/) `withConjInv`, whose value at $(j, \mathrm{false})$ is $(\tau_j^c)^{-1}$. For conjugate self-dual representations the new relations follow from the old ones.

**Lemma (Trace relations for the doubled family).** Let $(w, \tau, \varphi)$ be a tame generator family of level $\nu$. Let every $u_x$ be conjugate self-dual with twist $t$ (`New.Selmer.IsConjSelfDual`). Let $\mathcal{J}$ be a trace ideal for the traces of the $u_x$, the element $\ell^\nu$, the families $\tau$ and $\varphi$, the index map $\mathrm{id}$ and polynomials $H_j \in O[X]$. Then $\mathcal{J}$ is a trace ideal for the same traces and $\ell^\nu$, for the doubled families $\mathrm{withConjInv}\,\tau$ and $\mathrm{withConjInv}\,\varphi$, the index map $(j, b) \mapsto j$, and the same $H_j$.

Lean: `New.Selmer.isTraceIdeal_withConjInv` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* The first three conditions do not involve the families, so they carry over. Take $k = (j, b)$. For $b = \mathrm{true}$ the relation is the old one. Let $b = \mathrm{false}$, so the doubled family takes the values $(\tau_j^c)^{-1}$ and $(\varphi_j^c)^{-1}$. Fix $g$ and put $g' = (g^c)^{-1}$.

*Step 1: duality.* Conjugate self-duality with twist $t$ gives, for every $h$, $\operatorname{tr} u_x(h) = \chi(h)^{t-1} \operatorname{tr} u_x((h^c)^{-1})$. Apply it to $h = (\varphi_j^c)^{-i} g$. Since $((h)^c)^{-1} = \varphi_j^i g'$,
$$\operatorname{tr} u_x\big((\varphi_j^c)^{-i} g\big) = \chi\big((\varphi_j^c)^{-i} g\big)^{t-1} \operatorname{tr} u_x(\varphi_j^i g').$$
The same holds with $\tau_j$ in place of $\varphi_j$ and $i = 1$.

*Step 2: the character values.* The element $\tau_j$ is a tame generator at a place prime to $\ell$, so it lies in an inertia group there. The cyclotomic character is unramified at such places, and $\chi(\tau_j^c) = 1$. The element $\varphi_j$ fixes the $\ell^\nu$-th roots of unity, so $\chi(\varphi_j^c)^{\pm 1} \equiv 1 \pmod{\ell^\nu}$. Choose $d_m \in O$ with $\chi((\varphi_j^c)^{-1})^{m} = 1 + \ell^\nu d_m$.

*Step 3: the relation.* Put $G_j = (X - 1) H_j$ and write $G_j = \sum_i a_i X^i$. By steps 1 and 2,
$$\operatorname{tr}\big(G_j(u_x((\varphi_j^c)^{-1}))\, u_x(g)\big) = \chi(g)^{t-1}\Big(\operatorname{tr}\big(G_j(u_x(\varphi_j))\, u_x(g')\big) + \mathrm{err}_x\Big),$$
with $\mathrm{err}_x = \sum_i d_{(t-1)i}\, a_i\, \ell^\nu \operatorname{tr} u_x(\varphi_j^i g')$. In the same way the trace of $(u_x((\tau_j^c)^{-1}) - 1)\,u_x(g)$ is $\chi(g)^{t-1}$ times the trace of $(u_x(\tau_j) - 1)\,u_x(g')$. So the new relation at $g$ is
$$\chi(g)^{t-1} \Big(\mathrm{rel}_j(g') - X_j\, \mathrm{err}\Big),$$
where $\mathrm{rel}_j(g')$ is the old relation at $g'$. The old relation lies in $\mathcal{J}$. The function $\mathrm{err}$ is an $O$-combination of the functions $x \mapsto \ell^\nu \operatorname{tr} u_x(h)$, which lie in $\mathcal{J}$ by condition 3, and $X_j \in S$. So $X_j\,\mathrm{err} \in \mathcal{J}$. The scalar $\chi(g)^{t-1} \in O$ keeps the element in $\mathcal{J}$. $\square$

**Definition (Restriction of scalars).** For a subalgebra $S$ over the integers $\overline{\mathbb{Z}}_\ell$ of $\overline{\mathbb{Q}}_\ell$, `restrictToCoeffRing S O` is the same set, read as a subalgebra over a coefficient ring $O$.

Lean: `New.Selmer.restrictToCoeffRing` (New/Congruences/FirstOrder/TraceRelations.lean).

The method states the trace ideal over $\overline{\mathbb{Z}}_\ell$ and then needs it for lattices over a finite coefficient ring $O$.

**Lemma (Trace ideals pass to lattices).** Let $(w, \tau, \varphi)$ be a tame generator family of level $\nu$, and let the $u_x$ be conjugate self-dual with twist $t$. Let $u'_x : G \to M_n(O)$ be lattices in the $u_x$ (`New.Selmer.IsLatticeIn`). Let $\mathcal{J}$ be a trace ideal over a $\overline{\mathbb{Z}}_\ell$-subalgebra $S$ for the traces of the $u_x$, $\ell^\nu$, $\tau$, $\varphi$, the index map $\mathrm{id}$ and polynomials $H_j$ over $\overline{\mathbb{Z}}_\ell$. Let $H'_j \in O[X]$ have the same image as $H_j$ in $\overline{\mathbb{Q}}_\ell[X]$. Then $\mathcal{J}$ is a trace ideal over `restrictToCoeffRing S O` for the $u'_x$, $\ell^\nu$, the doubled families and the $H'_j$.

Lean: `New.Selmer.IsTraceIdeal.of_isLatticeIn` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* First restrict scalars from $\overline{\mathbb{Z}}_\ell$ to $O$ and replace $H_j$ by $H'_j$. The four conditions keep their meaning, since $O \subset \overline{\mathbb{Z}}_\ell$ and the polynomials have the same image. Then the previous lemma adds the conjugate places. Finally each lattice $u'_x$ comes with an algebra map $F_x$ from $M_n(O)$ to $M_n(\overline{\mathbb{Q}}_\ell)$ with $F_x(u'_x(g)) = u_x(g)$ that keeps traces ([lattices](/chapter/attached-representations/)). So every trace that occurs in the conditions for the $u'_x$ equals the corresponding trace for the $u_x$. $\square$

### Block diagonal lattices

In the method, the representation $u_x$ of a lift has the trace of a twisted main summand $\psi R$ plus the $t$ characters $\chi^e$, $e < t$. Its lattice should be the block sum of a lattice of $\psi R$ and the characters, so that the cocycles split into blocks.

**Definition (The summands).** For a lattice $T : G \to M_r(O)$, `summandRep T` is the family indexed by `Option (Fin t)`: at `none` it is $T$, and at `some e` it is the $1 \times 1$ representation $\chi^e$. The index type `SummandCoordIndex r i` is $r$ at `none` and a point at `some e` ([the summands](/chapter/main-summands/)).

Lean: `New.Selmer.summandRep`, `New.Selmer.SummandCoordIndex` (New/Congruences/LocalLoss/Basic.lean).

**Lemma (The character summands).** `summandRep T (some e) g` is the $1 \times 1$ matrix with entry $\chi(g)^e$.

Lean: `New.Selmer.summandRep_some_apply` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* This is the definition. $\square$

**Definition (The index bijection).** `summandCoordIndexEquiv r t` is the bijection from $r \sqcup \mathrm{Fin}\,t$ to the dependent sum of the `SummandCoordIndex r i`. It sends $a \in r$ to $(\mathrm{none}, a)$ and $e$ to $(\mathrm{some}\ e, \ast)$.

Lean: `New.Selmer.summandCoordIndexEquiv` (New/Congruences/FirstOrder/TraceRelations.lean).

**Lemma (The block sum).** The block diagonal matrix of the summands at $g$ is, after reindexing by the bijection above,
$$\begin{pmatrix} T(g) & 0 \\ 0 & \operatorname{diag}(\chi(g)^e)_{e < t} \end{pmatrix}.$$

Lean: `New.Selmer.blockDiagonal'_summandRep` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Compare entries in the four cases of the two indices. Each case holds by definition. $\square$

**Theorem (A block diagonal lattice).** Let $R$ be an $r$-dimensional and $R'$ an $n$-dimensional representation over $\overline{\mathbb{Q}}_\ell$, and let $R'$ have nondegenerate trace form on the span of its image ([`New.IsTraceNondeg`](/chapter/attached-representations/)). Let $\psi : G \to \overline{\mathbb{Q}}_\ell$ be a character with
$$\operatorname{tr} R'(g) = \psi(g) \operatorname{tr} R(g) + \sum_{e < t} \chi(g)^e \quad \text{for all } g.$$
Let $R_0$ be a lattice in $R$ over $O$, let $\psi' : G \to O$ agree with $\psi$, and let the twisted lattice $\psi' R_0$ span $M_r(O)$ over $O$. Let $\epsilon$ be a bijection from the dependent sum of the index types to $n$. Then $R'$ has a lattice $v$ over $O$ with $v(g)$ equal to the reindexing by $\epsilon$ of the block diagonal matrix of `summandRep (ψ' R₀)` at $g$.

Lean: `New.Selmer.exists_blockDiagonal_lattice` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Let $T = \psi' R_0$ and let $\rho$ be the family of summands of $T$, read over $\overline{\mathbb{Q}}_\ell$. Let $\Phi(\rho)$ be their block sum, reindexed by $\epsilon$.

*Step 1: semiprime span.* The family $\rho$ has semiprime span: if $y$ is in the span of the image and $y\,\rho(g)\,y = 0$ for all $g$, then $y = 0$. Check this on each block. On the block $T$, the map $M \mapsto y M y$ is $O$-linear and vanishes on every $T(g)$. Since the $T(g)$ span $M_r(O)$, it vanishes on all of $M_r(O)$. Take $M = E_{ba}$, the elementary matrix. Then $(y E_{ba} y)_{ab} = y_{ab}^2 = 0$, so $y_{ab} = 0$. On a character block, take $g = 1$: $y^2 = 0$ for a $1 \times 1$ matrix, so $y = 0$.

*Step 2: the traces agree.* Since $R_0$ is a lattice in $R$ and $\psi' = \psi$, the trace of $T(g)$ is $\psi(g) \operatorname{tr} R(g)$. The trace of a character block is $\chi(g)^e$. The trace of a block sum is the sum of the traces of the blocks, and reindexing does not change the trace. So $\operatorname{tr} R'(g) = \operatorname{tr} \Phi(\rho(g))$ for all $g$.

*Step 3: conjugation.* By [the conjugation theorem](/decl/New.IsTraceNondeg.exists_conj_of_trace_eq/), a representation with nondegenerate trace form and a representation with semiprime span that have the same traces are conjugate: there is an invertible $Z$ with $R'(g) = Z\, \Phi(\rho(g))\, Z^{-1}$. The block sum of the summands over $O$ maps to $\Phi(\rho(g))$ over $\overline{\mathbb{Q}}_\ell$, so it is a lattice in $R'$ with the conjugation $Z$. $\square$

**Remark (Formalization).** The conjugation theorem is a form of the classical fact that, in characteristic $0$, a semisimple representation is determined by its trace. The source uses a version with the hypothesis of nondegenerate trace form on one side and semiprime span on the other, which [the chapter on attached representations](/chapter/attached-representations/) proves. The hypothesis that $\psi' R_0$ spans $M_r(O)$ is a strong form of absolute irreducibility over $O$: by Nakayama's lemma it is equivalent to the statement that the reduction of $\psi' R_0$ spans the matrices over the residue field. The method gets it from [the main summands](/chapter/main-summands/) for large coefficient rings.

**Corollary (Block diagonal lattices for a family).** Let every $u_x$, $x \in Y$, have nondegenerate trace form and some lattice over $O$. Let $\mathcal{X} \subseteq Y$, and for $x \in \mathcal{X}$ let $\operatorname{tr} u_x = \psi \operatorname{tr} R_x + \sum_{e<t} \chi^e$, with lattices $R_{0,x}$, characters $\psi'_x = \psi$ over $O$, and $\psi'_x R_{0,x}$ spanning $M_r(O)$. Then there are lattices $u'_x$ in all the $u_x$ such that, for $x \in \mathcal{X}$, $u'_x$ is the reindexed block sum of the summands of $\psi'_x R_{0,x}$.

Lean: `New.Selmer.exists_blockDiagonal_lattices` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* For $x \in \mathcal{X}$ take the lattice of the theorem. For $x \notin \mathcal{X}$ take the given lattice. The choices are made by `choose`. $\square$

### Twisted lattices

[A twisted lattice](/chapter/main-summands/#cocycles-relations-and-selmer-lengths) (`New.Selmer.IsTwistedLattice`) is a model $(R_0, \psi', \zeta')$ over $O$ of $(R, \psi, \zeta)$: $R_0$ is a lattice in $R$, $\psi'$ and $\zeta'$ are $\psi$ and $\zeta$ with values in $O$, and the inertial element $\gamma$ acts on $\psi' R_0$ by the scalar $\zeta'$.

**Lemma (The twist at elements where $\psi$ is trivial).** Let $(R_0, \psi', \zeta')$ be a twisted lattice. If $\psi(g) = 1$, then $\psi' R_0(g) = R_0(g)$.

Lean: `New.Selmer.IsTwistedLattice.twistRep_apply_eq_of_eq_one` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* The twist multiplies $R_0(g)$ by $\psi'(g) = \psi(g) = 1$. $\square$

**Lemma (Ramification of the twisted lattice).** Fix the isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ (`PadicIso ℓ`). Let $(R_0, \psi', \zeta')$ be a twisted lattice. Let $\psi$ come from the norm one torus $U(1)$ (`New.IsFromU1`) for the places above $\ell$ and the modulus $Q$: $\psi(\mathrm{Art}(x)) = \eta(x/\bar x)$ for an idele class character $\eta$ that is trivial on the units outside these places and their conjugates. Let $R$ be a main summand ([`New.Selmer.IsMainSummandLike`](/chapter/main-summands/)) with twist $t$ and Hodge-Tate jumps $J$. Let $g$ lie in an inertia group above a place outside the places above $\ell$, the places above $p_0 p_1$ and the conjugation closure of $Q$. Then $\psi' R_0(g) = 1$.

Lean: `New.Selmer.IsTwistedLattice.twistRep_eq_one_of_mem_inertiaAbove` (New/Congruences/FirstOrder/TraceRelations.lean).

*Proof.* Since $g$ is in an inertia group outside $Q$ and its conjugates and outside $\ell$, the character $\psi$ is trivial at $g$: by local class field theory the inertia group is the image of the local units, and $\eta$ is trivial on them. By the previous lemma, $\psi' R_0(g) = R_0(g)$. A main summand is unramified outside $\ell p_0 p_1$, so $R(g) = 1$. A lattice in $R$ is $1$ wherever $R$ is $1$ (`New.Selmer.IsLatticeIn.eq_one`), so $R_0(g) = 1$. $\square$

The statement lists the full main summand hypothesis, but the proof uses only that $R$ is unramified outside $\ell p_0 p_1$. The comment in the source says so.
