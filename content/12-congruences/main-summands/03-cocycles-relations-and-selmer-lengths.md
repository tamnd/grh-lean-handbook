---
title: Cocycles, relations and Selmer lengths
lean:
  - New/Congruences/LocalLoss/Basic.lean
  - New/Congruences/GaloisRepresentations/SelmerHypotheses.lean
decls:
  - New.Selmer.ribetCocyclesIn
  - New.Selmer.ribetCocycles
  - New.Selmer.mem_ribetCocycles
  - New.Selmer.ribetCocycles.exists_graph_subrepresentation
  - New.Selmer.SummandCoordIndex
  - New.Selmer.summandRep
  - New.Selmer.tateTwist_smul
  - New.Selmer.localChart
  - New.Selmer.crysCocyclesAt
  - New.Selmer.crysRelations
  - New.Selmer.obeying_crysRelations
  - New.Selmer.crystallineColength
  - New.Selmer.AbsGal
  - New.Selmer.placesAboveM
  - New.Selmer.badPlaces
  - New.Selmer.placesDividing_union_subset_badPlaces
  - New.Selmer.twistError
  - New.Selmer.selmerCocycles
  - New.Selmer.IsTwistedLattice
  - New.Selmer.IsTwistedLattice.cyclotomicChar_eq_one
  - New.Selmer.HasTwistedLattice
  - New.Selmer.crystallineSelmerLength
  - New.Selmer.HasDivisibleSelmerLengthLe
  - New.Selmer.length_selmerCocycles_le_crystallineSelmerLength
  - New.Selmer.HasDivisibleSelmerLengthLe.hasTwistedLattice
  - New.Selmer.HasDivisibleSelmerLengthLe.mono
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Cocycles, relations and Selmer lengths

In Ribet's method ([Ribet elements](/chapter/ribet-elements/)) the cost of an extension is a length of a module of cocycles. This section defines three such measures: the module $\mathrm{Coc}(\rho, B)$ of cocycles that obey every relation of a family, the crystalline colength at $\ell$, and the crystalline Selmer length. The section ends with the error term $e'_\ell$ of the twisting theorem.

### Background on cocycles

- A *relation* on functions $c : G \to B^d$ is a finitely supported $f : G \to M_d(O)$, and $c$ *obeys* $f$ if $\sum_g f(g)\, c(g) = 0$. For a set $L$ of relations, $\mathrm{Ob}(L, B)$ is the module of functions that obey all of them. For a module $Z$, $\mathrm{Rel}(Z)$ is the set of relations that hold on $Z$. For submodules $S, T$, $\mathrm{relLen}(S, T)$ is the length of $S/(S \cap T)$, in $\mathbb{N} \cup \{\infty\}$ ([relations and cocycles](/chapter/fitting-ideals/#relations-and-cocycles), [lengths](/chapter/fitting-ideals/#discrete-valuation-rings-and-relative-lengths)).
- The cocycle rule $c(gh) = c(g) + \rho(g)c(h)$ is a set of relations, the *cocycle relations* of $\rho$ ([relations and cocycles](/chapter/fitting-ideals/#relations-and-cocycles)).
- A coefficient ring is the ring of integers $O$ of a finite Galois extension of $\mathbb{Q}_\ell$ in $\bar{\mathbb{Q}}_\ell$. "For all large $O$" means for all $O$ beyond some $O_0$ in the order of inclusion. The normalized length $\lambda_O$ counts $\ell$ as $1$ ([coefficient rings](/chapter/fitting-ideals/#coefficient-rings)).
- For a representation $\rho$ of a decomposition group above $\ell$, the crystalline cocycles form the module of $\rho$-cocycles whose extension is crystalline ([crystalline representations](/chapter/period-rings/#crystalline-representations)).
- The Selmer module of $\rho$ for a set $S$ of places and relations $L$ is the module of locally constant cocycles, zero on the inertia groups above places outside $S$, that obey $L$. Its length with coefficients in $\mathrm{Frac}(O)/O$ is the divisible Selmer length ([Selmer modules](/chapter/building-representations/#ramified-places-auxiliary-places-and-selmer-modules)).

### Cocycles that obey the relations of a family

Let $G$ be a group, $O$ a commutative ring, $u_x : G \to M_\sigma(O)$ for $x \in X$ a family of representations, and $\rho : G \to M_d(O)$ a representation. In Ribet's method, $\rho$ is one block of the $u_x$. A linear relation $\sum_g \theta_g (u_x(g) - 1) = 0$ that holds for all $x$ at once is a relation that the family cannot see. A cocycle that gives a class of the family must obey it.

**Definition (Cocycles of a family).** For an $O$-module $B$, $\mathrm{Coc}(\rho, B)$ is the set of $c : G \to B^d$ such that:

1. $c$ obeys the cocycle relations of $\rho$;
2. for every finitely supported $\theta : G \to O$ with $\sum_g \theta_g (u_x(g) - 1) = 0$ for all $x$, we have $\sum_g \theta_g\, c(g) = 0$.

It is an $O$-submodule. For $a \in O$, write $\mathrm{Coc}(\rho, a) = \mathrm{Coc}(\rho, O/a)$.

Lean: `New.Selmer.ribetCocyclesIn`, `New.Selmer.ribetCocycles` (New/Congruences/LocalLoss/Basic.lean).

*Proof that it is a submodule.* Both conditions are linear in $c$. $\square$

**Lemma (Membership).** A function $c : G \to (O/a)^d$ lies in $\mathrm{Coc}(\rho, a)$ if and only if $c(gh) = c(g) + \rho(g)\,c(h)$ for all $g, h$, and condition 2 holds.

Lean: `New.Selmer.mem_ribetCocycles` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* To obey the cocycle relations is the cocycle rule ([relations and cocycles](/chapter/fitting-ideals/#relations-and-cocycles)). $\square$

The next result is the reason for condition 2. A cocycle that obeys the relations of the family is, up to a large power of $a$, a linear function of the family. So it is the second component of a subrepresentation that is a graph.

**Theorem (Graph of a cocycle).** Let $X$ be finite and let $O$ be noetherian. Let $c \in \mathrm{Coc}(\rho, a)$. Then there are $k \in \mathbb{N}$ and a subrepresentation $Y$ of $M_\sigma(O)^X \times (O/a)^d$, where $g$ acts on the first factor by left multiplication with $(u_x(g))_x$ and on the second through $\rho$, such that:

1. the first projection is injective on $Y$;
2. $\big((u_x(g) - 1)_x + a^k v,\ c(g)\big) \in Y$ for every $g \in G$ and every $v \in M_\sigma(O)^X$.

Lean: `New.Selmer.ribetCocycles.exists_graph_subrepresentation` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* For $\theta : G \to O$ finitely supported, put $L\theta = \sum_g \theta_g (u_x(g) - 1)_x$ and $C\theta = \sum_g \theta_g c(g)$. Condition 2 says $L\theta = 0 \Rightarrow C\theta = 0$. The module $M = M_\sigma(O)^X$ is finitely generated over the noetherian ring $O$. By the Artin-Rees lemma for the ideal $(a)$ and the submodule $L(O^{(G)})$, there is $k_0$ such that for $n \geq k_0$,
$$a^n M \cap \mathrm{im}\, L = a^{n - k_0}\,(a^{k_0} M \cap \mathrm{im}\, L) .$$
Put $k = k_0 + 1$, define $N(\theta, v) = (L\theta + a^{k} v,\ C\theta)$, and let $Y$ be the image of $N$.

*Stability.* For $g \in G$, let $\mathrm{sh}_g$ send $(\theta, v)$ to $(\theta', u(g) v)$, where $\theta'$ sends the point mass at $h$ to the point mass at $gh$ minus the point mass at $g$. Then $u(g)(u(h) - 1) = (u(gh) - 1) - (u(g) - 1)$, and the cocycle rule gives $\rho(g)c(h) = c(gh) - c(g)$. So $g \cdot N(\theta, v) = N(\mathrm{sh}_g(\theta, v))$, and $Y$ is a subrepresentation.

*The graph.* Let $N(\theta, v)$ have first component $0$. Then $L\theta = a^{k}(-v)$ lies in $a^{k} M \cap \mathrm{im}\, L$. By Artin-Rees with $n = k$, $L\theta = a\, w$ with $w = L\eta$ for some $\eta$. Then $L(a\eta - \theta) = 0$, so $C(a\eta - \theta) = 0$, and $C\theta = a\, C\eta = 0$ because $a$ kills $O/a$. So the point is $0$, and the first projection is injective on $Y$.

*The points.* $N(\delta_g, v) = ((u_x(g) - 1)_x + a^k v,\ c(g))$. $\square$

### The summands of a lift

A lift in Ribet's method has a main summand $T$ of rank $r$ and $t$ characters of rank one. The index set of the $i$-th summand, for $i \in \{\ast\} \cup \{0, \dots, t - 1\}$, is $r$ for the main summand $\ast$ and a point for each character. The $i$-th summand is $T$ for $i = \ast$, and the Tate twist $O(-e) = \varepsilon^{-e}$ for $i = e$.

Lean: `New.Selmer.SummandCoordIndex`, `New.Selmer.summandRep` (New/Congruences/LocalLoss/Basic.lean).

**Lemma (Tate twists on a decomposition group).** Let $\mathrm{emb}$ be an embedding of $\bar{\mathbb{Q}}$ in $\bar{\mathbb{Q}}_\ell$ that induces the place $A$, with the map $\mathrm{emb}_\ast$ from the decomposition group of $A$ to $G_\ell$. Then an element $g$ of the decomposition group acts on $O(-c)$ by $\varepsilon_\ell(\mathrm{emb}_\ast g)^{-c}$, where $\varepsilon_\ell$ is the cyclotomic character of $G_\ell$.

Lean: `New.Selmer.tateTwist_smul` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* The global cyclotomic character at $g$ equals the local one at $\mathrm{emb}_\ast g$, because $\mathrm{emb}$ maps roots of unity to roots of unity compatibly. $\square$

### The crystalline relations above $\ell$

**Definition (Local chart).** For each place $v$ of $E$ above $\ell$, fix an embedding $e_v : \bar{\mathbb{Q}} \to \bar{\mathbb{Q}}_\ell$ that induces the chosen place of $\bar{\mathbb{Q}}$ over $v$, with the open embedding of its decomposition group into $G_\ell$.

Lean: `New.Selmer.localChart` (New/Congruences/LocalLoss/Basic.lean).

**Remark (Formalization).** The chart is an instance made by a choice. Every later use goes through this one instance, so no two charts need to agree. The crystalline condition at $v$ does not depend on the chart, but the source does not prove this and does not need it.

**Definition (Crystalline relations).** Let $u : G_E \to M_n(O)$. For $v \mid \ell$, $Z_v(u)$ is the module of crystalline cocycles of the decomposition group $G_v$ of the chosen place over $v$, with values in $O^n$. The *crystalline relations* of $u$ are the relations of $\mathrm{Rel}(Z_v(u))$ for all $v \mid \ell$, extended by zero from $G_v$ to $G_E$.

Lean: `New.Selmer.crysCocyclesAt`, `New.Selmer.crysRelations` (New/Congruences/LocalLoss/Basic.lean).

**Lemma (Local form).** A function $c : G_E \to (O/a)^n$ obeys the crystalline relations of $u$ if and only if, for every $v \mid \ell$, its restriction to $G_v$ obeys every relation that holds on $Z_v(u)$.

Lean: `New.Selmer.obeying_crysRelations` (New/Congruences/LocalLoss/Basic.lean).

*Proof.* A relation $f$ supported on $G_v$, pushed to $G_E$, evaluates $c$ only on $G_v$. $\square$

So a cocycle modulo $a$ that obeys the crystalline relations is one that looks crystalline to every linear test that crystalline cocycles pass. This is the form of the crystalline condition that survives reduction modulo $\ell^M$.

**Definition (Crystalline colength).** Let $w_x$, $x \in X$, be a family of representations and $u$ a summand. The *crystalline colength* of $u$ modulo $\ell^M$ is
$$\mathrm{relLen}\big(\mathrm{Coc}(u, \ell^M),\ \mathrm{Ob}(\mathrm{crysRel}(u), O/\ell^M)\big) \in \mathbb{N} \cup \{\infty\},$$
where $\mathrm{Coc}$ is taken for the family $w$.

Lean: `New.Selmer.crystallineColength` (New/Congruences/LocalLoss/Basic.lean).

[The local loss](/chapter/local-loss/) bounds this colength by the defect bound of the previous section.

### Places and the Selmer groups

Write $G_E = \mathrm{Gal}(\bar{\mathbb{Q}}/E)$. The places *above $M$* are the finite places $v$ of $E$ that contain $p_0$ or $p_1$. The *bad places* for $\ell$ are the places that divide $\ell M N$, where $N$ is the level of the data.

Lean: `New.Selmer.AbsGal`, `New.Selmer.placesAboveM`, `New.Selmer.badPlaces`, with `New.Selmer.placesDividing_union_subset_badPlaces` for the fact that the places above $\ell$ and above $M$ are bad (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Definition (Selmer cocycles modulo $\ell^m$).** Let $\rho : G_E \to M_n(O)$, let $Q$ be a finite set of places, and let $\gamma \in G_E$. The module $\mathrm{Sel}_m(\rho, Q, \gamma)$ is the module of locally constant cocycles $c : G_E \to (O/\ell^m)^n$ for $\rho$ that are zero on the inertia groups above places outside $\{v \mid \ell\} \cup \{v \mid M\} \cup Q \cup \bar Q$, obey the crystalline relations of $\rho$, and satisfy $c(\gamma) = 0$.

Lean: `New.Selmer.selmerCocycles` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

When $\rho(\gamma) - 1$ is invertible, each cocycle class has exactly one member with $c(\gamma) = 0$. So the condition $c(\gamma) = 0$ turns a module of cocycles into a module of classes.

**Definition (Crystalline Selmer length).** With $\rho, Q, \gamma$ as above, the *crystalline Selmer length* of $\rho$ is the divisible Selmer length of $\rho$ for the places $\{v \mid \ell\} \cup \{v \mid M\} \cup Q \cup \bar Q$ and the relations $\mathrm{crysRel}(\rho) \cup \{c \mapsto c(\gamma)\}$. It lies in $\mathbb{N} \cup \{\infty\}$.

Lean: `New.Selmer.crystallineSelmerLength` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Lemma (Finite levels).** For every $M$, $\mathrm{len}_O\, \mathrm{Sel}_M(\rho, Q, \gamma)$ is at most the crystalline Selmer length of $\rho$ for $Q$ and $\gamma$.

Lean: `New.Selmer.length_selmerCocycles_le_crystallineSelmerLength` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* A cocycle of $\mathrm{Sel}_M$ obeys the crystalline relations, the relations of the inertia groups and the relation $c(\gamma) = 0$. So $\mathrm{Sel}_M$ lies in the Selmer module with coefficients in $O/\ell^M$ for the enlarged set of relations. The length of that module is at most the divisible Selmer length, since $\ell^M \neq 0$ ([Selmer modules](/chapter/building-representations/#ramified-places-auxiliary-places-and-selmer-modules)). $\square$

### Twisted lattices and the Selmer hypothesis

The twisting theorem twists a representation $R$ over $\bar{\mathbb{Q}}_\ell$ by a character $\psi$. To speak of a Selmer group, one needs a lattice: a model over a coefficient ring $O$. A *lattice in* $R$ is a $u : G_E \to M_n(O)$ such that $P^{-1} R(g) P = u(g)$ for one $P \in \mathrm{GL}_n(\bar{\mathbb{Q}}_\ell)$ and all $g$ ([representations from traces](/chapter/attached-representations/#representations-from-traces)).

**Definition (Twisted lattice).** Let $\psi : G_E \to \bar{\mathbb{Q}}_\ell$ be a character, $R$ a representation, $\gamma \in G_E$ and $\zeta$ an $\ell$-adic integer of $\bar{\mathbb{Q}}_\ell$. A triple $(u, \psi', \zeta')$ over $O$ is a *twisted lattice* for these data if:

1. $\zeta' = \zeta$, and $\psi'(g) = \psi(g)$ for all $g$;
2. $u$ is a lattice in $R$;
3. $\psi' \otimes u$ sends $\gamma$ to the scalar $\zeta'$;
4. $\zeta' - 1$ is a unit of $O$;
5. $\gamma$ lies in an inertia group above a place of $E$ that does not divide $\ell$.

The data *have a twisted lattice* if such a triple exists over all large $O$.

Lean: `New.Selmer.IsTwistedLattice`, `New.Selmer.HasTwistedLattice` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Lemma (Cyclotomic character at $\gamma$).** For a twisted lattice, $\varepsilon(\gamma) = 1$.

Lean: `New.Selmer.IsTwistedLattice.cyclotomicChar_eq_one` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* By condition 5, $\gamma$ is in inertia at a place prime to $\ell$, where the cyclotomic character of $\ell$-power roots of unity is unramified. $\square$

**Definition (Selmer hypothesis).** For $\mathrm{sel} \in [0, \infty]$, the data $(\psi, R, Q, \gamma, \zeta)$ have *divisible Selmer length at most* $\mathrm{sel}$ if for all large $O$ there is a twisted lattice $(u, \psi', \zeta')$ over $O$ with
$$\lambda_O\big(\text{crystalline Selmer length of } \psi' \otimes u \text{ for } Q, \gamma\big) \leq \mathrm{sel} .$$

Lean: `New.Selmer.HasDivisibleSelmerLengthLe` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Lemma.** The Selmer hypothesis for $\mathrm{sel}$ gives a twisted lattice, and it implies the Selmer hypothesis for every $\mathrm{sel}' \geq \mathrm{sel}$.

Lean: `New.Selmer.HasDivisibleSelmerLengthLe.hasTwistedLattice`, `New.Selmer.HasDivisibleSelmerLengthLe.mono` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

*Proof.* Forget the length bound, or compose it with $\mathrm{sel} \leq \mathrm{sel}'$, for each large $O$. $\square$

**Remark (Formalization).** The textbook Bloch-Kato Selmer group is a subgroup of $H^1(G_E, V/T)$ cut out by local conditions, with $H^1_f$ at $\ell$ (S. Bloch and K. Kato, *L-functions and Tamagawa numbers of motives*, The Grothendieck Festschrift I (1990), Section 3). The source uses cocycles, not classes. It fixes a representative of each class by $c(\gamma) = 0$, which is valid when $\rho(\gamma) - 1$ is invertible, as condition 4 gives. The crystalline condition at $\ell$ is the set of linear relations of the crystalline cocycles, not the kernel of a map to $H^1(G_v, B_{\mathrm{crys}} \otimes V)$. The source does not prove that the two agree, and the argument needs only the relational form. The hypothesis holds "for all large $O$", so a bound proved over one ring must hold over all larger rings.

### The twist error

**Definition (Twist error).** For a prime $\ell$, put
$$e'_\ell = (4f + 3)\, r\, v_\ell(N_{\mathrm{ch}}) + 2^{-\ell},$$
where $f$ is the number of infinite places of $E$ and $N_{\mathrm{ch}}$ is the chosen group order: the order of the product of the groups $\mathrm{GL}_{rt}$ over the residue fields at the chosen places ([the objects of the upper bound](/chapter/upper-bound-objects/)).

Lean: `New.Selmer.twistError` (New/Congruences/GaloisRepresentations/SelmerHypotheses.lean).

**Remark (Formalization).** The term $2^{-\ell}$ is never $0$, so $e'_\ell > 0$ for every $\ell$. The sum of $e'_\ell$ over all primes still converges, since $v_\ell(N_{\mathrm{ch}}) = 0$ for all but finitely many $\ell$. The term makes a bound over all primes into a sum of positive terms. Here $v_\ell$ is the $\ell$-adic valuation of a natural number.
