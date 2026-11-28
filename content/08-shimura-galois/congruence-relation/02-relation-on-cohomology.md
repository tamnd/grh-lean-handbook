---
title: From points to cohomology
lean:
  - Lib/Cohomology/Etale/Basic.lean
  - Lib/ClassField/Places/GaloisDefs.lean
  - Lib/Shimura/CongruenceRelation/EichlerShimura.lean
  - Lib/Cohomology/SmoothBaseChange.lean
decls:
  - New.Variety.Cancels
  - New.Variety.Cancels.mono
  - New.Variety.CongruenceRelation
  - New.IsFrob
  - New.Variety.ellAdicCohom.frobEnd
  - New.Variety.ellAdicCohom.frobEnd_app
  - New.Variety.ellAdicCohom.ellAdicPull_frobEnd
  - New.Variety.ellAdicCohom.congruence_relation
  - New.Variety.ellAdicCohom.galoisAction_eq_one_of_inertia
  - New.Variety.isTestCohomEquiv_baseChangeTransition
status: drafted
drafted_by: writer@claude-opus-5-5
---
## From points to cohomology

This section proves step 2 of the plan. A relation between Frobenius twists of maps, checked at the points of the special fibre, gives a relation between pull-backs and the Galois action on cohomology. The case of the identity relation gives that inertia acts trivially. Section 3 proves the relation on points for the Hecke legs of the model.

### Relations between points

The relation on points is a relation in a free abelian group. Let $V$ be a set, $v : I \to V$ a map from a finite set and $m : I \to \mathbb{Z}$.

**Definition.** The integers $m_i$ *cancel along* $v$ if $\sum_{i \in I} m_i [v_i] = 0$ in the free abelian group on $V$. Equivalently, for each $y \in V$ the sum of the $m_i$ with $v_i = y$ is $0$.

Lean: `New.Variety.Cancels` (Lib/Cohomology/Etale/Basic.lean).

**Lemma.** If the $m_i$ cancel along $v$, and $v'$ factors through $v$ (that is, $v_i = v_j$ implies $v'_i = v'_j$), then the $m_i$ cancel along $v'$.

Lean: `New.Variety.Cancels.mono` (Lib/Cohomology/Etale/Basic.lean).

*Proof.* Each fibre of $v'$ is a union of fibres of $v$, and the sum of the $m_i$ over each fibre of $v$ is $0$. $\square$

Now let $R$ be a ring, $W$ and $Z$ schemes over $\operatorname{Spec} R$, $p$ a prime and $\mathfrak{p} \subseteq R$ a set. For a field $k$ of characteristic $p$ write $\operatorname{Frob}_k : k \to k$, $t \mapsto t^p$.

**Definition (Congruence relation).** Let $u_i : W \to Z$ be maps over $R$, $m_i \in \mathbb{Z}$ and $a_i \in \mathbb{N}$, for $i$ in a finite set $I$. The family satisfies the *congruence relation modulo $\mathfrak{p}$* with coefficients $m$ and exponents $a$ if the following holds. For every field $k$ of characteristic $p$ and every point $x : \operatorname{Spec} k \to W$ whose ring map $R \to k$ kills every element of $\mathfrak{p}$, the $m_i$ cancel along
$$i \mapsto u_i \circ x \circ \operatorname{Spec}(\operatorname{Frob}_k^{a_i}).$$

Lean: `New.Variety.CongruenceRelation` (Lib/Cohomology/Etale/Basic.lean).

So the relation says $\sum_i m_i [\operatorname{Frob}^{a_i}(u_i(x))] = 0$ as a formal sum of $k$-points of $Z$, for every point $x$ of the fibre over $\mathfrak{p}$.

**Remark (Formalization).** This is a pointwise relation. The classical congruence relation is an identity of cycles on $W \times Z$ in characteristic $p$, with multiplicities; for modular curves the Frobenius graph enters with multiplicity $1$ and its transpose with multiplicity $p$. The pointwise relation forgets the cycles and keeps only the formal sums of points. A multiplicity of the classical relation appears here as several indices $i$ with the same twisted point, as in the case $n = 2$ of Section 3. The source can work with points because its cohomology is built from free abelian groups on points (Volume 7, Chapter 2), so that a relation on points passes to cohomology directly. The classical proofs use the relation of cycles. The source does not discuss whether the pointwise form would be enough for étale cohomology in the sense of SGA 4, and this book does not either.

**Example.** Take $I = \{0, 1\}$, $u_0 = u_1 = \operatorname{id}_Z$, $m = (-1, 1)$ and $a = (0, 0)$. At each point the formal sum is $-[x] + [x] = 0$. So this family satisfies the congruence relation for every $\mathfrak{p}$. The proof of the inertia lemma below uses exactly this family.

### Frobenius elements

Let $\Omega$ be a field with an action of a group $\Gamma$, and let $A$ be a valuation subring of $\Omega$, with maximal ideal $\mathfrak{m}_A$ and valuation $v_A$.

**Definition (Frobenius element).** Let $q \in \mathbb{N}$. An element $\sigma \in \Gamma$ is a *Frobenius for $q$ at $A$* if $\sigma$ stabilises $A$ and $\sigma x - x^q \in \mathfrak{m}_A$ for every $x \in A$.

Lean: `New.IsFrob` (Lib/ClassField/Places/GaloisDefs.lean).

For $q$ the order of the residue field of a place below $A$ this is an arithmetic Frobenius. For $q = 1$ it says that $\sigma$ lies in the inertia group of $A$. The definition puts no condition on the residue field of $A$ itself, so it also makes sense for $A$ of mixed characteristic with residue field $\bar{\mathbb{F}}_p$, which is the case of interest. If $\sigma$ is a Frobenius for $q$, then $\sigma^e$ is a Frobenius for $q^e$.

### Frobenius acts trivially on cohomology

The first ingredient is the classical fact that the absolute Frobenius of a scheme of characteristic $p$ acts as the identity on étale cohomology with coefficients prime to $p$. The source cites Stacks Project Tag 03SN for it. In the source the statement is about the cohomology of a functor $U$ on rings, built as in Volume 7, Chapter 2.

**Definition.** Let $U$ be a functor on rings such that $p = 0$ in every ring $B$ for which $U(B)$ is not empty. For $j \in \mathbb{N}$, the endomorphism $\operatorname{Fr}^j$ of $U$ sends $x \in U(B)$ to $U(\phi)(x)$, where $\phi : B \to B$ is $b \mapsto b^{p^j}$.

Lean: `New.Variety.ellAdicCohom.frobEnd` (Lib/Shimura/CongruenceRelation/EichlerShimura.lean). The value at a point is `New.Variety.ellAdicCohom.frobEnd_app` (same file).

The map $b \mapsto b^{p^j}$ is a ring map because $p = 0$ in $B$. Naturality holds because ring maps commute with $p^j$-th powers.

**Lemma (Frobenius acts trivially).** Let $U$ be as above. Then the pull-back along $\operatorname{Fr}^j$ is the identity of $\mathbb{Q}_\ell \otimes H^n(U, \mathbb{Z}_\ell)$, for every $n$ and $j$.

Lean: `New.Variety.ellAdicCohom.ellAdicPull_frobEnd` (Lib/Shimura/CongruenceRelation/EichlerShimura.lean).

*Proof.* The cohomology of $U$ is computed on the category of points $(B, x)$ of $U$, with $B$ a test ring, through the coefficient functor $(B, x) \mapsto \mathbb{Z}_\ell(B)$. Here $\mathbb{Z}_\ell(B)$ is the ring of Witt vectors of the locally constant functions $\operatorname{Spec} B \to \mathbb{F}_\ell$. The Frobenius gives an endomorphism $\eta$ of the functor $(B, x) \mapsto B$ on this category, $\eta_B(b) = b^{p^j}$. It acts on the coefficients through the map $\operatorname{Spec} B \to \operatorname{Spec} B$ that it induces. This map is the identity: a prime ideal $\mathfrak{q}$ contains $b^{p^j}$ exactly when it contains $b$. So $\eta$ acts trivially on the coefficients. The endomorphism $\operatorname{Fr}^j$ of $U$ moves the tautological point of the category of points in the same way as $\eta$. Pull-back to the category of points along the tautological point is bijective on cohomology (Volume 7, Chapter 2). So the pull-back along $\operatorname{Fr}^j$ is the pull-back along $\eta$, which can be moved to the coefficients, where it is the identity. $\square$

The proof uses nothing about $U$ except that its points live in characteristic $p$. The classical proof is the same: the absolute Frobenius is a universal homeomorphism that is the identity on the underlying space.

### The relation on cohomology

Let $\Omega$ be an algebraic closure of $\mathbb{Q}$, with an action of $\Gamma$ by $R$-algebra automorphisms, and let $A \subseteq \Omega$ be a valuation ring. For a scheme $Y$ over $R$ write $V^n(Y) = \mathbb{Q}_\ell \otimes H^n(Y_\Omega, \mathbb{Z}_\ell)$, with the action of $\Gamma$ through $\Omega$. The textbook form of the next theorem is in Deligne's Bourbaki exposé 355 (1969), for modular curves, and in Harris and Taylor, *The geometry and cohomology of some simple Shimura varieties* (2001), Chapter III, for the unitary case.

**Theorem (Eichler-Shimura relation on cohomology).** Assume the following.

* The image of $R$ in $\Omega$ lies in $A$, the prime $p$ lies in $\mathfrak{m}_A$, and $\ell$ is a unit in $A$.
* $W$ and $Y$ are proper over $R$, and $Y$ is charted over $R$ (the hypothesis that stands in for smoothness; it gives smooth base change).
* $g \in \Gamma$ is a Frobenius for $p^f$ at $A$.
* $u_i : W \to Y$, $e_i \in \mathbb{N}$ and $m_i \in \mathbb{Z}$, for $i$ in a finite set $I$, satisfy the congruence relation modulo $\mathfrak{p}$ with coefficients $m_i$ and exponents $e_i f$, where $\mathfrak{p}$ is the preimage in $R$ of $\mathfrak{m}_A$.

Then for every $x \in V^n(Y)$,
$$\sum_{i \in I} m_i \, u_i^*\big(g^{-e_i} x\big) = 0 \quad \text{in } V^n(W).$$

Lean: `New.Variety.ellAdicCohom.congruence_relation` (Lib/Shimura/CongruenceRelation/EichlerShimura.lean). Smooth base change, used in the proof, is `New.Variety.isTestCohomEquiv_baseChangeTransition` (Lib/Cohomology/SmoothBaseChange.lean).

The Galois element in the conclusion is $g^{-1}$, a geometric Frobenius. The sign is forced: on the special fibre the arithmetic Frobenius $g$ acts on coefficients as $t \mapsto t^{p^f}$, and moving points forward by Frobenius is the inverse operation on cohomology.

The idea of the proof is the classical one. Cohomology over $\Omega$ is the same as cohomology over $A$, by smooth base change. Cohomology over $A$ injects into cohomology of the special fibre, by proper base change. On the special fibre, $g^{-e_i}$ becomes a Frobenius, which acts trivially by the lemma above. Then the relation on points finishes the proof. The source adds one step that is special to its cohomology: a relation that holds at every point holds in cohomology, because the locus where it holds is dense for cohomology.

*Proof.* Step 1 (lift to $A$). Since $Y$ is charted, smooth base change makes the pull-back from the cohomology of $Y$ over $A$ to the cohomology of $Y$ over $\Omega$ bijective. So $x$ is the pull-back of a class $y$ over $A$.

Step 2 (the maps $\mu_i$). The element $g$ stabilises $A$, so $\sigma_i = g^{-e_i}$ restricts to a ring automorphism of $A$ that fixes the image of $R$. A point of $W$ over $A$ is a pair $(w, \omega)$, with $\omega$ a ring map from $A$. Let $\mu_i$ send $(w, \omega)$ to $(u_i(w), \omega \circ \sigma_i)$. Over $\Omega$ the pull-back along $\mu_i$ is $x \mapsto u_i^*(g^{-e_i} x)$. So it is enough to prove that $\sum_i m_i \mu_i^* y = 0$ over $A$.

Step 3 (restrict to the special fibre). Let $U_0$ be the part of the points of $W$ over $A$ whose ring map kills $\mathfrak{m}_A$. Every such point lives in characteristic $p$, since $p \in \mathfrak{m}_A$. Restriction from $W$ over $A$ to $U_0$ is injective on cohomology, by proper base change; here the coefficients are $\mathbb{Z}/\ell$ and $\ell$ is a unit in $A$. So it is enough to prove that $\sum_i m_i \mu_i^* y$ restricts to $0$ on $U_0$.

Step 4 (insert Frobenius). On $U_0$ let $F_i = \mu_i \circ \operatorname{Fr}^{e_i f}$. By the lemma on Frobenius, $F_i^* = \mu_i^*$ on the cohomology of $U_0$. So it is enough to prove $\sum_i m_i F_i^* y = 0$.

Step 5 (the relation locus is dense). Let $L \subseteq U_0$ be the locus of points $z$ where the $m_i$ cancel along $i \mapsto F_i(z)$. On $L$ the sum $\sum_i m_i [F_i]$ is $0$ as a map into the free abelian group on the points of $Y$, so the sum of pull-backs vanishes on $L$. It remains to show that restriction to $L$ is injective on cohomology. By properness, Volume 7 gives a criterion: it is enough to treat points $z$ with values in an algebraically closed field $k$ and to show that the $m_i$ cancel along $i \mapsto F_i(z)$.

Step 6 (the relation at a geometric point). Write $z = (w, \omega)$ with $\omega : A \to k$ and $\omega(\mathfrak{m}_A) = 0$. Since $g$ is a Frobenius for $p^f$, $\sigma_i^{-1}(a) - a^{p^{e_i f}} \in \mathfrak{m}_A$ for every $a \in A$. So
$$\omega(a) = \omega(\sigma_i a)^{p^{e_i f}} \quad (a \in A).$$
Hence $F_i(z)$ is the point $\operatorname{Frob}^{e_i f}(u_i(w))$, together with the ring map $\omega$, the same for all $i$. The point $w$ kills $\mathfrak{p}$, so the congruence relation says that the $m_i$ cancel along $i \mapsto \operatorname{Frob}^{e_i f}(u_i(w))$. By the lemma on factoring, they cancel along $i \mapsto F_i(z)$. $\square$

**Remark (Formalization).** Steps 1, 3 and 5 are theorems about the cohomology of Volume 7, Chapter 2, and they are the deep part of the proof. Smooth base change is `New.Variety.isTestCohomEquiv_baseChangeTransition` (Lib/Cohomology/SmoothBaseChange.lean). It asks only that $Y$ be charted: the functor of points of $Y$ has a subfunctor that is covered by pieces étale over tori. It is stated with coefficients $\mathbb{Z}/\ell$. Proper base change and the density criterion are stated for functors proper over the base. This chapter takes them as given. The hypothesis on $W$ is only properness. No smoothness of $W$ is needed, because the class $x$ lives on $Y$.

### Inertia acts trivially

**Corollary (Good reduction).** Let $R$, $\Omega$, $A$, $p$, $\ell$ and $Y$ be as in the theorem. Let $g$ lie in the inertia group of $A$. Then $g$ acts as the identity on $V^n(Y)$.

Lean: `New.Variety.ellAdicCohom.galoisAction_eq_one_of_inertia` (Lib/Shimura/CongruenceRelation/EichlerShimura.lean).

*Proof.* The element $g^{-1}$ is a Frobenius for $p^0 = 1$, since the inertia group is a group. Apply the theorem with $f = 0$, $W = Y$, $I = \{0, 1\}$, $u_0 = u_1 = \operatorname{id}$, $e = (0, 1)$ and $m = (-1, 1)$. The exponents $e_i f$ are $0$, and the relation on points is the identity relation of the example. The conclusion reads $-x + (g^{-1})^{-1} x = 0$, that is $g x = x$. $\square$

The classical statement is that a smooth proper variety with good reduction at $A$ has cohomology unramified at $A$. For abelian varieties this is one direction of the criterion of Néron, Ogg and Shafarevich. The source cites Stacks Project Tag 0GKD for the smooth and proper base change behind it.
