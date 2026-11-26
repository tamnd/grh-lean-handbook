---
title: Even classes and cocycles of Tate twists
lean:
  - New/Congruences/FirstOrder/EvenClasses.lean
  - New/Congruences/FirstOrder/TateTwistCocycles.lean
decls:
  - New.Selmer.IsAuxTwist
  - New.Selmer.tateTwist_eq_one_of_cyclotomicChar_eq_one
  - New.Selmer.IsTameGeneratorFamily.cyclotomicInv_withConjInv_eq_one_and_dvd
  - New.Selmer.add_conjGal_mem_evenClasses
  - New.Selmer.apply_withConjInv_false_eq_neg
  - New.Selmer.apply_eq_zero_of_mem_obeying_crysRelations
  - New.Selmer.relLength_torsionBy_le_length_shaOdd
  - New.Selmer.hasTriangleCost_tateTwist
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Even classes and cocycles of Tate twists

This section proves that a triangle of primes gives the triangle cost of chapter 2 for each character $O(-e)$. The bound is the length of the odd classes plus the local loss above $\ell$. Throughout, $E$ contains a primitive $5040$-th root of unity, and cocycles take values in $(O/\ell^\nu)(-e)$, written as vectors of length one.

### What is recalled

[Auxiliary primes and first-order deformations](/chapter/first-order-deformations/) states the following objects of the file EvenClasses. This section uses them as stated there.

- [Even classes](/chapter/first-order-deformations/#the-real-subfield-and-even-classes) of exponent $e$ for $S$ (`New.Selmer.evenClasses`): cocycles in $(O/\ell^\nu)(-e)$ unramified off $\ell$, $S$ and $\bar S$, with $z(g^c) = z(g)$, that vanish on the elements of the decomposition groups above $\ell$ with $\mathrm{cyc} = 1$.
- A [tame generator family](/chapter/first-order-deformations/#the-real-subfield-and-even-classes) $(w_j, \tau_j, \varphi_j)$ of level $\nu$ (`New.Selmer.IsTameGeneratorFamily`): $w_j$ off $\ell$, $\varphi_j$ fixes the $\ell^\nu$-th roots of unity, and $\tau_j$ is the chosen tame generator at a place over $w_j$. Its doubled family (`New.Selmer.withConjInv`) adds the elements $(\tau_j^c)^{-1}$.
- [Killing tame generators removes ramification](/decl/New.Selmer.IsTameGeneratorFamily.mem_selmerModule_of_tame_eq_zero/): a cocycle unramified off $S \cup \{w_j\} \cup \{\bar w_j\}$ that vanishes on the doubled family is unramified off $S$.
- [The divisibility](/decl/New.Selmer.four_dvd_cyclotomicChar_sub_one/) $4 \mid \mathrm{cyc}(a) - 1$ for every $a \in G$.
- [Testing with maps to $\mathbb{Z}/\ell^\nu$](/decl/New.Selmer.eq_zero_of_forall_mem_Z1_of_mem_evenClasses/).
- A [triangle of primes](/chapter/first-order-deformations/#the-triangle-of-primes) for $a \in G$ with bounds $h$ and $c$ (`New.Selmer.IsPrimeTriangle`). It has five conditions: a tame generator family, test points, separation, the triangle condition, and $4(\mathrm{cyc}(a)^{-e} - 1)^2 \mid \ell^h$. This section numbers them in the same way.

### The rest of the file on even classes

**Definition (Auxiliary twist).** Let $S$ and $Q$ be finite sets of places, $\psi \colon G \to \bar{\mathbb{Q}}_\ell$ a character and $c \in [0, \infty]$. The pair $(Q, \psi)$ is an *auxiliary twist* for $S$ with cost $c$ if three conditions hold.

1. $Q$ is auxiliary for $S$.
2. $\psi$ comes from the norm-one torus for the places above $\ell$ and for $Q$.
3. There are tame generators $\sigma_P$ at places over the $P \in Q$, off $\ell$, with $\sum_{P \in Q} v_\ell(\psi(\sigma_P) - 1) \leq c$.

Lean: `New.Selmer.IsAuxTwist` (New/Congruences/FirstOrder/EvenClasses.lean).

Condition 3 says that $\psi$ is not too close to $1$ on tame inertia. The twisting theorem of [Stickelberger systems and the twisting theorem](/chapter/twisting-theorem/) produces such twists, and [Ribet's element for Galois representations](/chapter/ribet-elements/#ribets-element-for-galois-representations) uses $c$ as its bound $\mathrm{ram}$.

**Remark (Formalization).** Condition 3 is written as a tame generator family of level $0$ with $\varphi_P = 1$. At level $0$ the condition on $\varphi$ asks that $\mathrm{cyc}_1(1) = 1$, which always holds, so only the conditions on $w$ and $\tau$ remain. The valuation $v_\ell$ is `New.ellVal`. It is $\infty$ at $0$ and $0$ at elements of norm at least $1$. If $\psi(\sigma_P) = 1$ for some $P$, then the sum is $\infty$ and only $c = \infty$ is allowed.

**Lemma.** If $\mathrm{cyc}(g) = 1$, then the Tate twist $\mathrm{cyc}^{-e}$ is $1$ at $g$, with values in any $\mathbb{Z}_\ell$-algebra.

Lean: `New.Selmer.tateTwist_eq_one_of_cyclotomicChar_eq_one` (New/Congruences/FirstOrder/EvenClasses.lean).

*Proof.* The twist is $\mathrm{cyc}(g)^{-e}$, and $1^{-e} = 1$. $\square$

**Lemma.** Let $(w_j, \tau_j, \varphi_j)$ be a tame generator family of level $\nu$. Then $\mathrm{cyc}^{-1}$ is $1$ on the doubled family of the $\tau_j$, and $\ell^\nu$ divides $\mathrm{cyc}^{-e}(x) - 1$ in $O$ for every $e$ and every $x$ in the doubled family of the $\varphi_j$.

Lean: `New.Selmer.IsTameGeneratorFamily.cyclotomicInv_withConjInv_eq_one_and_dvd` (New/Congruences/FirstOrder/EvenClasses.lean).

*Proof.* The element $\tau_j$ is in an inertia group at a place off $\ell$, where the $\ell$-power roots of unity are unramified. So $\mathrm{cyc}(\tau_j) = 1$. The character $\mathrm{cyc}$ is invariant under $g \mapsto g^c$, so $\mathrm{cyc}((\tau_j^c)^{-1}) = 1$ too. For $\varphi_j$, the element fixes the $\ell^\nu$-th roots of unity, so $\mathrm{cyc}(\varphi_j) \equiv 1$ modulo $\ell^\nu$, and the same holds for $(\varphi_j^c)^{-1}$ and for all powers. $\square$

So all elements of both doubled families act trivially on $(O/\ell^\nu)(-e)$.

### Even parts are even classes

For a cocycle $z$, write $z^c = z \circ \mathrm{conjGal}$, so $z^c(g) = z(cgc)$. The *even part* of $z$ is $z + z^c$ and the *odd part* is $z^c - z$.

**Lemma.** Let $e \neq 0$. Let $z$ be a locally constant cocycle in $(O/\ell^\nu)(-e)$, unramified off $\ell$, $S$ and $\bar S$, that vanishes on the elements of the decomposition groups above $\ell$ with $\mathrm{cyc} = 1$. Then $z + z^c$ is an even class of exponent $e$ for $S$.

Lean: `New.Selmer.add_conjGal_mem_evenClasses` (New/Congruences/FirstOrder/TateTwistCocycles.lean).

*Proof.* The function $z^c$ is a cocycle, because $\mathrm{cyc}(g^c) = \mathrm{cyc}(g)$: so $g$ and $g^c$ act alike on the twist. It is locally constant because $\mathrm{conjGal}$ is continuous. If $g$ is in the inertia group of a place $A$ over $v$, then $g^c$ is in the inertia group of $cA$, which lies over $\bar v$. So $z^c$ is unramified off the same set, because this set is closed under conjugation. In the same way, conjugation by $c$ maps the decomposition groups above $\ell$ to decomposition groups above $\ell$ and keeps $\mathrm{cyc} = 1$, so $z^c$ satisfies the local condition. The sum is invariant under $g \mapsto g^c$ because $c^2 = 1$. $\square$

The hypothesis $e \neq 0$ is needed only to match the local sets. In the source, the local set for exponent $e$ (`New.Selmer.shaLocalSet ℓ E e`) is the union of the inertia groups above $\ell$ if $e = 0$. For $e \neq 0$ it is the set of elements of the decomposition groups above $\ell$ with $\mathrm{cyc} = 1$. Even classes always use the second form.

**Lemma.** Let $(w_j, \tau_j, \varphi_j)$ be a tame generator family of level $\nu$, and let $z$ be a cocycle in $(O/\ell^\nu)(-e)$. Then $z((\tau_j^c)^{-1}) = -z(\tau_j^c)$ and $z((\varphi_j^c)^{-1}) = -z(\varphi_j^c)$.

Lean: `New.Selmer.apply_withConjInv_false_eq_neg` (New/Congruences/FirstOrder/TateTwistCocycles.lean).

*Proof.* For any $g$, the cocycle identity at $g^{-1}g = 1$ gives $0 = z(g^{-1}) + \rho(g^{-1}) z(g)$. If $g$ acts trivially, then $z(g^{-1}) = -z(g)$. By the last lemma, $\tau_j^c$ and $\varphi_j^c$ act trivially. $\square$

So $z$ agrees at $\tau_j$ and $(\tau_j^c)^{-1}$ if and only if $(z + z^c)(\tau_j) = 0$. This is the bridge from the triangle cost, which compares values at $\tau_j$ and $(\tau_j^c)^{-1}$, to even classes.

### The local loss above $\ell$

The next definition is from the later chapter [The main summands of the attached Galois representations](/chapter/main-summands/). It is stated here once, because the file TateTwistCocycles uses it through FittingBlock.

**Definition (Crystalline relations).** For a representation $u$ of $G$ over $O$ and a place $v$ above $\ell$, let $Z_f(v)$ be the module of crystalline cocycles of the decomposition group at the chosen place over $v$, with values in $O^n$ through $u$. The *crystalline relations* of $u$ are the linear relations $\sum_g r_g\, z(g) = 0$ that hold on $Z_f(v)$ for some $v$ above $\ell$, extended by zero from the decomposition group to $G$.

Lean: `New.Selmer.crysRelations` (New/Congruences/LocalLoss/Basic.lean).

Crystalline cocycles are defined with Fontaine's period ring in [period rings](/chapter/period-rings/). The fact used here is from the same chapter. If $\Gamma$ acts on $T$ through $\mathrm{cyc}^{-a}$ with $a \geq 0$, a crystalline cocycle vanishes at every $s$ that acts trivially, provided that $s$ is in inertia when $a = 0$ ([the Bloch-Kato vanishing](/decl/New.Period.crysCocycles.apply_eq_zero_of_cyclotomicGp/)).

**Lemma.** Let $z$ be a cocycle in $(O/\ell^\nu)(-e)$ that obeys the crystalline relations of $O(-e)$. Then $z$ vanishes on the local set of exponent $e$.

Lean: `New.Selmer.apply_eq_zero_of_mem_obeying_crysRelations` (New/Congruences/FirstOrder/TateTwistCocycles.lean).

*Proof.* Let $g$ be in the local set, at a place $A$ above $\ell$. Then $g$ fixes $A$, acts trivially on the twist, and lies in the inertia group of $A$ if $e = 0$. Let $v$ be the place of $E$ under $A$. There is $s \in G$ that moves $A$ to the chosen place over $v$. The element $g' = sgs^{-1}$ has the same three properties at the chosen place. By the Bloch-Kato vanishing, every crystalline cocycle at $v$ vanishes at $g'$. So the single term $[g']$ is a crystalline relation, and $z(g') = 0$. Now compute $z(gs^{-1})$ in two ways. As $gs^{-1} = s^{-1} g'$,
$$z(s^{-1}) = z(s^{-1}) + \rho(s^{-1})\,z(g') = z(gs^{-1}) = z(g) + \rho(g)\,z(s^{-1}) = z(g) + z(s^{-1}).$$
So $z(g) = 0$. $\square$

### Odd classes bound what the triangle leaves

The module $Ш_{\mathrm{odd}}$ of exponent $e$ (`New.Selmer.shaOdd`, from [Building the representations](/chapter/building-representations/)) consists of the locally constant cocycles in $(O/\ell^\nu)(-e)$ that are unramified off $\ell$, vanish on the local set of exponent $e$, and, if $e \neq 0$, satisfy $z(g^c) = -z(g)$. Its length is bounded by [the bound on $Ш_{\mathrm{odd}}$](/chapter/odd-classes/).

For submodules $S$ and $T$, write $\mathrm{len}(S \bmod T)$ for the length of $S/(S \cap T)$ (`New.relLength`, from [Fitting ideals, lengths and coefficient rings](/chapter/fitting-ideals/)).

**Proposition.** Let $(w_j, \tau_j, \varphi_j)$ form a triangle of primes for $g_0$ with bounds $h$ and $c$ and types $\mathrm{ty}$. Let $0 < e < t$. Let $S$ be a module of cocycles in $(O/\ell^\nu)(-e)$ with these properties:

1. each $z \in S$ is unramified off $\ell$ and vanishes on the local set of exponent $e$;
2. $(\mathrm{cyc}(g_0)^{-e} - 1)\, z(g_0) = 0$ for each $z \in S$;
3. $(z + z^c)(\varphi_j) = 0$ for each $z \in S$ and each $j$ with $\mathrm{ty}(j) = e$.

Then $\mathrm{len}(S \bmod S[\ell^h]) \leq \mathrm{len}(Ш_{\mathrm{odd}})$, where $S[\ell^h]$ is the $\ell^h$-torsion.

Lean: `New.Selmer.relLength_torsionBy_le_length_shaOdd` (New/Congruences/FirstOrder/TateTwistCocycles.lean).

*Proof.* Consider the linear map $f(z) = z^c - z$. We show that $f$ maps $S$ into $Ш_{\mathrm{odd}}$ and that its kernel on $S$ lies in $S[\ell^h]$. Then the length of $S$ modulo $S[\ell^h]$ is at most the length of $f(S)$.

Let $z \in S$. By the lemma on even parts, with no extra places, $z + z^c$ is an even class. So $z^c$ vanishes on the local set, as $z^c = (z + z^c) - z$. Also $f(z) = (z + z^c) - z - z$ is unramified off $\ell$, and $f(z)(g^c) = z(g) - z(g^c) = -f(z)(g)$. So $f(z) \in Ш_{\mathrm{odd}}$.

Let $z \in S$ with $f(z) = 0$, that is, $z^c = z$. Let $s$ be the test points of condition 2 of the triangle. For $i \in s$ there is $j$ with $\mathrm{ty}(j) = e$ and $(z + z^c)(\varphi_j) = 2(z + z^c)(i)$, because $z + z^c$ is an even class unramified off $\ell$. So
$$4\,z(i) = 2\,(z + z^c)(i) = (z + z^c)(\varphi_j) = 0$$
by hypothesis 3. Let $d = \mathrm{cyc}(g_0)^{-e} - 1$. The cocycle $4dz$ lies in $S$, vanishes at $g_0$ by hypothesis 2, and vanishes at the test points. By the detection clause of condition 2 of the triangle, $4dz = 0$. By condition 5, $4d^2$ divides $\ell^h$; write $\ell^h = 4d^2 a$. Then $\ell^h z = ad \cdot (4dz) = 0$. $\square$

### The triangle cost of a Tate twist

Recall [the triangle cost](/chapter/ribet-elements/#fitting-ideals-and-the-triangle-cost) (`New.Selmer.HasTriangleCost`). For a module $Z$ of functions, families $\tau, \tau', \varphi, \varphi'$, a set $I$ of indices, $C \in O$ and $b \in [0, \infty]$, it asks for a set $L$ of group elements such that, with $Z_0$ the members of $Z$ that vanish on $L$: (a) for $j \in I$, a $z \in Z_0$ that agrees at $\tau_i, \tau'_i$ for $i < j$ and at $\varphi_i, \varphi'_i$ for $i < j$ in $I$ has $C z(\tau_j) = C z(\tau'_j)$; (b) for each $S \leq Z_0$ whose members vanish at all $\tau_j, \tau'_j$ and agree at $\varphi_j, \varphi'_j$ for $j \in I$, $\mathrm{len}(Z \bmod Z_0) + \mathrm{len}(S \bmod S[C]) \leq b$.

**Theorem (Triangle cost of a Tate twist).** Let $(w_j, \tau_j, \varphi_j)$ form a triangle of primes for $g_0$ with bounds $h$ and $c$ and types $\mathrm{ty}$, and let $e < t$. Let $Z$ be a module of locally constant cocycles in $(O/\ell^\nu)(-e)$, unramified off $\ell$, the $w_j$ and the $\bar w_j$. Suppose that $(\mathrm{cyc}(g_0)^{-e} - 1)\, z(g_0) = 0$ for each $z \in Z$ that is unramified off $\ell$. Let
$$\mathrm{len}(Z \bmod Z_f) + \mathrm{len}(Ш_{\mathrm{odd}}) \leq b,$$
where $Z_f$ is the module of functions that obey the crystalline relations of $O(-e)$. Then $Z$ has triangle cost $b$ for $\tau_j$, $(\tau_j^c)^{-1}$, $\varphi_j$, $(\varphi_j^c)^{-1}$, the set $I = \{j : \mathrm{ty}(j) = e\}$ and $C = \ell^h$.

Lean: `New.Selmer.hasTriangleCost_tateTwist` (New/Congruences/FirstOrder/TateTwistCocycles.lean).

*Proof.* Take $L$ to be the local set of exponent $e$.

For (a), let $j \in I$ and $z \in Z_0$. Then $\mathrm{ty}(j) = e > 0$, so the lemma on even parts gives that $z + z^c$ is an even class of exponent $e$ for the places $w$. By the lemma on inverses, agreement of $z$ at $\tau_i$ and $(\tau_i^c)^{-1}$ means $(z + z^c)(\tau_i) = 0$, and the same holds for $\varphi_i$. So the hypothesis of (a) is the hypothesis of the triangle condition 4 for $z + z^c$. It gives $\ell^h (z + z^c)(\tau_j) = 0$, which is $\ell^h z(\tau_j) = \ell^h z((\tau_j^c)^{-1})$.

For (b), first $\mathrm{len}(Z \bmod Z_0) \leq \mathrm{len}(Z \bmod Z_f)$, because a cocycle that obeys the crystalline relations vanishes on $L$, so $Z \cap Z_f \subseteq Z_0$. Next let $S \leq Z_0$ be as in (b). Its members vanish on the doubled family of the $\tau_j$, so they are unramified off $\ell$ by the lemma on killing tame generators. Here the representation is $\mathrm{cyc}^{-e}$, which is trivial on elements with $\mathrm{cyc} = 1$. If $e = 0$, then $S \subseteq Ш_{\mathrm{odd}}$, as there is no sign condition, and $\mathrm{len}(S \bmod S[\ell^h]) \leq \mathrm{len}(S) \leq \mathrm{len}(Ш_{\mathrm{odd}})$. If $e \neq 0$, apply the proposition. Its hypothesis 2 is the hypothesis on $g_0$. Its hypothesis 3 holds because $z(\varphi_j) = z((\varphi_j^c)^{-1}) = -z(\varphi_j^c)$. Adding the two bounds gives $b$. $\square$

**Example.** Let $t = 2$, so the only positive exponent is $e = 1$, and let $J$ have one element $j$. For $e = 1$ the set $I$ is $\{j\}$. Condition (a) at $j$ has no hypothesis, so it says that $\ell^h z(\tau_j) = \ell^h z((\tau_j^c)^{-1})$ for every $z \in Z_0$. The triangle condition 4 gives exactly this: $\ell^h$ kills the value at $\tau_j$ of every even class of exponent $1$. For $e = 0$ the set $I$ is empty, (a) is empty, and (b) gives the bound $\mathrm{len}(Z \bmod Z_f) + \mathrm{len}(Ш_{\mathrm{odd}})$ with $Ш_{\mathrm{odd}}$ the unramified homomorphisms.
