---
title: Albert, Brauer, Hasse and Noether
lean:
  - Lib/ClassField/Global/AlbertBrauerHasseNoether.lean
  - Lib/ClassField/Local/ArtinMap.lean
  - Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean
decls:
  - New.IsComplexConj.mul_self
  - New.IsTotallyPositive.exists_resH2_cyclicClass_eq_zero
  - New.IsPlaceOver.abelianLift_artinAt_principal
  - New.cyclicClass_eq_zero_iff_norm
  - New.relIndex_norm_unit_pow
  - New.exists_map_norm_eq_of_abelianLift_artinAt_eq_one
  - New.albert_brauer_hasse_noether
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Albert, Brauer, Hasse and Noether

This section and the next prove the global theorems that rest on the second inequality of Section 5. The order of the proofs is the order of the source. Hasse's norm theorem in prime degree comes first, and then the local-global principle for the Brauer group. Section 7 proves reciprocity by Artin's method and then the norm theorems.

Fix a number field $K$, embedded in $\Omega$, and a group $\Gamma$ with `IsProGalois Γ K Ω`. For a character $\chi$ of $\Gamma$ with values in $\mathbb{Q}/\mathbb{Z}$ and $x \in K^\times$, write $(\chi, x) \in H^2(\Gamma, \Omega^\times)$ for the symbol `cyclicClass (unitsModule Γ).ρ χ (DiscreteUnits.ofBase Γ Ω (.ofMul x))` of Section 4. Write $\operatorname{res}_U$ for `(unitsModule Γ).resH2 U`.

### The textbook statements

The theorem of Albert, Brauer, Hasse and Noether says that the sequence
$$0 \to \operatorname{Br}(K) \to \bigoplus_v \operatorname{Br}(K_v) \xrightarrow{\ \sum \operatorname{inv}_v\ } \mathbb{Q}/\mathbb{Z} \to 0$$
is exact, where $v$ runs over all places, finite and infinite. Injectivity on the left is the local-global principle: a central simple algebra over $K$ that splits at every place splits. Hasse's norm theorem says that for a cyclic extension $L/K$, an element of $K^\times$ is a norm from $L^\times$ if and only if it is a norm from $L_w^\times$ at every place $v$, with $w$ over $v$. The source cites Milne, *Class Field Theory* (version 4.03, 2020), Chapters VII and VIII, and Tate, *Global class field theory*, Chapter VII of Cassels and Fröhlich, for these results. It cites H. Hasse, *Die Struktur der R. Brauerschen Algebrenklassengruppe*, Math. Ann. 107 (1933), for the method that gets reciprocity from the sum formula.

In both textbook statements the infinite places are local conditions of the same kind as the finite places. The source has no components at the infinite places. It replaces each condition at the real places by a condition on complex conjugations or by total positivity.

### Symbols at the real places

An element $c \in \Gamma$ is a complex conjugation (`New.IsComplexConj`, Section 3) if it acts as complex conjugation under some embedding of $\Omega$ in $\mathbb{C}$.

**Lemma (Conjugations are involutions).** If $c$ is a complex conjugation, then $c^2 = 1$.
Lean: `New.IsComplexConj.mul_self` (Lib/ClassField/Global/AlbertBrauerHasseNoether.lean).

*Proof.* Under the embedding $j$, the element $c^2$ acts on $j(\Omega)$ as the square of complex conjugation, which is the identity. The action of $\Gamma$ on $\Omega$ is faithful, so $c^2 = 1$. $\square$

**Lemma (Totally positive symbols).** Let $\chi$ be a character of $\Gamma$ and let $x \in K^\times$ be totally positive. Then there is an open subgroup $U$ of $\Gamma$ such that every complex conjugation lies in $U$ and $\operatorname{res}_U (\chi, x) = 0$.
Lean: `New.IsTotallyPositive.exists_resH2_cyclicClass_eq_zero` (Lib/ClassField/Global/AlbertBrauerHasseNoether.lean).

*Proof.* Take $y \in \Omega^\times$ with $y^2 = x$. Let $U$ be the intersection of the stabiliser of $y$ with the kernel of $2\chi$. It is open. On $U$ the symbol $(\chi, x) = (\chi, y^2)$ is $(2\chi, y)$, and both $2\chi$ and the action on $y$ are trivial on $U$, so the restriction is zero. Let $c$ be a complex conjugation for the embedding $j$. Then $j(y)$ is a square root of a positive real number $j(x)$, so $j(y)$ is real and $c$ fixes $y$. Also $2\chi(c) = \chi(c^2) = 0$ by the previous lemma. So $c \in U$. $\square$

The open subgroup $U$ cuts out a finite extension $F$ of $K$ in which every real place of $K$ stays real. This is the form in which the source states every condition at the real places.

### The local symbol is minus the local invariant

The link between symbols and the Artin map is one lemma of the local theory.

**Lemma (Local symbol and invariant).** Let $A$ lie over the finite place $w$ of $K$, let $\chi$ be a character of $\Gamma$, and let $x \in K^\times$. Let $D$ be the decomposition group of $A$ and let $\iota_D$ be the map `classOfInvariant D (fixedFieldOf D) A` from $\mathbb{Q}/\mathbb{Z}$ to $H^2(D, \Omega^\times)$ of Section 4. Then
$$\iota_D\big(\chi(\operatorname{artinAt}_w(x))\big) = -\operatorname{res}_D (\chi, x).$$
Lean: `New.IsPlaceOver.abelianLift_artinAt_principal` (Lib/ClassField/Local/ArtinMap.lean).

Since $\iota_D$ is a bijection (`New.IsLocalGalois.classOfInvariant_bijective`, Section 4), the local symbol $\chi(\operatorname{artinAt}_w(x))$ is trivial if and only if $(\chi, x)$ dies on $D$. The sign comes from the geometric convention of the source. With the arithmetic convention of Serre, *Local Fields*, Chapter XIV, the sign is $+$.

The second link is the norm criterion for cyclic symbols.

**Lemma (Symbols and norms).** Let $L/K$ be finite, and let $\chi$ be a character of $\Gamma$ whose kernel acts on $\Omega$ as the Galois group of $\Omega/L$. Then for $x \in K^\times$, the symbol $(\chi, x)$ is $0$ if and only if $x = N_{L/K}(z)$ for some $z \in L^\times$.
Lean: `New.cyclicClass_eq_zero_iff_norm` (Lib/ClassField/GaloisCohomology/KummerCyclicClasses.lean).

This is the explicit form of the textbook isomorphism $H^2(\operatorname{Gal}(L/K), L^\times) \cong K^\times / N L^\times$ for cyclic $L/K$, together with inflation into $H^2(\Gamma, \Omega^\times)$.

### Hasse's norm theorem in prime degree

The first global theorem is Hasse's theorem for an extension of prime degree in which no real place ramifies.

**Lemma (Norm index of S-units).** Let $L/K$ be Galois of prime degree $l$. Let $S$ be a finite set of finite places of $K$ that contains every place that ramifies in $L$, and such that the principal ideles and the ideles that are units off $S$ generate all finite ideles. Let $T$ be the set of places of $L$ over $S$. Write $E_S$ and $E_T$ for the $S$-units and $T$-units, and $r_K$, $r_L$ for the numbers of infinite places. Then
$$\big([E_S : N E_T] \cdot l\big)^{l-1} \cdot l^{\#T + r_L} = (l^l)^{\#S + r_K}.$$
Lean: `New.relIndex_norm_unit_pow` (Lib/ClassField/Global/AlbertBrauerHasseNoether.lean).

*Proof sketch.* By Dirichlet's unit theorem, $E_S$ has rank $\#S + r_K - 1$ and $E_T$ has rank $\#T + r_L - 1$. Tate's index formula (Section 4) for the cyclic group $\operatorname{Gal}(L/K)$ acting on $E_T$ then gives the norm index. The indices $\#(A / lA) / \#A[l]$ that occur in it are $l^{\operatorname{rank} A}$, so they are known from the ranks. Off $S$ there is no ramification, so the valuations of $L$ extend those of $K$, and the $T$-units that have a norm in $E_S$ are controlled. $\square$

**Theorem (Hasse, prime degree).** Let $L/K$ be Galois of prime degree, with $\ker \chi$ acting as the Galois group of $\Omega/L$. Suppose that $\chi$ kills every complex conjugation. Let $x \in K^\times$ have $\chi(\operatorname{artinAt}_v(x)) = 1$ at every finite place $v$. Then $x = N_{L/K}(z)$ for some $z \in L^\times$.
Lean: `New.exists_map_norm_eq_of_abelianLift_artinAt_eq_one` (Lib/ClassField/Global/AlbertBrauerHasseNoether.lean).

*Proof.* Take $S$ large: it contains the ramified places, the support of $x$, the places needed to represent the ideal classes of $L$ by norms, and generators of the class group of $K$. Let $\tau$ be the tuple of local symbols $v \mapsto \chi(\operatorname{artinAt}_v(\cdot))$ for $v \in S$. Among the $S$-units, the norms from $E_T$ lie in the kernel of $\tau$. The second inequality (Section 5), applied to the open group $W = K^\times (\ker \tau \cap U_S)$, and the local count of the image of each local symbol, show that the kernel of $\tau$ on $E_S$ has the same index as $N E_T$. So the two groups are equal. The element $x$ is an $S$-unit in the kernel of $\tau$, so it is a norm. $\square$

The hypothesis that $\chi$ kills the complex conjugations says that every real place of $K$ stays real in $L$. Then every element is a local norm at the real places, so the theorem has the textbook hypotheses at all places.

### Albert, Brauer, Hasse and Noether

**Theorem (Albert, Brauer, Hasse, Noether).** Let $\alpha \in H^2(\Gamma, \Omega^\times)$. Suppose that $\operatorname{res}_{D_A} \alpha = 0$ for the decomposition group $D_A$ of every place $A$ of $\Omega$ over a finite place of $K$. Suppose that there is an open subgroup $U$ of $\Gamma$ that contains every complex conjugation, with $\operatorname{res}_U \alpha = 0$. Then $\alpha = 0$.
Lean: `New.albert_brauer_hasse_noether` (Lib/ClassField/Global/AlbertBrauerHasseNoether.lean).

*Proof.* First reduce to the case where $U$ is normal of prime index. The class $\alpha$ dies on the normal core of $U$. Climb from the core to $\Gamma$ in steps $V \leq U'$ of prime index, and apply the reduced case over the fixed field of $U'$ at each step. The hypotheses pass to each step, since the decomposition groups of $U'$ are intersections with those of $\Gamma$, and a conjugate of a complex conjugation is a complex conjugation. Now let $U$ be normal of prime index. Then $U$ is the kernel of a character $\chi$, and $\alpha$ dies on $\ker \chi$. So $\alpha = (\chi, x)$ for some $x \in K^\times$ (`New.cyclicClass_spec`). The local hypothesis and the lemma on local symbols give $\chi(\operatorname{artinAt}_v(x)) = 1$ for all $v$. The group $U$ contains the complex conjugations, so $\chi$ kills them. By Hasse's theorem in prime degree, $x$ is a norm from the fixed field of $U$. By the norm criterion, $\alpha = (\chi, x) = 0$. $\square$

**Remark (Formalization).** The textbook hypothesis at a real place $v$ is that $\alpha$ dies on the decomposition group $\{1, c_v\}$. The source asks for one open subgroup $U$ that contains all complex conjugations, with $\alpha$ zero on $U$. This hypothesis implies the textbook one, since each $\{1, c\}$ lies in $U$. As a hypothesis it is stronger: it asks for a finite splitting field of $\alpha$ in which the real places stay real. By the textbook theorem the two are equivalent after the fact, but the source does not prove this. The source does not state the exact sequence, the sum formula, or the injectivity into the full direct sum. For a totally complex $K$ there are no complex conjugations in $\Gamma$ (`New.IsComplexConj.false_of_isTotallyComplex`), and the hypothesis says only that $\alpha$ dies on some open subgroup. The argument needs no more, because every application has such a $U$ at hand: the kernel of a character that kills the conjugations, or the group of the lemma on totally positive symbols.
