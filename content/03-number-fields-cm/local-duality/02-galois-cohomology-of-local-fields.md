---
title: Galois cohomology of local fields
lean:
  - Lib/ClassField/Places/GaloisDefs.lean
  - Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean
  - Lib/ClassField/GaloisCohomology/TateIndexFormula.lean
  - Lib/ClassField/LocalDuality/KummerFiniteness.lean
  - Lib/ClassField/Local/InvariantMap.lean
decls:
  - New.IsLocalGalois
  - New.Z1
  - New.cokerKerIndex
  - New.cokerKerIndex_local_units
  - New.exists_root_near_one
  - New.IsLocalGalois.card_kummer_cocycles
  - New.IsLocalGalois.card_ker_natCast_Z1_unitsModule
  - New.IsLocalGalois.finite_Z1
  - New.IsLocalGalois.classOfInvariant_bijective
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Galois cohomology of local fields

This section gives the classical facts on the Galois cohomology of a local field that the rest of the chapter needs. Then it gives the setting of the source, its 1-cocycles, and its count of Kummer cocycles. The source counts cocycles, not classes, and it proves its count from Hilbert 90 and an estimate for roots near $1$, not from the Euler characteristic formula.

### The classical theory

Let $k$ be a finite extension of $\mathbb{Q}_p$, let $\bar k$ be an algebraic closure and let $G_k = \mathrm{Gal}(\bar k/k)$. A *discrete $G_k$-module* is an abelian group $M$ with an action of $G_k$ such that the stabiliser of each element is open. For such $M$ the groups $H^i(k, M)$ are the cohomology groups of the complex of continuous cochains. In degree $1$, a continuous map $f : G_k \to M$ is a *1-cocycle* if $f(gh) = f(g) + g f(h)$ for all $g, h$. It is a *1-coboundary* if $f(g) = g m - m$ for some $m \in M$. Then $H^1(k, M) = Z^1(k, M)/B^1(k, M)$.

The classical facts are the following. The references are Serre, *Galois Cohomology*, Chapter II, §5, and Milne, *Arithmetic Duality Theorems*, second edition, Chapter I, §2.

1. *Hilbert 90.* $H^1(k, \bar k^\times) = 0$. This holds for every field and its separable closure (Serre, *Local Fields*, Chapter X, §1).
2. *Kummer theory.* For $n \geq 1$ the sequence $1 \to \mu_n \to \bar k^\times \to \bar k^\times \to 1$, with the map $x \mapsto x^n$, is exact. With Hilbert 90 it gives $H^1(k, \mu_n) \cong k^\times/k^{\times n}$.
3. *The index of $n$-th powers.* $[k^\times : k^{\times n}] = n \cdot \#\mu_n(k) \cdot \#(\mathcal{O}/n\mathcal{O})$, where $\mathcal{O}$ is the ring of integers of $k$. If $p \nmid n$, then $\#(\mathcal{O}/n) = 1$. If $n = p$, then $\#(\mathcal{O}/p) = p^{[k:\mathbb{Q}_p]}$ (Neukirch, *Algebraic Number Theory*, Chapter II, §5).
4. *The Brauer group.* The invariant map gives an isomorphism $H^2(k, \bar k^\times) \cong \mathbb{Q}/\mathbb{Z}$ (Serre, "Local class field theory", Chapter VI of Cassels and Fröhlich, *Algebraic Number Theory*, §1).
5. *Finiteness.* For a finite $M$, the groups $H^i(k, M)$ are finite for all $i$, and they are zero for $i \geq 3$ (Serre, *Galois Cohomology*, II.5.2).

From facts 2 and 3 one can count cocycles, not only classes. The group $B^1(k, \mu_n)$ is the image of $\mu_n(\bar k)$ under $m \mapsto (g \mapsto g m / m)$, and its kernel is $\mu_n(k)$. So $\#B^1(k, \mu_n) = n/\#\mu_n(k)$, and

$$\#Z^1(k, \mu_n) = \#H^1(k, \mu_n) \cdot \#B^1(k, \mu_n) = n \cdot \#\mu_n(k) \cdot \#(\mathcal{O}/n) \cdot \frac{n}{\#\mu_n(k)} = n^2 \cdot \#(\mathcal{O}/n).$$

The factor $\#\mu_n(k)$ cancels. This is the form in which the source states Kummer theory.

### The setting of the source

The source does not use $\mathbb{Q}_p$ or a completion. It fixes an algebraically closed field $\Omega$ of characteristic $0$, a field $k$ with an algebra map to $\Omega$, and a profinite group $\Gamma$ that acts on $\Omega$ as the Galois group of $\Omega$ over $k$.

**Definition (Local Galois setting).** Let $A$ be a valuation subring of $\Omega$. The class `IsLocalGalois Γ k A` says four things. (a) $\Gamma$ is the Galois group of $\Omega$ over $k$ (`IsProGalois`), and $\Omega$ is algebraically closed of characteristic $0$. (b) Every $g \in \Gamma$ maps $A$ to itself. (c) The valuation ring $\mathcal{O} = A \cap k$ of $k$ is a discrete valuation ring. (d) The residue field of $\mathcal{O}$ is finite.

Lean: `New.IsLocalGalois` (Lib/ClassField/Places/GaloisDefs.lean).

Condition (b) says that $A$ is the only extension of the valuation of $k$ to $\Omega$, so $k$ is henselian. The field $k$ need not be complete. For example the algebraic numbers in $\mathbb{Q}_p$ form such a field. This is the form of a local field that the source uses everywhere. It lets the source treat the completion of a number field at a place inside one fixed algebraic closure of $\mathbb{Q}$. The chapter [CM fields, towers and places](/chapter/cm-fields/) shows how the places and the decomposition groups are set up.

**Definition (Continuous 1-cocycles).** For a representation $\rho$ of a topological group $G$ on a topological module $M$, `Z1 ρ` is the submodule of the maps $f : G \to M$ that are continuous and satisfy $f(gh) = f(g) + \rho(g) f(h)$.

Lean: `New.Z1` (Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean).

The source works with `Z1` in most statements of this chapter. It writes $\Omega^\times$ additively as `DiscreteUnits Ω`, with the discrete topology, and `unitsModule Γ` is $\Omega^\times$ as a discrete $\Gamma$-module.

**Definition (Index of an endomorphism).** For a linear map $f : A \to B$ of abelian groups, `cokerKerIndex f` is the rational number $\#\mathrm{coker}(f)/\#\ker(f)$. It is $0$ if one of the two groups is infinite.

Lean: `New.cokerKerIndex` (Lib/ClassField/GaloisCohomology/TateIndexFormula.lean).

This index is the Herbrand quotient of a single map. It is multiplicative along short exact sequences when the map commutes with the sequence. The chapter [Class field theory on finite ideles](/chapter/class-field-theory/) uses it for the Tate index formula.

### The index of $l$-th powers

**Lemma (Index of $l$-th powers).** Let `IsLocalGalois Γ L A` hold, let $l \neq 0$ and let $Y$ be an additive group with an isomorphism $Y \cong L^\times$. For multiplication by $l$ on $Y$: (a) the index $\#(Y/lY)/\#Y[l]$ is not $0$, so both groups are finite; (b) it is equal to $l \cdot \#(\mathcal{O}/l\mathcal{O})$.

Lean: `New.cokerKerIndex_local_units` (Lib/ClassField/LocalDuality/KummerFiniteness.lean).

Since $Y[l] = \mu_l(L)$, this is fact 3 above in the form $[L^\times : L^{\times l}]/\#\mu_l(L) = l \cdot \#(\mathcal{O}/l)$.

*Proof.* The source's proof has three steps. First, the index is multiplicative in the exact sequence $1 \to \mathcal{O}^\times \to L^\times \to \mathbb{Z} \to 0$ given by the valuation, and on $\mathbb{Z}$ it is $l$. Second, $\mathcal{O}^\times$ can be replaced by the subgroup $V = 1 + l\pi\mathcal{O}$ of finite index, where $\pi$ is a uniformiser, since the index of a map on a finite group is $1$. Third, on $V$ the map $x \mapsto x^l$ is injective, and $a \mapsto (a-1)/(l\pi)$ identifies its cokernel with $\mathcal{O}/l$. The second and third steps need roots of elements near $1$. The source gets them in $\Omega$ from `New.exists_root_near_one`, which plays the part of Hensel's lemma. $\square$

**Lemma (Roots near one).** Let $A$ be a valuation subring of an algebraically closed field $\Omega$, with absolute value $|x|$ given by the valuation of $A$. Let $l$ be a natural number and $r \neq 0$. If $|a - 1| \leq |l| \cdot r$, then $a = z^l$ for some $z$ with $|z - 1| \leq r$.

Lean: `New.exists_root_near_one` (Lib/ClassField/LocalDuality/KummerFiniteness.lean).

The source's proof does not use a Newton iteration. It looks at the polynomial $a - X^l$. Its logarithmic derivative at $1$ is $-l/(a-1)$, and this is the sum of $1/(1-z)$ over the roots $z$. If every root is far from $1$, then every term is small, and the sum cannot have the size of $l/(a-1)$.

### The count of Kummer cocycles

**Theorem (Kummer cocycles).** Let `IsLocalGalois Γ k A` hold and let $n \neq 0$. Let $c$ be the number of continuous 1-cocycles $\Gamma \to \Omega^\times$ that are killed by $n$, that is, with values in $\mu_n$. Then (a) $0 < c$, so the group is finite; (b) $c = n^2 \cdot \#(\mathcal{O}/n\mathcal{O})$.

Lean: `New.IsLocalGalois.card_kummer_cocycles` (Lib/ClassField/LocalDuality/KummerFiniteness.lean).

The group in the statement is the kernel of multiplication by $n$ on $Z^1(\Gamma, \Omega^\times)$. A cocycle $f$ with $n f = 0$ has values in $\mu_n$, so this kernel is $Z^1(\Gamma, \mu_n)$. The count agrees with the classical count above.

*Proof.* By Hilbert 90 for $\Omega^\times$, the coboundary map $\Omega^\times \to Z^1(\Gamma, \Omega^\times)$ is onto. Its kernel is the group $k^\times$ of invariants. So the sequence $1 \to k^\times \to \Omega^\times \to Z^1(\Gamma, \Omega^\times) \to 1$ is exact. The index of multiplication by $n$ is multiplicative along it. On $\Omega^\times$ multiplication by $n$ is onto with kernel $\mu_n$, so its index is $1/n$. On $k^\times$ the index is $n \cdot \#(\mathcal{O}/n)$ by `New.cokerKerIndex_local_units`. So the index on $Z^1$ is $1/(n \cdot n \cdot \#(\mathcal{O}/n))$. The group $Z^1(\Gamma, \Omega^\times)$ is divisible, because it is a quotient of $\Omega^\times$, so the cokernel is trivial. So the kernel has $n^2 \cdot \#(\mathcal{O}/n)$ elements. $\square$

This proof does not use the Euler characteristic formula. It is a variant of Kummer theory that counts cocycles.

**Corollary (Kummer cocycles, the count).** Under the same hypotheses, the kernel of $n$ on $Z^1(\Gamma, \Omega^\times)$ has $n^2 \cdot \#(\mathcal{O}/n)$ elements.

Lean: `New.IsLocalGalois.card_ker_natCast_Z1_unitsModule` (Lib/ClassField/LocalDuality/KummerFiniteness.lean).

**Corollary (Finiteness of 1-cocycles).** Let `IsLocalGalois Γ k A` hold and let $M$ be a finite discrete $\Gamma$-module over a commutative ring. Then $Z^1(\Gamma, M)$ is finite.

Lean: `New.IsLocalGalois.finite_Z1` (Lib/ClassField/LocalDuality/KummerFiniteness.lean).

*Proof.* Take an open normal subgroup $U$ that acts trivially on $M$ and on $\mathrm{Hom}(M, \Omega^\times)$. A cocycle $z$ is fixed by its values on a set of representatives of $\Gamma/U$ and by the cocycles $f \circ z$ of $U$ in $\Omega^\times$, for $f \in \mathrm{Hom}(M, \Omega^\times)$. These are killed by $\#M$. The fixed field of $U$ is again local, so the count of Kummer cocycles over it leaves finitely many of them. $\square$

This is the finiteness of $H^1$ for a finite module, fact 5, in degree $1$ and for cocycles.

### The Brauer group

**Theorem (The invariant map).** Let `IsLocalGalois Γ k A` hold. The map `classOfInvariant` from $\mathbb{Q}/\mathbb{Z}$ to $H^2(\Gamma, \Omega^\times)$ is bijective.

Lean: `New.IsLocalGalois.classOfInvariant_bijective` (Lib/ClassField/Local/InvariantMap.lean).

This is fact 4, stated for the inverse of the invariant map and for a henselian $k$. The chapter [Class field theory on finite ideles](/chapter/class-field-theory/) treats its proof. In this chapter it gives the target of the cup product: for a finite $M$, the cup product of a cocycle with values in $M^\vee = \mathrm{Hom}(M, \Omega^\times)$ and a cocycle with values in $M$ is a class in $H^2(\Gamma, \Omega^\times)$, so an element of $\mathbb{Q}/\mathbb{Z}$.

**Remark (Formalization).** Three points separate the source from the textbook. First, the local field is henselian and not complete, and it sits inside one algebraically closed $\Omega$. All counts of the source hold in this setting. Second, the counts are for $Z^1$, not for $H^1$. The two differ by the factor $\#B^1(M) = \#M/\#M^\Gamma$. The source carries this factor through all of its statements, and this is why the exponent $2 + d$ appears in the next section. Third, the source proves the count of Kummer cocycles from Hilbert 90 and the estimate for roots near $1$ alone. It does not prove the finiteness of $H^2$ or the vanishing of $H^i$ for $i \geq 3$, and it does not need them in these files.
