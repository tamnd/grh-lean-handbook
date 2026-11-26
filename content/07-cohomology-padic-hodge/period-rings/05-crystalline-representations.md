---
title: Crystalline representations
lean:
  - Lib/PadicHodge/Crystalline/Basic.lean
  - Lib/PadicHodge/Crystalline/Regularity.lean
  - Lib/PadicHodge/Crystalline/FixedRatios.lean
decls:
  - New.Period.OverGp
  - New.Period.tensorAction
  - New.Period.fixedPeriods
  - New.Period.IsAdmissible
  - New.Period.IsCrystalline
  - New.Period.nearOne
  - New.Period.Dpcris
  - New.Period.IsPotentiallyCrystalline
  - New.Period.crysCocycles
  - New.Period.IsAdmissible.tate_twist
  - New.Period.isAdmissible_of_cyclotomicGp_zpow
  - New.Period.Bmax.exists_witt_ratio
  - New.Period.fontaine_regularity
  - New.Period.IsAdmissible.exists_basis
  - New.Period.IsAdmissible.of_jointly_injective
  - New.Period.IsAdmissible.of_bilinear
  - New.Period.IsAdmissible.of_pairing
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Crystalline representations

This section defines admissible, crystalline and potentially crystalline representations with the ring $B_{\max}$ of Section 4. It proves Fontaine's computation of fixed fractions, that the fixed periods contain a basis, and stability under the usual operations. The source cites J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, Sections 1 and 5, and O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), Sections 5.2 and 9.

### The setting

The source does not fix a field $K$. It fixes a group $\Gamma$ with a homomorphism $j : \Gamma \to G_p$ with open image (the class `OverGp`). The main example is $\Gamma = G_K$ with the inclusion.

Lean: `New.Period.OverGp` (Lib/PadicHodge/Crystalline/Basic.lean).

Let $R$ be a $\mathbb{Z}_p$-algebra, $T$ an $R$-module and $\rho : \Gamma \to \mathrm{GL}_R(T)$ a representation. For a ring $B$ with an action of $G_p$, the group $\Gamma$ acts on $B \otimes_{\mathbb{Z}_p} T$ by $g \mapsto j(g) \otimes \rho(g)$. For a filter $F$ on $\Gamma$, the *fixed periods along $F$* are the $y \in B \otimes T$ such that $(j(g) \otimes \rho(g))\,y = y$ for $F$-almost all $g$.

Lean: `New.Period.tensorAction` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.fixedPeriods`.

Two filters are used. The top filter $\top$ asks that $y$ is fixed by every $g$. The filter $\mathrm{nearOne}$ is the pull-back along $j$ of the neighbourhoods of $1$ in $G_p$, so an element is fixed along it when it is fixed by the preimage of some open subgroup, which the source does not choose.

Lean: `New.Period.nearOne` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.eventually_nearOne_apply_eq`.

**Definition (Admissible, crystalline).** The representation $\rho$ is *admissible along $F$* if the fixed periods along $F$ in $B_{\max} \otimes_{\mathbb{Z}_p} T$ span it as a $B_{\max}$-module. It is *crystalline* if it is admissible along $\top$, and *potentially crystalline* if it is admissible along $\mathrm{nearOne}$. The set $D_{\mathrm{pcris}}(\rho)$ is the set of fixed periods along $\mathrm{nearOne}$.

Lean: `New.Period.IsAdmissible` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.IsCrystalline`, `New.Period.IsPotentiallyCrystalline`, `New.Period.Dpcris`.

In the classical theory (Fontaine, Astérisque 223, Exposé III, Section 5), $V$ is a finite-dimensional continuous $\mathbb{Q}_p$-representation of $G_K$, and $V$ is crystalline if $\dim_{K_0} (B_{\mathrm{cris}} \otimes_{\mathbb{Q}_p} V)^{G_K} = \dim_{\mathbb{Q}_p} V$. Since $B_{\mathrm{cris}}$ is regular, this is equivalent to the statement that the invariants span $B_{\mathrm{cris}} \otimes V$. The source takes the span condition as the definition. Potentially crystalline classically means crystalline on $G_L$ for a finite extension $L$ of $K$. Along $\mathrm{nearOne}$, the open subgroup can depend on the element, but when finitely many elements span, one open subgroup fixes all of them.

**Remark (Formalization).** The definition has no hypotheses on $T$ and $\rho$. There is no continuity, no finiteness and no freeness. The tensor product is over $\mathbb{Z}_p$, not over $R$. These choices have consequences.

1. If $T$ is killed by a power of $p$, then $B_{\max} \otimes_{\mathbb{Z}_p} T = 0$, since $p$ is a unit in $B_{\max}$. So every torsion representation is crystalline, by the definition. The source uses the notion only for lattices and for modules over $\mathbb{Q}_p$-algebras, where this effect does not occur.
2. A representation that is not continuous can be admissible. The definition does not see the topology of $T$. In the uses in Volume 12, the representations are continuous, and the hypothesis is carried by the context.
3. Because the tensor product is over $\mathbb{Z}_p$, for $R$ a finite extension of $\mathbb{Q}_p$ the module $B_{\max} \otimes_{\mathbb{Z}_p} T$ is $B_{\max} \otimes_{\mathbb{Q}_p} T$, the module of the classical theory for the underlying $\mathbb{Q}_p$-representation. The $R$-structure is extra, and it acts through `coeffEnd` below.

The register records the replacement of $B_{\mathrm{cris}}$ by $B_{\max}$ as F-056, in [definitions weaker than the textbook](/chapter/register-of-findings/).

**Definition (Crystalline cocycles).** $Z_f(\rho)$ is the $R$-submodule of maps $c : \Gamma \to T$ for which there is $y \in B_{\max} \otimes T$ with $1 \otimes c(g) = (j(g) \otimes \rho(g))\,y - y$ for every $g \in \Gamma$.

Lean: `New.Period.crysCocycles` (Lib/PadicHodge/Crystalline/Basic.lean).

For $T$ free over $\mathbb{Z}_p$, a map in $Z_f(\rho)$ is a cocycle (Section 8). The source does not ask for continuity. Classically (Bloch-Kato, *L-functions and Tamagawa numbers of motives*, Grothendieck Festschrift I (1990), Section 3), $H^1_f(K, V)$ is the kernel of $H^1(K, V) \to H^1(K, B_{\mathrm{cris}} \otimes V)$, and $Z_f$ is the module of cocycles whose classes lie in it.

### Two first examples

**Theorem (Tate twists).** Let $c \in \mathbb{Z}$ and let $\sigma = \chi^c \rho$, that is, $\sigma(g)x = \chi(g)^c\rho(g)x$. If $\rho$ is admissible along $F$, then so is $\sigma$. If $\Gamma$ acts on $T$ by $\chi^c$, then $\rho$ is admissible along every filter.

Lean: `New.Period.IsAdmissible.tate_twist` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.isAdmissible_of_cyclotomicGp_zpow`, `New.Period.exists_tate_twist_unit`.

*Proof.* The period $t$ of Section 4 is $p\mu$ times a unit, so it is a unit of $B_{\max}$. Put $u = t^{-c}$. Then $(j(g) \otimes \sigma(g))(uy) = u\,(j(g) \otimes \rho(g))(y)$, so multiplication by $u$ maps the fixed periods of $\rho$ onto those of $\sigma$. For the second claim, the trivial representation is admissible along every filter. $\square$

Since $\varphi(t) = pt$, the pair $(\varphi^n, j(g))$ acts on $u$ by $p^{-nc}\chi(g)^{-c}$. This factor gives the Frobenius operator of a Tate twist in Section 6. The proof needs that $t$ is a unit, so it needs that $B_{\max}$ inverts $\mu$.

### Fixed fractions

The core input is Fontaine's computation of the invariants of the fraction field. Classically (Brinon-Conrad, Section 9.1), $\mathrm{Frac}(B_{\mathrm{cris}})^{G_K} = K_0$, the maximal unramified subextension of $K$. The source proves a version for one fraction and an open subgroup that it does not choose.

**Theorem (Fixed fractions).** Let $a, b \in B_{\max}$ with $b \neq 0$. Suppose that $b \cdot g(a) = g(b) \cdot a$ for all $g$ in some neighbourhood of $1$ in $G_p$. Then there are $f \geq 1$, $n \geq 0$ and $w \in W(\mathbb{F}_{p^f})$ with $p^n a = w b$.

Lean: `New.Period.Bmax.exists_witt_ratio` (Lib/PadicHodge/Crystalline/FixedRatios.lean).

So $a/b$ lies in $W(\mathbb{F}_{p^f})[1/p]$, the field $K_0$ for some unramified $K_0$. Here $W(\mathbb{F}_{p^f})$ is the Witt ring of $\{x \in O^\flat : x^{p^f} = x\}$, a subring of $A_{\inf}$.

*Proof.* The relation holds on an open subgroup $U$ with fixed field $L$. The source takes a *Kummer chart* for $U$: a Teichmüller element $z \in A_{\inf}$ with $\theta(z)$ a uniformizer of $L$, with an Eisenstein polynomial over $W(\mathbb{F}_{p^f})$. The chart is built in [Kisin frames and limits](/chapter/kisin-frames/). By the invariants of $B_{\mathrm{dR}}$ (Section 4), $a/b = \lambda \in L$. Expand $a$ and $b$ in the coordinates of the chart, cancel the largest power of $z$ in a nonzero coordinate of $b$, and reduce modulo $z$. This gives $\lambda w_1 = w_0$ with $w_0, w_1 \in W(\mathbb{F}_{p^f})$ and $w_1 \neq 0$, up to a power of $p$. $\square$

**Remark (Formalization).** The degree $f$ and the exponent $n$ are existential and not specified. The theorem does not say that $f$ is the residue degree of the fixed field of $U$, though the proof gives this. Only the containment $a/b \in W(\mathbb{F}_{p^f})[1/p]$ is used later. The proof depends on `New.Lift.exists_kummerChart` (Lib/PadicHodge/Kisin/KummerChartExistence.lean), which comes after this file in the reading order of the source and before it in the import order. The chapter uses the result here and leaves its proof to the next chapter.

### Regularity and bases

Fontaine calls a ring $B$ with an action of $G$ *regular* when $B$ is a domain, $B^G = \mathrm{Frac}(B)^G$, and every $b \neq 0$ with $\mathbb{Q}_p b$ stable is a unit (Fontaine, Astérisque 223, Exposé III, Section 1). The source proves the form that it needs.

**Theorem (Regularity).** Let $\mathrm{nearOne} \leq F$. Let $w : \iota \to B_{\max}$ be finitely supported and let $b \in B_{\max}$ be nonzero. If $b \cdot g(w) = g(b) \cdot w$ for $F$-almost all $g$, with $g$ acting through $j$ on each coordinate, then $w = b\,a$ for some finitely supported $a$ that is fixed by $F$-almost all $g$.

Lean: `New.Period.fontaine_regularity` (Lib/PadicHodge/Crystalline/Regularity.lean).

*Proof.* For each $i$, fixed fractions give $p^n w_i = c\,b$ with $c$ a Witt vector, so $w = b\,a$. The relation reads $b \cdot g(b)\,g(a) = g(b) \cdot b\, a$ in the domain $B_{\max}$, so $g(a) = a$. $\square$

The theorem says that a fixed fraction of elements of $B_{\max}$ is a fixed element of $B_{\max}$. It does not say that the units condition of Fontaine holds. The source does not need it in that form.

**Theorem (Fixed bases).** Let $\mathrm{nearOne} \leq F$ and let $\rho$ be admissible along $F$. Then $B_{\max} \otimes T$ has a $B_{\max}$-basis whose elements are fixed periods along $F$.

Lean: `New.Period.IsAdmissible.exists_basis` (Lib/PadicHodge/Crystalline/Regularity.lean).

*Proof.* Take a maximal $B_{\max}$-linearly independent family $(x_i)_{i \in s}$ of fixed periods, by Zorn's lemma. For a fixed period $y$, maximality gives $b \neq 0$ and $w$ with $b y = \sum_i w_i x_i$. Applying $g$ and comparing coefficients gives $b\, g(w) = g(b)\, w$. Regularity gives $w = b a$, so $y = \sum_i a_i x_i$. $\square$

**Remark (Formalization).** The basis is indexed by a set $s$ of fixed periods, and the source does not prove that $s$ is finite. For $T$ free of rank $d$ over $\mathbb{Z}_p$, the module $B_{\max} \otimes T$ is free of rank $d$, and every basis has $d$ elements, so $s$ is finite in that case. The theorem is proved by Zorn's lemma, and the basis is not explicit.

Classically, the fixed basis gives the comparison isomorphism $B_{\mathrm{cris}} \otimes_{K_0} D_{\mathrm{cris}}(V) \cong B_{\mathrm{cris}} \otimes_{\mathbb{Q}_p} V$. The source uses the basis directly.

### Stability

The next three theorems give the stability of admissible representations under subobjects and finite direct sums, under tensor products and quotients, and under twisted duals. Classically these are in Fontaine, Astérisque 223, Exposé III, Section 1, and Brinon-Conrad, Section 5.2. Let $\mathrm{nearOne} \leq F$ in all three.

**Theorem (Subobjects and sums).** Let $\tau_i$ on $S_i$ be finitely many representations admissible along $F$. Let $f_i : T' \to S_i$ be $\mathbb{Z}_p$-linear maps that are jointly injective and equivariant for $F$-almost all $g$. Then $\rho'$ on $T'$ is admissible along $F$.

Lean: `New.Period.IsAdmissible.of_jointly_injective` (Lib/PadicHodge/Crystalline/Regularity.lean), `New.Period.IsAdmissible.of_retraction`, `New.Period.le_of_fixed_mem_of_saturated`.

The proof goes through a retraction: the base change of $(f_i)$ to $B_{\max}$ has a left inverse, and its image is a saturated stable submodule of a free module, which is spanned by its fixed elements (`le_of_fixed_mem_of_saturated`).

**Theorem (Tensor products and quotients).** Let $\beta : T'' \times T \to T'$ be a $\mathbb{Z}_p$-bilinear map that is equivariant for $\sigma$, $\rho$, $\rho'$ and whose values span $T'$. If $\sigma$ and $\rho$ are admissible along $F$, then so is $\rho'$.

Lean: `New.Period.IsAdmissible.of_bilinear` (Lib/PadicHodge/Crystalline/Regularity.lean).

**Theorem (Twisted duals).** Let $T$ be finite and free over $R$ and admissible along $F$. Let $b : T'' \cong \mathrm{Hom}_R(T, R)$ be an $R$-linear isomorphism with $b(\sigma(g)x)(\rho(g)y) = \chi(g)^c\, b(x)(y)$. Then $\sigma$ is admissible along $F$. Also, for $s$ in inertia, every polynomial that kills $(s, 0)$ on $T$ kills $(s^{-1}, 0)$ on $T''$.

Lean: `New.Period.IsAdmissible.of_pairing` (Lib/PadicHodge/Crystalline/Regularity.lean).

The second claim of the last theorem uses the notion of a polynomial that kills a pair, which is defined in Section 6.
