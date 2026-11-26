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

This section uses the ring $B_{\max}$ of Section 4 to define admissible, crystalline and potentially crystalline representations. It proves Fontaine's computation of fixed fractions in the form that the source needs, that the fixed periods of an admissible representation contain a basis, and that admissibility is stable under the usual operations. Section 6 uses these results to build the Frobenius operator. The source cites J.-M. Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), Exposé III, Sections 1 and 5, and O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009), Sections 5.2 and 9.

### The setting

The source does not fix a field $K$. It fixes a group $\Gamma$ with a homomorphism $j : \Gamma \to G_p$ whose image is open. This is the class `OverGp`. The main example is $\Gamma = G_K$ with the inclusion, but the setting also covers open subgroups of $G_K$ and quotients through which a representation factors.

Lean: `New.Period.OverGp` (Lib/PadicHodge/Crystalline/Basic.lean).

Let $R$ be a $\mathbb{Z}_p$-algebra, $T$ an $R$-module and $\rho : \Gamma \to \mathrm{GL}_R(T)$ a representation. For a ring $B$ with an action of $G_p$, the group $\Gamma$ acts on $B \otimes_{\mathbb{Z}_p} T$ by $g \mapsto j(g) \otimes \rho(g)$. For a filter $F$ on $\Gamma$, the *fixed periods along $F$* are the $y \in B \otimes T$ such that $(j(g) \otimes \rho(g))\,y = y$ for $F$-almost all $g$.

Lean: `New.Period.tensorAction` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.fixedPeriods`.

Two filters are used. The top filter $\top$ asks that $y$ is fixed by every $g$. The filter $\mathrm{nearOne}$ is the pull-back along $j$ of the filter of neighbourhoods of $1$ in $G_p$. An element is fixed along $\mathrm{nearOne}$ when it is fixed by all $g$ with $j(g)$ in some open neighbourhood of $1$, that is, by the preimage of some open subgroup. Filters let one definition cover both cases, and they spare the source from choosing the open subgroup.

Lean: `New.Period.nearOne` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.eventually_nearOne_apply_eq`.

**Definition (Admissible, crystalline).** The representation $\rho$ is *admissible along $F$* if the fixed periods along $F$ in $B_{\max} \otimes_{\mathbb{Z}_p} T$ span it as a $B_{\max}$-module. It is *crystalline* if it is admissible along $\top$, and *potentially crystalline* if it is admissible along $\mathrm{nearOne}$. The set $D_{\mathrm{pcris}}(\rho)$ is the set of fixed periods along $\mathrm{nearOne}$.

Lean: `New.Period.IsAdmissible` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.IsCrystalline`, `New.Period.IsPotentiallyCrystalline`, `New.Period.Dpcris`.

In the classical theory (Fontaine, Astérisque 223, Exposé III, Section 5), $V$ is a finite-dimensional continuous $\mathbb{Q}_p$-representation of $G_K$, $D_{\mathrm{cris}}(V) = (B_{\mathrm{cris}} \otimes_{\mathbb{Q}_p} V)^{G_K}$, and $V$ is crystalline if $\dim_{K_0} D_{\mathrm{cris}}(V) = \dim_{\mathbb{Q}_p} V$. Since $B_{\mathrm{cris}}$ is a regular ring in Fontaine's sense, this is equivalent to the statement that the map $B_{\mathrm{cris}} \otimes_{K_0} D_{\mathrm{cris}}(V) \to B_{\mathrm{cris}} \otimes V$ is an isomorphism, and so to the statement that the invariants span $B_{\mathrm{cris}} \otimes V$. The source takes the span condition as the definition. Potentially crystalline classically means crystalline on $G_L$ for a finite extension $L$ of $K$. Along $\mathrm{nearOne}$, an element is fixed by the preimage of an open subgroup that depends on the element. When $D_{\mathrm{pcris}}$ is spanned by finitely many elements, one open subgroup fixes a spanning set, and the two notions agree up to the difference between $B_{\max}$ and $B_{\mathrm{cris}}$.

**Remark (Formalization).** The definition has no hypotheses on $T$ and $\rho$. There is no continuity, no finiteness and no freeness. The tensor product is over $\mathbb{Z}_p$, not over $R$. These choices have consequences.

1. If $T$ is killed by a power of $p$, then $B_{\max} \otimes_{\mathbb{Z}_p} T = 0$, since $p$ is a unit in $B_{\max}$. So every torsion representation is crystalline, by the definition. The source uses the notion only for lattices and for modules over $\mathbb{Q}_p$-algebras, where this effect does not occur.
2. A representation that is not continuous can be admissible. The definition does not see the topology of $T$. In the uses in Volume 12, the representations are continuous, and the hypothesis is carried by the context.
3. Because the tensor product is over $\mathbb{Z}_p$, for $R$ a finite extension of $\mathbb{Q}_p$ the module $B_{\max} \otimes_{\mathbb{Z}_p} T$ is $B_{\max} \otimes_{\mathbb{Q}_p} T$, the module of the classical theory for the underlying $\mathbb{Q}_p$-representation. The $R$-structure is extra, and it acts through `coeffEnd` below.

The register records the replacement of $B_{\mathrm{cris}}$ by $B_{\max}$ as F-056, in [definitions weaker than the textbook](/chapter/register-of-findings/).

**Definition (Crystalline cocycles).** $Z_f(\rho)$ is the $R$-submodule of maps $c : \Gamma \to T$ for which there is $y \in B_{\max} \otimes T$ with $1 \otimes c(g) = (j(g) \otimes \rho(g))\,y - y$ for every $g \in \Gamma$.

Lean: `New.Period.crysCocycles` (Lib/PadicHodge/Crystalline/Basic.lean).

A map in $Z_f(\rho)$ is a cocycle: if $1 \otimes c(g) = g y - y$ for all $g$, then $1 \otimes c(gh) = gh\,y - y = g(hy - y) + (gy - y)$, which is $1 \otimes (\rho(g)c(h) + c(g))$, and $1 \otimes -$ is injective on a lattice. The source does not ask for continuity here either. Classically (Bloch-Kato, *L-functions and Tamagawa numbers of motives*, Grothendieck Festschrift I (1990), Section 3), $H^1_f(K, V)$ is the kernel of $H^1(K, V) \to H^1(K, B_{\mathrm{cris}} \otimes V)$, and $Z_f$ is the module of cocycles whose classes lie in it. Section 8 computes the rank of $Z_f$ for a lattice.

### Two first examples

**Theorem (Tate twists).** Let $c \in \mathbb{Z}$ and let $\sigma = \chi^c \rho$, that is, $\sigma(g)x = \chi(g)^c\rho(g)x$. If $\rho$ is admissible along $F$, then so is $\sigma$. If $\Gamma$ acts on $T$ by $\chi^c$, then $\rho$ is admissible along every filter.

Lean: `New.Period.IsAdmissible.tate_twist` (Lib/PadicHodge/Crystalline/Basic.lean), `New.Period.isAdmissible_of_cyclotomicGp_zpow`, `New.Period.exists_tate_twist_unit`.

*Proof.* Let $t \in A_{\max}$ be the period of Section 4, with $g(t) = \chi(g)t$. It is $p\mu$ times a unit, and $p$ and $\mu$ are units of $B_{\max}$, so $t$ is a unit of $B_{\max}$. Put $u = t^{-c}$. Then $j(g)(u) = \chi(g)^{-c}u$, so $(j(g) \otimes \sigma(g))(uy) = u\,(j(g) \otimes \rho(g))(y)$. Multiplication by $u$ maps the fixed periods of $\rho$ onto those of $\sigma$, and it is a unit, so it maps a spanning set to a spanning set. For the second claim, the trivial representation is admissible along every filter, since every $1 \otimes x$ is fixed, and $\chi^c$ is a twist of it. $\square$

The proof of the source records more. For every $n$, the pair $(\varphi^n, j(g))$ acts on $u$ by $p^{-nc}\chi(g)^{-c}$, since $\varphi(t) = pt$. This factor $p^{-nc}$ is the reason why the Frobenius operator of a Tate twist is the original one times a power of $p$, below.

Here the source uses that $t$ is a unit of $B_{\max}$. This is the place where it matters that $B_{\max}$ inverts $\mu$: in $B^+$ the element $t$ is not a unit, and $\mathbb{Z}_p(1)$ is not $B^+$-admissible.

### Fixed fractions

The core input is Fontaine's computation of the invariants of the fraction field. Classically (Brinon-Conrad, Section 9.1), $\mathrm{Frac}(B_{\mathrm{cris}})^{G_K} = K_0$, the maximal unramified subextension of $K$. The source proves a version for one fraction and an open subgroup that it does not choose.

**Theorem (Fixed fractions).** Let $a, b \in B_{\max}$ with $b \neq 0$. Suppose that $b \cdot g(a) = g(b) \cdot a$ for all $g$ in some neighbourhood of $1$ in $G_p$. Then there are $f \geq 1$, $n \geq 0$ and $w \in W(\mathbb{F}_{p^f})$ with $p^n a = w b$.

Lean: `New.Period.Bmax.exists_witt_ratio` (Lib/PadicHodge/Crystalline/FixedRatios.lean).

So the fraction $a/b$ lies in $W(\mathbb{F}_{p^f})[1/p]$, the field $K_0$ of the classical statement for some unramified $K_0$. Here $W(\mathbb{F}_{p^f})$ is the ring of Witt vectors of the subfield $\{x \in O^\flat : x^{p^f} = x\}$ of $O^\flat$, so it is a subring of $A_{\inf}$, and $w b$ means the image of $w$ in $B_{\max}$ times $b$.

*Proof.* The relation holds on an open subgroup $U$ of $G_p$, since $G_p$ is profinite. Let $L$ be the fixed field of $U$. The source takes a *Kummer chart* for $U$. This is a Teichmüller element $z \in A_{\inf}$ with $\theta(z)$ a uniformizer of $L$, together with an Eisenstein polynomial $E$ over $W(\mathbb{F}_{p^f})$, where $p^f$ is the size of the residue field of $L$. The chart is defined and built in the Kisin folder, and is the subject of the next chapter, [Kisin frames and limits](/chapter/kisin-frames/). With the chart, the source argues as follows. The quotient $a/b$ in $B_{\mathrm{dR}}$ is fixed by $U$, so by the theorem on the invariants of $B_{\mathrm{dR}}$ in Section 4 it is an element $\lambda$ of $L$. Multiply $a$ and $b$ by a power of $\mu$ so that both lie in $B^+$. Expand both in the coordinates that the chart gives, and take a coordinate of $b$ that is not zero. The relation $a = \lambda b$ holds coordinate by coordinate. Cancel the largest power of $z$ and reduce modulo $z$. This gives $\lambda w_1 = w_0$ with $w_0, w_1 \in W(\mathbb{F}_{p^f})$ and $w_1 \neq 0$, after multiplication by a power of $p$. So $\lambda \in W(\mathbb{F}_{p^f})[1/p]$. $\square$

**Remark (Formalization).** The degree $f$ and the exponent $n$ are existential and not specified. The theorem does not say that $f$ is the residue degree of the fixed field of $U$, though the proof gives this. Only the containment $a/b \in W(\mathbb{F}_{p^f})[1/p]$ is used later. The proof depends on `New.Lift.exists_kummerChart` (Lib/PadicHodge/Kisin/KummerChartExistence.lean), which comes after this file in the reading order of the source and before it in the import order. The chapter uses the result here and leaves its proof to the next chapter.

### Regularity and bases

Fontaine calls a ring $B$ with an action of $G$ *regular* when $B$ is a domain, $B^G = \mathrm{Frac}(B)^G$, and every $b \neq 0$ such that the line $\mathbb{Q}_p b$ is $G$-stable is a unit (Fontaine, Astérisque 223, Exposé III, Section 1, and Brinon-Conrad, Section 5.2). The point of regularity is the next statement. The source proves the form that it needs, for vectors of fractions.

**Theorem (Regularity).** Let $\mathrm{nearOne} \leq F$. Let $w : \iota \to B_{\max}$ be finitely supported and let $b \in B_{\max}$ be nonzero. If $b \cdot g(w) = g(b) \cdot w$ for $F$-almost all $g$, with $g$ acting through $j$ on each coordinate, then $w = b\,a$ for some finitely supported $a$ that is fixed by $F$-almost all $g$.

Lean: `New.Period.fontaine_regularity` (Lib/PadicHodge/Crystalline/Regularity.lean).

*Proof.* Fix a coordinate $i$. The relation holds for $w_i$ and $b$ for all $g$ near $1$, since $\mathrm{nearOne} \leq F$. By the theorem on fixed fractions, $p^n w_i = c\,b$ with $c$ a Witt vector. Since $p$ is a unit of $B_{\max}$, $b$ divides $w_i$. So $w = b\,a$ for some $a$. The relation then reads $b \cdot g(b)\,g(a) = g(b) \cdot b\, a$, and $b$ and $g(b)$ are nonzero in the domain $B_{\max}$, so $g(a) = a$. $\square$

The theorem says that a fixed fraction of elements of $B_{\max}$ is a fixed element of $B_{\max}$. It does not say that the units condition of Fontaine holds. The source does not need it in that form.

**Theorem (Fixed bases).** Let $\mathrm{nearOne} \leq F$ and let $\rho$ be admissible along $F$. Then $B_{\max} \otimes T$ has a $B_{\max}$-basis whose elements are fixed periods along $F$.

Lean: `New.Period.IsAdmissible.exists_basis` (Lib/PadicHodge/Crystalline/Regularity.lean).

*Proof.* Take a maximal $B_{\max}$-linearly independent family $(x_i)_{i \in s}$ of fixed periods, by Zorn's lemma. It is enough to show that every fixed period $y$ is in the span. If $y$ is not in the family, maximality gives $b \neq 0$ and $w$ with $b y = \sum_i w_i x_i$. Apply $g$, for $g$ that fixes $y$ and all $x_i$ that occur: $g(b)\, y = \sum_i g(w_i) x_i$. Multiply the first equation by $g(b)$ and the second by $b$ and compare coefficients, which is allowed since the $x_i$ are independent: $b\, g(w) = g(b)\, w$. Regularity gives $w = b a$, and then $b y = b \sum_i a_i x_i$, so $y = \sum_i a_i x_i$. The fixed periods span by hypothesis, so the family is a basis. $\square$

**Remark (Formalization).** The basis is indexed by a set $s$ of fixed periods, and the source does not prove that $s$ is finite. For $T$ free of rank $d$ over $\mathbb{Z}_p$, the module $B_{\max} \otimes T$ is free of rank $d$, and every basis has $d$ elements, so $s$ is finite in that case. The theorem is proved by Zorn's lemma, and the basis is not explicit.

Classically, the fixed basis gives the comparison isomorphism $B_{\mathrm{cris}} \otimes_{K_0} D_{\mathrm{cris}}(V) \cong B_{\mathrm{cris}} \otimes_{\mathbb{Q}_p} V$. The source does not state an isomorphism in this form. It uses the basis directly, in the construction of the Frobenius operator below and in Sections 6 to 8.

### Stability

The next three theorems give the stability of admissible representations under subobjects and finite direct sums, under tensor products and quotients, and under twisted duals. Classically these are in Fontaine, Astérisque 223, Exposé III, Section 1, and Brinon-Conrad, Section 5.2. Let $\mathrm{nearOne} \leq F$ in all three.

**Theorem (Subobjects and sums).** Let $\tau_i$ on $S_i$ be finitely many representations admissible along $F$. Let $f_i : T' \to S_i$ be $\mathbb{Z}_p$-linear maps that are jointly injective and equivariant for $F$-almost all $g$. Then $\rho'$ on $T'$ is admissible along $F$.

Lean: `New.Period.IsAdmissible.of_jointly_injective` (Lib/PadicHodge/Crystalline/Regularity.lean), `New.Period.IsAdmissible.of_retraction`, `New.Period.le_of_fixed_mem_of_saturated`.

The proof goes through a retraction. The base change of $(f_i)$ to $B_{\max}$ has a $B_{\max}$-linear left inverse. In coordinates for fixed bases of the $B_{\max} \otimes S_i$, the image is a saturated submodule of a free module that is stable along $F$. A saturated stable submodule is spanned by its fixed elements, by an elimination argument that uses regularity at each step (`le_of_fixed_mem_of_saturated`).

**Theorem (Tensor products and quotients).** Let $\beta : T'' \times T \to T'$ be a $\mathbb{Z}_p$-bilinear map that is equivariant for $\sigma$, $\rho$, $\rho'$ and whose values span $T'$. If $\sigma$ and $\rho$ are admissible along $F$, then so is $\rho'$.

Lean: `New.Period.IsAdmissible.of_bilinear` (Lib/PadicHodge/Crystalline/Regularity.lean).

**Theorem (Twisted duals).** Let $T$ be finite and free over $R$ and admissible along $F$. Let $b : T'' \cong \mathrm{Hom}_R(T, R)$ be an $R$-linear isomorphism with $b(\sigma(g)x)(\rho(g)y) = \chi(g)^c\, b(x)(y)$. Then $\sigma$ is admissible along $F$. Also, for $s$ in inertia, every polynomial that kills $(s, 0)$ on $T$ kills $(s^{-1}, 0)$ on $T''$.

Lean: `New.Period.IsAdmissible.of_pairing` (Lib/PadicHodge/Crystalline/Regularity.lean).

The second claim of the last theorem uses the notion of a polynomial that kills a pair, which is defined in Section 6.
