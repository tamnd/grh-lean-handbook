---
title: The chapter and what it costs
lean:
  - Lib/PadicComparison/CrystallineFrobenius.lean
  - Lib/PadicComparison/HodgeTate/PeriodMap.lean
  - Lib/Shimura/Eigenspace.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and what it costs

This chapter explains the comparison theorems of the source. In the classical theory, these theorems compare the $p$-adic étale cohomology of an algebraic variety over a $p$-adic field with cohomologies built from differential forms, through rings of periods. The source does not prove the classical theorems. It proves statements of the same shape about its own cohomology on test rings, and it proves only what its argument for Galois representations needs. This section says what the chapter proves, where the results enter the argument, what they cost, and how the proofs go.

### The classical theorems

Let $C = \mathbb{C}_p$ be the completion of an algebraic closure $\overline{\mathbb{Q}}_p$ of $\mathbb{Q}_p$, and let $\mathcal{O}_C$ be its valuation ring. Let $G_p = \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$. Four results of $p$-adic Hodge theory stand behind this chapter.

1. *The primitive comparison theorem.* Let $X$ be a proper smooth rigid analytic variety over $C$. Then the natural map $H^i_{\mathrm{et}}(X, \mathbb{F}_p) \otimes \mathcal{O}_C/p \to H^i_{\mathrm{et}}(X, \mathcal{O}_X^+/p)$ is an almost isomorphism, and $H^i_{\mathrm{et}}(X, \mathbb{F}_p)$ is finite. This is Scholze, *p-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), Theorem 1.3. For algebraic varieties, the statement goes back to Faltings.
2. *Finiteness.* The groups $H^i_{\mathrm{et}}(X, \mathbb{Z}_p)$ are finitely generated $\mathbb{Z}_p$-modules. For proper algebraic varieties, this is SGA 4, Exposé XIV, together with the passage to the limit over $\mathbb{Z}/p^k$.
3. *The Hodge-Tate decomposition.* For $X$ proper and smooth over a finite extension $K$ of $\mathbb{Q}_p$, there is a $G_K$-equivariant isomorphism $H^n_{\mathrm{et}}(X_{\overline{K}}, \mathbb{Q}_p) \otimes_{\mathbb{Q}_p} C \cong \bigoplus_{i+j=n} H^i(X, \Omega^j) \otimes_K C(-j)$. This is due to Faltings, *p-adic Hodge theory*, J. Amer. Math. Soc. 1 (1988), and Scholze 2013 gives a proof by perfectoid methods.
4. *The crystalline comparison.* If $X$ has good reduction over $W(k)$, then $H^n_{\mathrm{et}}(X_{\overline{K}}, \mathbb{Q}_p)$ is a crystalline representation of $G_K$, and $D_{\mathrm{cris}}$ of it is the crystalline cohomology of the special fibre, with its Frobenius. This is due to Fontaine and Messing and to Faltings, *Crystalline cohomology and p-adic Galois representations* (1989). Bhatt, Morrow and Scholze give a proof in *Integral p-adic Hodge theory*, Publ. Math. IHÉS 128 (2018).

The source cites all four results. It proves none of them as stated.

### What the source proves

The source works with the cohomology of [the previous chapters](/chapter/cohomology-ext/). For a scheme $Y$ over a ring $R$ and an $R$-algebra $\Omega$ that is an algebraic closure of $\mathbb{Q}$, the "geometric $p$-adic cohomology" of $Y$ is $V^n(Y) = \mathbb{Q}_p \otimes_{\mathbb{Z}_p} H^n$, where $H^n$ is an Ext group on the category of test rings. The coefficients are the Witt vectors of the locally constant functions to $\mathbb{F}_p$. The source proves four groups of statements about these groups, and each group has the shape of one classical theorem.

1. *Almost descent* (Section 3). On perfect algebras over the tilt $\mathcal{O}^\flat$ of $\mathcal{O}_C$, the coefficients $b \mapsto b \otimes N \otimes \mathfrak{m}$ are acyclic, when $p^\flat$ kills $N$. Here $\mathfrak{m}$ is the maximal ideal of $\mathcal{O}^\flat$. This is the form of the almost purity and v-descent results that the source needs.
2. *The primitive comparison* (Sections 4 and 5). For $Y$ proper and covered by étale charts over $\Omega$, the cohomology of the points of $Y$ commutes with flat base change of the coefficients, the cohomology with $\mathbb{F}_p$ coefficients is finite, and the cohomology with coefficients from the tilt is the cohomology of the points of $Y$ in $p$-adic test rings. From this, $V^n(Y)$ is finite over $\mathbb{Q}_p$, the Galois action on it is continuous, and a period map compares $K \otimes V^n(Y)$ with cohomology with period coefficients, for any period ring pair $(S, K)$.
3. *The Hodge-Tate map* (Section 6). A map $\lambda_h$ sends Hodge cohomology classes to cohomology on pairs, and its values come from vectors of $\mathbb{C}_p \otimes V^{q+h}(Y)$ of Hodge-Tate weight $h$. The source does not prove that $\lambda_h$ is a bijection.
4. *Crystallinity and the Frobenius relation* (Section 7). If $Y$ is charted over a noetherian ring $R$ and over $\Omega$, the decomposition group at a $p$-adic place acts on $V^n(Y)$ by a crystalline representation. A congruence relation between Frobenius twists of maps $W \to Y$ on the special fibre gives the same relation between operators on $B_{\max} \otimes V^n(Y)$.

Section 2 gives the objects on which all of this happens: the $p$-adic test rings, their tilts, and Fontaine's map $\theta$. Section 8 has exercises and the notes.

### Where the chapter enters the argument

The source reduces the Generalized Riemann Hypothesis to three theorems on lattices of automorphic forms. [The plan](/chapter/theorem-and-plan/) gives the reduction. Theorem C needs Galois representations attached to automorphic forms on unitary groups. These come from the cohomology of Shimura varieties in Volume 8, and [the first chapter of this volume](/chapter/schemes-through-points/) shows the chain of declarations from the main argument to this volume.

The comparison theorems enter that chain at four lines of `Lib/Shimura/Eigenspace.lean`. The lemma `New.Variety.Model.isNullHecke_mul_of_kills_weight` (line 418) uses the Woods Hole formula of [Chapter 2](/chapter/cohomology-ext/) at line 458 and the Hodge-Tate result `New.Variety.exists_hasHodgeTateWeight` of Section 6 at line 461. The lemma `New.Variety.Model.isKilledBy_heckePoly_of_isEigenQuotient` (line 615) uses the crystalline relation `New.Variety.ellAdicCohom.isCrystalline_and_linearFrob_rel` of Section 7 at line 674. The theorem `New.Variety.Model.exists_galois_rep` (line 689) uses the same crystalline result at line 746 with the empty relation, to get crystallinity alone. It then calls the two lemmas: line 759 calls `New.Variety.Model.jumpsRelAt_of_isEigenQuotient`, which calls the first lemma at line 532, and line 761 calls the second lemma. The same theorem uses `New.Variety.ellAdicCohom.continuous_galoisAction` of Section 5 at line 737, in the call to `New.Variety.exists_isEigenQuotient`. That lemma also needs the instance of finite dimension of $V^n(Y)$ over $\mathbb{Q}_p$ from Section 5, and Lean finds it by instance search. So three results of this chapter are used by name in the proof: the Hodge-Tate result, the crystalline result and the continuity of the Galois action. The finiteness enters as an instance. All other results of this chapter reach the proof through these.

The Hodge-Tate result gives the Hodge-Tate jumps of the representation, together with the Woods Hole formula. The crystalline result gives crystallinity at $p$ and the relation between the Frobenius and the Hecke polynomial, through the congruence relation of the integral model.

### The cost

The volume has a cost, and this chapter carries it. There are three points. The reader must keep them in mind in every section.

*The cohomology is not étale cohomology.* The groups $H^n$ are Ext groups of functors on a category of test rings. The source does not compare them with étale cohomology in the sense of SGA 4. So "$V^n(Y)$ is finite" and "$V^n(Y)$ is crystalline" are statements about these Ext groups. A reader who wants the classical statements needs a comparison with étale cohomology. The source does not give it.

*"Crystalline" means $B_{\max}$-admissible.* The source uses the ring $B_{\max}$ of Colmez, not the ring $B_{\mathrm{cris}}$ of Fontaine. A representation is crystalline in the source if the $B_{\max}$-periods fixed by the group span $B_{\max} \otimes V$. [The chapter on period rings](/chapter/period-rings/) gives the definitions.

*The proof uses only the proved properties.* The source proves what the argument needs and nothing more. There is no integral comparison, no Hodge-Tate decomposition, no filtration, and no identification of $D_{\mathrm{cris}}$ with crystalline cohomology. The docstring of `CrystallineFrobenius.lean` says this in one line: "There is no integral form, no Hodge-Tate decomposition, and no identification with étale or crystalline cohomology."

The source claims that these weaker statements are enough for the argument. Lean accepts the statements, if the reported checks hold. This chapter explains what the statements say and how the source proves them.

### A sketch of the proofs

The proofs follow the perfectoid method of Scholze. The source replaces each geometric object by an algebraic one.

*Test rings.* A cell is a complete valuation ring, absolutely integrally closed, of mixed characteristic. A $p$-adic test is a nonempty product of cells with a map from $\mathcal{O}_C$. The product can be infinite. Its tilt is a perfect ring in characteristic $p$. The functor from $p$-adic tests to perfect $\mathcal{O}^\flat$-algebras is fully faithful, and Fontaine's map $\theta$ recovers the test from the Witt vectors of its tilt. Section 2 proves these facts.

*Almost descent.* Points of a perfect $\mathcal{O}^\flat$-algebra in tilts of tests satisfy v-descent for the almost coefficients. Čech descent then gives acyclicity. The proof reduces to a valuation ring over which the tilt of a test is faithfully flat. Section 3 gives the proof and the adic step that passes from coefficients mod $p$ to $p$-adic coefficients.

*Duality on products of projective lines.* The source shows that a comparison of two cohomology theories holds on all charted schemes once it holds at a point, if both theories satisfy a line formula on $\mathbb{P}^1$. The proof uses excision, products with $\mathbb{P}^1$ and the Leray-Hirsch theorem. Section 4 gives the argument.

*The primitive comparison.* The point case holds because $\mathcal{O}^\flat$ and $\Omega$ are initial. The duality argument extends it to charted proper schemes. The valuative criterion of properness identifies the points of $Y$ in a test with the points in the generic fibre. Section 5 states the result and its corollaries, and lifts it to period rings.

*The Hodge-Tate map.* The square-zero thickening $W(S^\flat)[1/p]/(\ker \theta)^2$ of $S[1/p]$ gives pairs $(S, M)$. Lifts of points to these pairs give a contraction class, and its $h$-th power defines $\lambda_h$. The Galois group acts on the thickening through the cyclotomic character, and this gives the weight. Section 6 has the details.

*The crystalline comparison.* The source uses a Frobenius twist of the map $A_{\inf} \to A_{\max}$ and the ideal of elements with divided powers. On étale charts over tori, it adjoins compatible roots of the coordinates one at a time, and a Koszul argument shows that each step is a "line". This gives a spanning set of fixed periods, so the representation is crystalline. The same periods carry the Frobenius relation. Section 7 has the details.
