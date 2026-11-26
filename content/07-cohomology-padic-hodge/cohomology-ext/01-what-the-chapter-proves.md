---
title: What the chapter proves
lean:
  - Lib/Cohomology/WoodsHole.lean
  - Lib/Cohomology/Etale/Basic.lean
  - Lib/Cohomology/Etale/FilteredLimits.lean
decls:
  - New.Variety.H
  - New.Variety.ellAdicCohom.woods_hole
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter describes the cohomology theory of the source. The source does not import étale cohomology, coherent cohomology or de Rham cohomology. It defines one notion of cohomology and builds the rest from it. The cohomology of a functor $X$ from rings to sets, with coefficients in a functor $F$ to abelian groups, is the Ext group $\operatorname{Ext}^n(\mathbb{Z}[X], F)$. Here $\mathbb{Z}[X]$ is the functor $A \mapsto \mathbb{Z}[X(A)]$ of free abelian groups. The Ext is taken in the category of all functors on a small category of test objects. The test objects are certain rings, the test rings, or pairs of a ring and a module.

The chapter states three main results of this theory.

1. **Proper base change** for coefficients $\mathbb{Z}/\ell$. Let $A$ be a valuation ring whose fraction field is algebraically closed, with $\ell$ invertible in $A$. Let $Y$ be proper over $A$. Then restriction from $Y$ to its closed fibre is bijective on cohomology in every degree. Section 4 gives the precise form.
2. **Smooth base change** for coefficients $\mathbb{Z}/\ell$. Let $A$ be a valuation ring of $\bar{\mathbb{Q}}$ over a prime $p \neq \ell$, and let $Y$ be built from charts étale over tori. Then pull-back from $Y_A$ to $Y_{\bar{\mathbb{Q}}}$ is bijective on cohomology in every degree. Section 5 gives the precise form.
3. **The Woods Hole formula, vanishing half.** Let $u_i : W \to Y$ be maps and $b_i$ scalars. If $\sum_i b_i u_i^*$ kills all Hodge classes of $Y$ under the Hodge-Tate map $\lambda_h$, then for every map $c : W \to Y$ the local terms of weight $h$ at the coincidences of $c$ with the $u_i$ add up to zero. Section 7 gives the precise form.

Lean: `New.Variety.H` (Lib/Cohomology/Etale/Basic.lean).

Lean: `New.Variety.ellAdicCohom.woods_hole` (Lib/Cohomology/WoodsHole.lean).

The first two results are used inside the theory. The third is the only result of the theory that a later volume uses by name.

### Where the chapter sits

The chapter uses the functors of points of [Chapter 1 of this volume](/chapter/schemes-through-points/). There a scheme $X$ over a ring $R$ enters the source only through the functor $B \mapsto X(B)$ on commutative rings. This chapter takes that functor as its basic object. It never uses a sheaf on a site of the scheme.

The chapter feeds Volume 8. There the source builds Galois representations from the $\ell$-adic cohomology of certain models of Shimura varieties ([Building the representations](/chapter/building-representations/)). The Woods Hole formula gives the trace identities that relate Hecke operators to point counts ([The congruence relation](/chapter/congruence-relation/)). The lemma `woods_hole` is applied once, at line 458 of `Lib/Shimura/Eigenspace.lean`, in the proof of `New.Variety.Model.isNullHecke_mul_of_kills_weight`. A chain of lemmas leads from there to `New.Variety.Model.exists_galois_rep` (line 689 of the same file) and then to the files `Lib/GaloisRep/Main/SeedRepresentation.lean`, `Lib/GaloisRep/Main/SplitCase.lean` and `Lib/GaloisRep/Main/AllRanks.lean`. The final theorem of the source in `New` uses no theorem of this chapter by name. It reaches the chapter only through this path. The plan of the whole proof is in [The theorem and the plan](/chapter/theorem-and-plan/).

### What it is not

The cohomology of this chapter is not compared with étale cohomology. The head of the file on filtered limits says that "equality with étale cohomology is neither proved nor used" ([FilteredLimits.lean](lean:Lib/Cohomology/Etale/FilteredLimits.lean#L40)). The head of the Woods Hole file says that "no comparison with étale or coherent cohomology is stated" ([WoodsHole.lean](lean:Lib/Cohomology/WoodsHole.lean#L49)). So the names "proper base change" and "smooth base change" are names of analogues. The theorems of SGA 4 are statements about sheaves on the étale site. The theorems here are statements about Ext groups of functors on test rings. They have the same shape, and the source proves them from its own definition. A reader must not transfer a theorem of SGA 4 to this theory without a proof. Section 3 says more about this point.

The cohomology is Ext of presheaves, not of sheaves. The category of coefficients is the category of all functors from test rings to abelian groups, with no condition of descent. The test rings are chosen so that this does not matter for the coefficients that the source uses. Section 3 explains why.

The source also does not compute a trace. The Woods Hole formula of the source is the vanishing half of the holomorphic Lefschetz formula of Atiyah and Bott. It says that a sum of local terms is zero under a hypothesis. Section 7 states the exact form.

### What the chapter uses

The reader needs the language of categories and functors, abelian categories, and Ext groups in an abelian category with enough projectives (Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994, Chapter 2 and Section 3.4). The reader needs valuation rings, absolutely integrally closed rings and Witt vectors at the level of a first course in commutative algebra. For Sections 6 and 7 the reader needs exterior powers and square-zero extensions. For the comparison with the classical theory, the reader can use Milne, *Étale Cohomology* (Princeton University Press, 1980), Chapter VI.

### The sketch

Section 2 defines spaces, coefficients and cohomology. A space is a functor from commutative rings to sets. The free abelian group on a representable functor is projective, by the Yoneda lemma. So a representable space has no higher cohomology. The basic tools are the Mayer-Vietoris sequence and the notion of a dense subfunctor.

Section 3 defines the test rings. These are reduced, absolutely integrally closed rings in which any two elements are comparable up to an idempotent. Their local rings are valuation rings of algebraically closed fields. The coefficients $\mathbb{Z}/\ell$ are the locally constant functions on the spectrum. The $\ell$-adic coefficients are their Witt vectors. The $\ell$-adic cohomology of a scheme $X$ over $R$ is $\mathbb{Q}_\ell \otimes H^n(X_\Omega, \mathbb{Z}_\ell)$. A group that acts on $\Omega$ acts on it.

Section 4 proves proper base change. The proof covers a proper space by its points with values in valuation rings. Čech descent along this cover reduces the claim to the case of a single valuation ring, where it is a direct computation.

Section 5 treats the projective line. The class $\eta$ of $\mathcal{O}(1)$ and the class $1$ form a basis of the cohomology of $\mathbb{P}^1$ over a base, by a Leray-Hirsch argument. Smooth base change then follows, for spaces built from charts étale over tori.

Section 6 defines Hodge cohomology. The test objects are pairs $(A, M)$ of a $k$-algebra and a module. The coefficient is $(A, M) \mapsto \bigwedge_A M$. A space $N$ gives the functor $(A, M) \mapsto N(A \oplus M)$. The section defines the symbol class $[dT/T]$, the classes of points, and the Künneth formula, and it constructs the class of the diagonal.

Section 7 proves the fixed point formula: the pull-back of the diagonal class along a twisted graph is the sum of the point classes of the coincidences, with their Jacobian ratios. It then states the Woods Hole formula. The proof applies the Hodge-Tate map $\lambda_d$, which keeps distinct point classes linearly independent. It then takes the coefficient of $t^h$ in the twist parameter $t$. A model case on $\mathbb{P}^1$ shows the local terms.

Section 8 has exercises and notes.

**Remark (Formalization).** All theorems of this chapter are stated in the source and accepted by Lean, if the reported checks hold. The chapter does not claim that the theory agrees with the classical theories. Where the chapter gives a classical statement, it gives it with a citation, and then gives the form of the source. The register of findings has three rows on this part of the source: F-108 and F-109 on the index of the source, and F-112 on the name of `woods_hole` ([Citations and docstrings](/chapter/register-of-findings/)). The book follows the files where the index and the files disagree.
