---
title: Periods in the argument
lean:
  - Lib/PadicHodge/PeriodRings/Ainf.lean
  - Lib/PadicHodge/PeriodRings/CrystallineRings.lean
  - Lib/PadicHodge/Crystalline/Basic.lean
  - Lib/PadicHodge/BlochKato.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Periods in the argument

This chapter builds the period rings of $p$-adic Hodge theory and the notions of crystalline representation, Hodge-Tate weight and crystalline cocycle that the source defines with them. Its last main result is a rank formula of Bloch and Kato for the module of crystalline cocycles of a lattice. The chapter follows the files `PeriodRings`, `TateSen`, `Crystalline`, `BlochKato` and `Characters` of the source. The Kisin modules and the limits of crystalline representations come in the next chapter, [Kisin frames and limits](/chapter/kisin-frames/).

### The cost, first

The volume note asks the book to say this at the start of each chapter of this volume, and the statement here is short. In the source, a representation is *crystalline* when it is admissible for the ring $B_{\max}$ of Colmez. It is not admissible for the ring $B_{\mathrm{cris}}$ of Fontaine. The two notions agree in the classical theory, but the source does not prove this, and it does not use it. The source builds its own $B_{\max}$, its own field $B_{\mathrm{dR}}$, and its own period $t$. It proves for these objects the properties that the argument needs, and no theorem of the argument is stated on the classical objects. So a reader who compares a statement of this chapter with a textbook must read "crystalline" as "$B_{\max}$-admissible". The register of findings records this as F-056 in [definitions weaker than the textbook](/chapter/register-of-findings/).

### Where the chapter sits

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). The proof of Theorem C uses Galois representations of number fields with local conditions at the primes above $\ell$: the representation is crystalline there, it has prescribed Hodge-Tate weights, and a polynomial kills the action of a Frobenius on its Weil-Deligne representation. Volume 12 forms Selmer groups with these local conditions and bounds their size. The bound needs to know how many crystalline classes there are. That number is the rank formula of Section 8. Volume 3 uses the same cocycles in [local duality and the Greenberg-Wiles count](/chapter/local-duality/), and Volume 11 lists this chapter among the inputs of Volume 12 in [the plan of Theorem C](/chapter/theorem-c-plan/).

The comparison theorems of the source, in [the comparison theorems on test objects](/chapter/comparison-theorems/), prove that the cohomology of the varieties of the proof is crystalline in the sense of this chapter. The cohomology itself is defined in [cohomology as Ext on test rings](/chapter/cohomology-ext/), on the schemes of [schemes through their points](/chapter/schemes-through-points/). This chapter does not use those two chapters.

### What the chapter uses

The chapter uses Mathlib's $p$-adic numbers $\mathbb{Q}_p$, an algebraic closure $\overline{\mathbb{Q}}_p$, its completion $\mathbb{C}_p$, Witt vectors, the tilt of a ring and Fontaine's map $\theta$. It uses the Galois theory of infinite extensions. It does not use any result of $p$-adic Hodge theory from Mathlib, since Mathlib has none beyond the definitions of the tilt and of $\theta$. The source proves the theorems of Ax and of Tate that it needs. Two proofs, in Sections 5 and 6, use a result of the next chapter, a "Kummer chart". This is a forward reference inside the source, and Section 5 states the result that they use.

### Notation

Fix a prime $p$. Let $G_p = \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$ with its profinite topology. It acts on $\mathbb{C}_p$ by continuous isometries. Let $O_C$ be the ring of integers of $\mathbb{C}_p$, and let $\chi : G_p \to \mathbb{Z}_p^\times$ be the cyclotomic character, so that $g(\zeta) = \zeta^{\chi(g)}$ for every root of unity $\zeta$ of $p$-power order. The tilt is $O^\flat = \varprojlim_{x \mapsto x^p} O_C/p$. It is a perfect ring of characteristic $p$, and $x \mapsto x^\sharp$ is the multiplicative map $O^\flat \to O_C$ that sends a compatible sequence $(x_n)$ to $\lim \hat x_n^{p^n}$, for any lifts $\hat x_n$ of the $x_n$.

The source works with a group $\Gamma$ and a homomorphism $j : \Gamma \to G_p$ with open image. The main case is $\Gamma = G_K$ for a finite extension $K$ of $\mathbb{Q}_p$ inside $\overline{\mathbb{Q}}_p$, with $j$ the inclusion. A representation of $\Gamma$ is a module $T$ over a ring $R$ with a linear action $\rho$ of $\Gamma$. Here $R$ is a $\mathbb{Z}_p$-algebra. The cyclotomic character of $\Gamma$ is $\chi \circ j$, and the book writes $\chi$ for it.

### A sketch

The rings come in a tower:
$$A_{\inf} = W(O^\flat) \;\longrightarrow\; A_{\max} \;\longrightarrow\; B^+ = A_{\max}[1/p] \;\longrightarrow\; B_{\max} = B^+[1/\mu] \;\longrightarrow\; B_{\mathrm{dR}} = \mathrm{Frac}(B_{\mathrm{dR}}^+).$$
Here $\mu = [\varepsilon] - 1$ for a compatible system $\varepsilon$ of roots of unity of $p$-power order, $A_{\max}$ is the $p$-adic completion of $A_{\inf}[\xi/p]$, with $\xi$ a generator of the kernel of $\theta$, and $B_{\mathrm{dR}}^+$ is the $\xi$-adic completion of $B^+$. Section 2 proves that $\ker\theta = (\xi)$. Section 3 proves the theorems of Ax and Tate on the Galois invariants of $\mathbb{C}_p$. Section 4 builds the other rings, the period $t$ and the fundamental exact sequence. Section 5 defines admissible, crystalline and potentially crystalline representations, and proves that the fixed periods of an admissible representation contain a basis. Section 6 builds a linear Frobenius operator in place of the Weil-Deligne representation, and proves a descent from potentially crystalline to crystalline. Section 7 defines the Hodge-Tate jumps and proves that a potentially crystalline representation of rank $d$ has $d$ jumps with multiplicity. Section 8 proves the rank formula
$$\operatorname{rank}_{\mathbb{Z}_p} Z_f(T) = d + n \cdot \#\{\text{negative jumps}\},$$
where $Z_f(T)$ is the module of crystalline cocycles, $d$ the rank of $T$ and $n$ the index of $j(\Gamma)$ in $G_p$. Section 9 has the exercises and the notes.

Each section states the classical form of its results with a source, then the form in Lean. The remarks on the formalization say where the two differ.
