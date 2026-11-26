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

In the source, a representation is *crystalline* when it is admissible for the ring $B_{\max}$ of Colmez, not for the ring $B_{\mathrm{cris}}$ of Fontaine. The two notions agree in the classical theory, but the source does not prove this and does not use it. It builds its own $B_{\max}$, $B_{\mathrm{dR}}$ and period $t$, and no theorem of the argument is stated on the classical objects. So a reader must read "crystalline" in this chapter as "$B_{\max}$-admissible". The register of findings records this as F-056 in [definitions weaker than the textbook](/chapter/register-of-findings/).

### Where the chapter sits

The plan of the proof is in [the theorem and the plan](/chapter/theorem-and-plan/). The proof of Theorem C uses Galois representations of number fields with local conditions at the primes above $\ell$: the representation is crystalline there, it has prescribed Hodge-Tate weights, and a polynomial kills the action of a Frobenius on its Weil-Deligne representation. Volume 12 forms Selmer groups with these local conditions and bounds their size. The bound needs to know how many crystalline classes there are. That number is the rank formula of Section 8. Volume 3 uses the same cocycles in [local duality and the Greenberg-Wiles count](/chapter/local-duality/), and Volume 11 lists this chapter among the inputs of Volume 12 in [the plan of Theorem C](/chapter/theorem-c-plan/).

The comparison theorems of the source, in [the comparison theorems on test objects](/chapter/comparison-theorems/), prove that the cohomology of the varieties of the proof is crystalline in the sense of this chapter. The cohomology itself is defined in [cohomology as Ext on test rings](/chapter/cohomology-ext/), on the schemes of [schemes through their points](/chapter/schemes-through-points/). This chapter does not use those two chapters.

### What the chapter uses

The chapter uses Mathlib's $\mathbb{Q}_p$, $\overline{\mathbb{Q}}_p$, $\mathbb{C}_p$, Witt vectors, the tilt and Fontaine's map $\theta$, and the Galois theory of infinite extensions. Mathlib has no other $p$-adic Hodge theory, and the source proves the theorems of Ax and Tate that it needs. Two proofs, in Sections 5 and 6, use a "Kummer chart" from the next chapter. Section 5 states the result that they use.

### Notation

Fix a prime $p$. Let $G_p = \mathrm{Gal}(\overline{\mathbb{Q}}_p/\mathbb{Q}_p)$, acting on $\mathbb{C}_p$ by continuous isometries, let $O_C$ be the ring of integers of $\mathbb{C}_p$, and let $\chi : G_p \to \mathbb{Z}_p^\times$ be the cyclotomic character. The tilt is $O^\flat = \varprojlim_{x \mapsto x^p} O_C/p$, a perfect ring of characteristic $p$, with the multiplicative map $x \mapsto x^\sharp$ from $O^\flat$ to $O_C$, $(x_n) \mapsto \lim \hat x_n^{p^n}$.

The source works with a group $\Gamma$ and a homomorphism $j : \Gamma \to G_p$ with open image. The main case is $\Gamma = G_K$ for a finite extension $K$ of $\mathbb{Q}_p$ inside $\overline{\mathbb{Q}}_p$, with $j$ the inclusion. A representation of $\Gamma$ is a module $T$ over a ring $R$ with a linear action $\rho$ of $\Gamma$. Here $R$ is a $\mathbb{Z}_p$-algebra. The cyclotomic character of $\Gamma$ is $\chi \circ j$, and the book writes $\chi$ for it.

### A sketch

The rings come in a tower:
$$A_{\inf} = W(O^\flat) \;\longrightarrow\; A_{\max} \;\longrightarrow\; B^+ = A_{\max}[1/p] \;\longrightarrow\; B_{\max} = B^+[1/\mu] \;\longrightarrow\; B_{\mathrm{dR}} = \mathrm{Frac}(B_{\mathrm{dR}}^+).$$
Here $\mu = [\varepsilon] - 1$ for a compatible system $\varepsilon$ of $p$-power roots of unity, and $\xi$ generates the kernel of $\theta$. Section 2 proves that $\ker\theta = (\xi)$. Section 3 proves the theorems of Ax and Tate on the Galois invariants of $\mathbb{C}_p$. Section 4 builds the other rings, the period $t$ and the fundamental exact sequence. Section 5 defines admissible, crystalline and potentially crystalline representations, and proves that the fixed periods of an admissible representation contain a basis. Section 6 builds a linear Frobenius in place of the Weil-Deligne representation. Section 7 defines the Hodge-Tate jumps and proves that a potentially crystalline representation of rank $d$ has $d$ jumps. Section 8 proves the rank formula
$$\operatorname{rank}_{\mathbb{Z}_p} Z_f(T) = d + n \cdot \#\{\text{negative jumps}\},$$
where $Z_f(T)$ is the module of crystalline cocycles, $d$ the rank of $T$ and $n$ the index of $j(\Gamma)$ in $G_p$. Section 9 has the exercises and the notes.

Each section states the classical form of its results with a source, then the form in Lean. The remarks on the formalization say where the two differ.
