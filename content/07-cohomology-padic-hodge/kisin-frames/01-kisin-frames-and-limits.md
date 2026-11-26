---
title: Kisin frames and limits
lean:
  - Lib/PadicHodge/Kisin/FrameTheorem.lean
  - Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean
  - Lib/PadicHodge/Limit/CrystallineLimit.lean
  - Lib/PadicHodge/Limit/TraceLimit.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Kisin frames and limits

This chapter is about two parts of `Lib/PadicHodge`. The first part is `Lib/PadicHodge/Kisin`. It attaches to a crystalline lattice a module over a ring of power series, in the style of Kisin. The second part is `Lib/PadicHodge/Limit`. It shows that a $p$-adic limit of crystalline representations is crystalline, and that the local conditions of a Galois representation pass to limits of traces. The two parts are connected. The limit theorem uses one period that bounds the denominators of all crystalline lattices with jumps in a fixed interval, and the source gets that period from the frames of the first part.

The chapter uses the period rings of the chapter [Period rings and crystalline representations](/chapter/period-rings/). We use $A_{\inf}$, Fontaine's map $\theta$, the elements $\xi$, $\mu = [\varepsilon] - 1$ and $\tau = [\varepsilon^{1/p}] - 1$, Colmez's ring $A_{\max}$, the ring $B^+ = A_{\max}[1/p]$, the ring $B_{\max} = B^+[1/\mu]$ and the ring $B_{\mathrm{dR}}$ with its filtration. A representation is crystalline when it is $B_{\max}$-admissible: the invariants of $B_{\max} \otimes T$ span it over $B_{\max}$. The chapter [The comparison theorems on test objects](/chapter/comparison-theorems/) uses the same rings.

### The classical theory

Let $K$ be a finite extension of $\mathbb{Q}_p$ with residue field $k$ and uniformizer $\pi$. Let $\mathfrak{S} = W(k)[[u]]$, and let $E(u)$ be the Eisenstein polynomial of $\pi$. Fix a compatible system $\pi^{1/p^n}$ of roots of $\pi$, and let $K_\infty$ be the union of the fields $K(\pi^{1/p^n})$. The map $u \mapsto [\pi^\flat]$ embeds $\mathfrak{S}$ in $A_{\inf}$, and $E$ goes to a generator of $\ker\theta$. Kisin attaches to a $G_K$-stable $\mathbb{Z}_p$-lattice $T$ in a crystalline representation with Hodge-Tate weights in $[0, h]$ a finite free $\mathfrak{S}$-module $\mathfrak{M}$ with a Frobenius $\varphi$. The cokernel of the linearized Frobenius $\varphi^*\mathfrak{M} \to \mathfrak{M}$ is killed by $E^h$. This is the condition of *finite $E$-height*. The functor $T \mapsto \mathfrak{M}$ is fully faithful on lattices in crystalline representations. The source is M. Kisin, Crystalline representations and F-crystals, in Algebraic Geometry and Number Theory, Progr. Math. 253 (2006), 459-496. Bhatt, Morrow and Scholze give a version over $A_{\inf}$, the Breuil-Kisin-Fargues modules, in Integral $p$-adic Hodge theory, Publ. Math. IHÉS 128 (2018), section 4.

Kisin's proof uses Kedlaya's slope theory and étale $\varphi$-modules. The docstring of `Lib/PadicHodge/Kisin/PeriodMatrixFrame.lean` says that the source does not use either. It works with explicit matrices of periods and with linear retractions of $A_{\inf}$ onto the image of $\mathfrak{S}$.

### What the source proves

The source works with a *chart*: a map $\Lambda[[X]] \to A_{\inf}$ with $\Lambda = W(\mathbb{F}_{p^f})$, which sends $X$ to a Teichmüller element $z$ and an element $X^e V + p$ to an associate of $\xi$. A *Kummer chart* adds a subgroup $\Gamma'$ of the Galois group that moves $z$ by roots of unity. The next section treats these objects.

For a crystalline lattice $T$ and a chart, the source finds a *period matrix* $U$ over $B^+$ and then a *frame*: matrices $Q$ and $Z$ with $QL = \tau^h$, $UZ = E^h Q$ and $\varphi(Q) = vQB$ with $B$ over the image $S$ of the chart. For a *jump lattice* over a Kummer chart, the source defines an $A_{\inf}$-module $M$ (`kisinAinf`) and an $S$-module $N$ (`kisinModule`). The frame theorem says that $N$ is free over $S$, that $M$ is the $A_{\inf}$-span of $N$, that $\tau^a M$ is in $A_{\inf} \otimes T$ and $\tau^a (A_{\inf} \otimes T)$ is in $M$, and that $E^a \varphi N \subseteq N$. Here $a$ is the jump bound of the lattice.

The source does not prove the inclusion $E^n N \subseteq S\varphi(N)$. So it does not prove finite $E$-height. It does not state an equivalence of categories. The docstring of `New.Lift.KummerChart.JumpLattice.frame_theorem` says this. The source calls its result "a substitute, in the form needed here, for part of Kisin's theorem".

**Remark (Formalization).** The source uses Colmez's $B_{\max}$ in place of Fontaine's $B_{\mathrm{cris}}$. The comparison of the two rings is not formalized. So "crystalline" in this chapter means $B_{\max}$-admissible. The classical texts show that the two notions agree. The source does not use that fact, and no statement in this chapter depends on it.

The second part of the chapter is the limit theorem. Let a representation $R$ of a compact group be the limit, in the sense of traces on the group ring $\mathbb{Z}_p[G]$, of crystalline representations with jumps in $[0, h]$. Then the source shows that $R$ is crystalline. The classical form is a theorem of Berger for $\mathbb{Q}_p$-representations with bounded weights, and of Liu for lattices. The source applies the lattice form to the image of the group ring. The result `New.GaloisRep.local_clauses_of_trace_limit` then gives the local clauses of a Galois representation at a limit of traces: it is unramified or crystalline, its jumps are the limits of the jumps, and polynomials that kill a Weil element pass to the limit.

### Where the results are used

The frame theorem and jump lattices are used in the part `New/Congruences/Lifting` of the proof. The files that refer to `JumpLattice` or `frame_theorem` include `TameCharts`, `ExponentLattices`, `HodgeExpansion`, `DeepPoints`, `SidePoints`, `LongGap`, `FewLowJumps`, `SafeMoves`, `CupProductBound`, `CupOrthogonalityBounds` and `CutExponentBounds`, and also `New/Congruences/LocalLoss/LocalLattices`. The trace limit structure `New.GaloisRep.IsTraceLimit` is used in `Lib/GaloisRep/Main`: in `AllRanks`, `SplitCase` and `CuspidalTypes`. These are the places where local conditions of a Galois representation come from a family of representations attached to automorphic forms.

The source claims that these files compile with no `sorry`. This chapter describes the statements. It does not claim that the proof of any result is correct beyond this: Lean accepts it, if the reported checks hold.

### Plan of the chapter

The sections come in this order.

1. Charts and Kummer charts: the ring $S$, the element $E$, Weierstrass division, the existence of a Kummer chart for each open subgroup.
2. Period matrices and frames: the ring $S_B$, the period matrix of a crystalline lattice, and the frame.
3. Jump lattices and Kisin modules: forms with values in $B_{\mathrm{dR}}$, the modules $M$ and $N$, and letters.
4. The frame theorem: the nine properties and their consequences.
5. Limits of crystalline representations: the uniform period bound, the limit theorem, and the trace limit structure.
6. Exercises, notes and references.

Each section gives the classical statement where there is one, then the statement in the source, with a `Lean:` line for each statement. Where the two differ, a remark says how.

**Remark (Notation).** In the source, $e$ is the exponent of $X$ in the chart, not the ramification index of a fixed field. For the chart that the source builds for an open subgroup of $G_{\mathbb{Q}_p}$, the product $ef$ is the index of that subgroup, see `New.Lift.KummerChart.IsChartFor`. We write $\varphi$ for the Frobenius of $A_{\inf}$ and of the rings built from it. We write $E$ for the image of $X^e A + p$ in $A_{\inf}$, where $A$ is the unit series of the chart.
