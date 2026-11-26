---
title: What the chapter proves
lean:
  - New/Congruences/Lifting/ExponentLattices.lean
  - New/Congruences/Lifting/HodgeExpansion.lean
  - New/Congruences/Lifting/CupProductBound.lean
  - New/Congruences/Lifting/SidePoints.lean
  - New/Congruences/Lifting/TameCharts.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter builds the tools for the bounds on cup products at a place above $p$. The bounds are the subject of the next chapter, [cup products on Kisin modules](/chapter/cup-products/), and they feed [the local loss](/chapter/local-loss/). Together the three chapters are the fourth deep input of [the chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof). The plan of the whole argument is in [the theorem and the plan](/chapter/theorem-and-plan/).

The tools are of five kinds.

1. *Lattices with prescribed orders.* For a jump lattice $L$ over a Kummer chart and a letter $i$, the chapter defines the elements of $A_{\inf}$ times the localized Kisin module whose form values have at least prescribed orders along the Hodge filtration. It proves the rules that these lattices obey: the gap rule, saturation, the twists by $\varphi^a(E)$, the Galois action and the improvement of orders by invariance.
2. *The depth lemma.* An element whose value at $\varphi^a(E)$ is a constant modulo $\mathrm{Fil}^n$ is sent by an explicit operator to an element whose value is a constant modulo $\mathrm{Fil}^{n+1}$. The operator multiplies the constant by $p^{c}$, where $c = v_p(n) + d + 3a$ is the *cost* of the step.
3. *Hodge expansions.* The lattice with the standard orders is the Frobenius twist $\varphi^l(M)$ of the module $M$ of the frame theorem. Products of lattices add orders. Among $fn + 1$ points one finds a primitive combination that gains one step.
4. *Pairings and cokernel killers.* A pairing of two sides gives a cup product. The pairing lemma says when this cup product is a coboundary up to a power of $p$. A *cokernel killer* is a bound $p^\kappa E^s$ for the failure of the lift of constants. The chapter proves three such bounds: for unramified charts with small jumps, for jumps that are small at a few letters, and for tame charts.
5. *Side points.* With a cokernel killer and the depth lemma, the chapter builds points over each constant with prescribed orders and depths, at an explicit total cost.

### Notation

The background is in Volume 7. A Kummer chart $k$ for a group $\Gamma$ over $G_p$ is defined in [charts and Kummer charts](/chapter/kisin-frames/#charts-and-kummer-charts). It gives a subgroup $\Gamma'$ of $\Gamma$ of index prime to $p$, the ring $S = \Lambda[[z]] \subseteq A_{\inf}$ with $\Lambda = W(\mathbb{F}_q)$ and $q = p^f$, a coordinate $z$, and a series $E$ with $\theta(E) = 0$. Write $p_a = \varphi^a(E)$ for $a \geq 0$. Each $p_a$ is a unit of the localized rings, and the source keeps it as a unit $u_a$. The chart has a ramification index $e$ and a residue degree $f$. The *different bound* $d$ is $0$ if $e = 1$ and $v_p(e) + 1$ if $e \neq 1$. The chart is *unramified* if $E = z + p$, $e = 1$ and $d = 0$.

Write $\tau = [\varepsilon^{1/p}] - 1$ and $\delta = z\tau$, as in [the ring $A_{\inf}$ and the map $\theta$](/chapter/period-rings/). The *letters* are the units of $\mathbb{F}_q$. For a letter $i$ and $a \geq 0$, the letter $i^{(-a)}$ is the one whose $p^a$-th power is $i$; the source calls it `i.stepBack a`. The map $i \mapsto i^p$ is the Frobenius of letters.

A jump lattice $L$ with coefficients $\mathcal{O}$, its jump sets $J_i$, its forms, the forms of type $u$ at $i$, the modules $M$ and $N$, the localization $N_{\mathrm{loc}}$ of $N$ at all $p_a$, and its $A_{\inf}$-span $A_{\inf} N_{\mathrm{loc}}$ are defined in [jump lattices and Kisin modules](/chapter/kisin-frames/#jump-lattices-and-kisin-modules). The frame theorem, $\tau^{a} (A_{\inf} \otimes L) \subseteq M$ and $\tau^a M \subseteq A_{\inf} \otimes L$ with $a$ the jump bound, is in [the frame theorem](/chapter/kisin-frames/#the-frame-theorem). For $a \geq 0$ and a form $\mu$, the *value at $p_a$* of $x$ is $\mu(\varphi^{-a} x) \in B_{\mathrm{dR}}$. Write $\mathrm{Fil}^n = t^n B_{\mathrm{dR}}^+$ ([the rings $B_{\max}$ and $B_{\mathrm{dR}}$](/chapter/period-rings/)). The value field $\mathcal{K}_a$ is the subfield of $B_{\mathrm{dR}}$ of [values in $B_{\mathrm{dR}}$](/chapter/kisin-frames/#jump-lattices-and-kisin-modules). The value at $p_a$ is in $\mathrm{Fil}^1$ if and only if $p_a$ divides the element; this is the link between orders and divisibility.

### The model case

Let the chart be unramified with $f = 1$, so $S = \mathbb{Z}_p[[z]]$, $E = z + p$, $d = 0$ and there is one letter. Let $L = \mathbb{Z}_p$ with the trivial action and the jump set $\{0\}$. Then $M = A_{\inf} \otimes L$ and $N = S \otimes L$. An element $x = r \otimes 1$ has order at least $c$ at $p_a$ if and only if $\varphi^{-a}(r) \in \mathrm{Fil}^c$, that is, if and only if $p_a^c$ divides $r$. The standard orders at level $l$ ask for order $0$ at $p_a$ for $a < l$ and order $-u$ on the jump $u$ for $a \geq l$. Here $u = 0$, so all the orders are $0$, and the standard lattice is $A_{\inf} \otimes L = \varphi^l(M)$, as the theorem of [Hodge expansions](/chapter/exponent-lattices/#hodge-expansions) says. A depth step at $p_0$ costs $v_p(n)$: for $n$ prime to $p$ it is free. This chapter returns to the model case in each section.

### What the chapter uses

From Volume 7 the chapter uses the Kummer charts, the forms of a type, the Kisin modules and the frame theorem ([Kisin frames](/chapter/kisin-frames/)), and the rings $A_{\inf}$, $B_{\mathrm{dR}}^+$ and their filtration ([period rings](/chapter/period-rings/)). It uses crystalline cocycles and the Tate twist only in the pairing lemma. It also uses the Legendre formula $v_p(n!) = \sum_{j \geq 1} \lfloor n/p^j \rfloor$ and the lifting of the exponent for $p$-adic valuations. It uses nothing from the other chapters of this volume. The chapter [tied Selmer groups](/chapter/tied-selmer-groups/) is not used here.

### The sketch

Section 2 defines the cost and the depth step, and proves that a depth step exists for every $n \neq 0$. Section 3 defines the lattices with prescribed orders, proves the gap rule and the other rules, and proves the depth lemma. Section 4 identifies the standard lattices with $\varphi^l(M)$ and proves the rules of Hodge expansions. Section 5 defines the sides of a pairing and proves the pairing lemma. Section 6 defines lift ideals and proves the three cokernel killers. Section 7 builds the side points. Section 8 proves the existence of tame charts and the cokernel killer for tame charts. Section 9 has exercises and the notes.

The order of the files is the order of the sections. No file of this chapter imports a file of a later chapter of the volume. The imports are: exponent lattices from the frame theorem of Volume 7; Hodge expansions from exponent lattices and a file on matrix norms; the cup product bound from Hodge expansions; side points and tame charts from the cup product bound.

### The status

The source claims all the results of this chapter with full Lean proofs. The chapter states what Lean states. Where the source chooses an object by choice, or where a constant can be $0$, a remark says so. Finding F-088 of the notes touches the unramified cokernel killer of Section 6, which needs $p \geq 5$; the notes section discusses it.
