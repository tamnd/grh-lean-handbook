---
title: What the chapter proves
lean:
  - New/Congruences/Lifting/SafeMoves.lean
  - New/Congruences/Lifting/LongGap.lean
  - New/Congruences/Lifting/CutExponentBounds.lean
  - New/Congruences/Lifting/DeepPoints.lean
  - New/Congruences/Lifting/FewLowJumps.lean
  - New/Congruences/Lifting/CupOrthogonalityBounds.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

Let $\Gamma$ be a group with an open embedding into $G_p$, and let $Y$, $Y'$ be crystalline lattices with a pairing $P$ into $\mathbb{Z}/p^m(1)$. Two crystalline cocycles $a$ of $Y$ and $a'$ of $Y'$ have a cup product, a class in $H^2(\Gamma, \overline{\mathbb{Q}}_p^\times)$. Local Tate duality says that the pairing of crystalline classes is "almost" orthogonal ([local duality](/chapter/local-duality/)). This chapter makes "almost" exact. It proves that $p^N$ times the cup product is a coboundary, with an explicit $N$ in terms of the jumps of $Y$ and $Y'$, the ramification of a Kummer chart, and the pattern of the jumps along the Frobenius orbits of the letters.

The chapter proves four kinds of results.

1. *The walk.* If each Frobenius orbit of letters has marked letters, the *cuts*, and at each cut there are deep points and a *stop*, then the cup product is a scaled coboundary. This is a statement about orders and depths only.
2. *Cut schemes.* For two patterns of jumps, the sparse thick pattern and an arbitrary pattern on an unramified chart, the chapter chooses the cuts, builds the points, and finds the stops. This gives explicit exponents $10^3(\delta + (J+1)M)$ and $10^4(K + \log_p(2(b+M)))$.
3. *Small and few jumps.* If the jumps avoid a window below $0$, the cup product is a scaled coboundary with a small exponent. If only a few jumps are low, the cocycles that fail lie in a sublattice of bounded colength.
4. *Lattices of cocycles.* The results pass from single cocycles to the lattice $Z_f(Y)$ of all crystalline cocycles. The outputs are bounds for the *dual defect* and *cup exponents* $p^N Z_f(Y) \subseteq Z_f(Y)^{\perp}$.

The four outputs are `dualDefect_eq_zero_and_dualDefect_le`, `hasCupExponent_any_pattern`, `hasCupExponent_sparse_thick` and `hasCupExponent_of_isTameType`. They are stated in full in [the last section](/chapter/cup-products/#from-sides-to-lattices).

### Its place in the plan

The plan of the argument is in [the theorem and the plan](/chapter/theorem-and-plan/). Volume 12 proves the existence of regular families, and its chain of proof is in [regular families: the plan](/chapter/regular-families-plan/#the-chain-of-the-proof). Step 4 of the chain is the local loss above $\ell$. It has three chapters: [exponent lattices and Kummer charts](/chapter/exponent-lattices/), this chapter, and [the local loss](/chapter/local-loss/). The local loss chapter applies the four outputs with $p = \ell$ to the lattices of the Galois representations of the argument. Volume 2 explains the source of the sparse thick pattern: [progression-free sets](/chapter/progression-free-sets/) shows that no three $b$-letters follow one another at short distances.

### Notation

The notation is that of [exponent lattices](/chapter/exponent-lattices/#what-the-chapter-proves). Here is a short list.

- $k$ is a Kummer chart with ramification index $e$, residue degree $f$, the series $E$ and the different bound $d$. It is *unramified* if $E = z + p$, $e = 1$ and $d = 0$. $\Gamma' \subseteq \Gamma$ has index prime to $p$.
- Letters are the units of $\mathbb{F}_{p^f}$. The letter $i^{(-a)}$ lies $a$ steps before $i$: its $p^a$-th power is $i$. The *level* $a$ stands for $p_a = \varphi^a(E)$.
- An *order system* is a function $o(a, u)$ of a level $a$ and a jump $u$. $L_i(o)$ is the lattice of the elements at the letter $i$ whose values at $p_a$ on a form of type $u$ lie in $\mathrm{Fil}^{o(a,u)}$. $\mathrm{Inv}(L)$ is the set of $x$ with $gx - x \in L$ for all $g \in \Gamma'$.
- $\rho_t(a, u) = -u + t[a = 0]$, with $[\cdot]$ the indicator. The standard orders of level $l$ are $c^{\mathrm{std}}_l(a, u) = 0$ for $a < l$ and $-u$ for $a \geq l$. The shift $\mathrm{sh}_l(n, o)$ is $n$ below $l$ and $o(a - l, u)$ from $l$ on. $\mathrm{imp}(lo, o)$ is the improved system of [the depth lemma](/chapter/exponent-lattices/#invariance-and-the-depth-lemma).
- A *side* $S$ has a lattice $Y$, a lattice $C$ and a map $\alpha : C \to Z_f(Y)$. $K_i(o)$ is the set of vectors over $0$ with orders $o$. $\mathrm{Pts}_i(c, e, o, o')$ is the set of points over $p^e$ times the constant of $c$ at $i$, with orders $o$ and depth $o'$ ([side points](/chapter/exponent-lattices/#side-points)).
- For a pairing $P$ of $S$ and $S'$, the *Tate dual side* $T$ has the lattice $\mathrm{Hom}(Y \otimes Y', \mathcal{O}(1))$, the parameter lattice $\mathcal{O}$ and the jumps $\{0\} \cup \{-u-u'-1\}$. "$p^\kappa E^t$ kills $T$ at $i$" means that $p^\kappa E^t$ kills the cokernel of $T$ at $i$ ([cokernel killers](/chapter/exponent-lattices/#lift-ideals-and-cokernel-killers)).
- $c_a(n) = v_p(n) + d + 3a$ is the cost of a depth step, with $v_p(0) = 0$.

The chapter uses one result of the last chapter many times. We state it here in one line. **The pairing lemma** ([exponent lattices](/chapter/exponent-lattices/#pairing-sides-and-the-pairing-lemma)): if $x, w$ lie over $p^{e_1}c$ and $x', w'$ over $p^{e_2}c'$, the moves by $hx' - x'$ with $x$ at rest are safe with exponent $e_3$, and a safe path with exponent $e_3$ leads from $(\varphi x, \varphi x')$ through $(w, w')$ to $(x, x')$, then $(c, c')$ is a scaled cup coboundary with exponent $e$ for every $e \geq e_1 + e_2 + e_3$.

### The model case

Let the chart be unramified with $f = 1$, so there is one letter $i$ and $i^{(-a)} = i$. Let $Y = \mathbb{Z}_p(1)$ with the jump set $\{-1, 0\}$, let $Y' = \mathbb{Z}_p$ with the trivial action and the jump set $\{0\}$, and let $P$ be the product into $\mathbb{Z}/p^m(1)$. Then the Tate dual side has the jumps $\{0\} \cup \{-u-u'-1\} = \{-1, 0\}$. The cuts are all the letters, so $l = 1$. A standard point at $i$ has orders $\rho_{-\eta}$, a pole of order at most $\eta$ at $E$, and depth $-u + t + \eta$ at level $0$. The walk asks for two safe moves at each letter: one from $\varphi x$ to a stop, and one from the stop to $x$. In this case each move asks that two orders and one depth add up to a positive number. Section 2 does this computation in general.

### What the chapter uses

From [exponent lattices](/chapter/exponent-lattices/) the chapter uses the pairing lemma, the cokernel killers, the depth operators and the side points. From Volume 7 it uses the Kummer charts and the frame theorem ([Kisin frames](/chapter/kisin-frames/)) and relative lengths ([Fitting ideals](/chapter/fitting-ideals/#discrete-valuation-rings-and-relative-lengths)). From Volume 3 it uses crystalline cocycles and the cup orthogonal functions and the dual defect ([local duality](/chapter/local-duality/#duality-for-crystalline-cocycles)). From Volume 2 it uses the Legendre formula $v_p(n!) = \sum_{j \geq 1}\lfloor n/p^j\rfloor$.

No file of the chapter imports a file of a later chapter of the volume. The imports are: safe moves from side points; the long gap from safe moves; cut exponent bounds from the long gap; deep points from safe moves; few low jumps from deep points; the orthogonality bounds from cut exponent bounds and few low jumps.

### The sketch

Section 2 turns orders into safe moves and proves the walk. Section 3 builds deep points over a long gap of the Frobenius orbit, with a Taylor expansion in $E$. Section 4 chooses the cuts for the sparse thick pattern and for an arbitrary pattern, and proves the two cut theorems. Section 5 treats sides whose jumps avoid a window below $0$. Section 6 proves that if few jumps are low, the bad cocycles have bounded colength. Section 7 passes to lattices and states the four outputs. Section 8 has exercises and notes.

The idea of the walk is simple. Each side wants a lift of its cocycle to $W(C^\flat)$ that Frobenius almost fixes. One cannot move both lifts at once. So one side moves first, to a stop, while the other rests; then the other side moves; then the first side goes on to its point. A move is safe when the orders of the moved part and the depth of the point at rest add up to the bound that a cokernel killer of $T$ allows. Large jumps of one sign make one side "down" and the other "up", and then the side that is down is a stop.

### The status

The source claims all the results of this chapter with full Lean proofs. The chapter states what Lean states. Lean accepts them, if the reported checks hold. Finding F-088 says that the unramified cokernel killer needs $p \geq 5$. In this chapter it enters only through the killing cuts of the unramified kind ($p \geq 5$) and the arbitrary pattern ($p \geq 7$). The thin cuts, the sparse thick theorem with a constant sign, the theorems of Sections 5 and 6 and the tame theorem have no such hypothesis. The choice of theorem for each prime is made in [the local loss](/chapter/local-loss/). Finding F-104 says that the source cites preprints of 2026 for this part. The handbook does not rely on them.
