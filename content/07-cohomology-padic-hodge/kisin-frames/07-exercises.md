---
title: Exercises
lean:
  - Lib/PadicHodge/Kisin/FrameTheorem.lean
  - Lib/PadicHodge/Limit/CrystallineLimit.lean
  - Lib/PadicHodge/Limit/TraceLimit.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

The exercises use the notation of the previous sections. Each one has a hint. Some ask for a proof on paper, and some ask the reader to compare a statement in the source with a classical statement.

**Exercise 1.** Let $k$ be the unramified chart of the section on charts, with $\theta(z) = -p$ and $E = z + p$. Show that $E$ is not divisible by $p$ in $A_{\inf}$, and that $\theta(E) = 0$. Then show that $E$ is a unit in $W(C^\flat)$.

*Hint.* Reduce modulo $p$: the image of $E$ in $A_{\inf}/p = \mathcal{O}_{C^\flat}$ is the image of $z$, which is not $0$. For the last claim, use that $W(C^\flat)$ is a complete discrete valuation ring with uniformizer $p$, so an element not divisible by $p$ is a unit.

**Exercise 2.** Let $L$ be a jump lattice, and let $a$ be its jump bound. Use properties (f) and (g) of the frame theorem to show that $\tau^{2a}(A_{\inf} \otimes L) \subseteq \tau^a M \subseteq A_{\inf} \otimes L$. Deduce that $M = A_{\inf} \otimes L$ when $a = 0$.

*Hint.* Apply (g) and then multiply by $\tau^a$ for the first inclusion. The second inclusion is (f). For $a = 0$, both inclusions are equalities.

**Exercise 3.** Show that the jump bound of a jump lattice $L$ is at most $h$ when all jumps of $L$ over $\Gamma'$ lie in $[0, h]$. Give an example where it is strictly smaller than the width of an interval that contains the jumps.

*Hint.* The jump bound is the least $a$ with all jumps in $[-a, a]$, see `New.Lift.KummerChart.JumpLattice.jumpBound`. For the example, take jumps in $[-1, 1]$: the width is $2$ and the bound is $1$.

**Exercise 4.** Let $g \in \Gamma$ satisfy $g \Gamma' g^{-1} \subseteq \Gamma'$. Show from the definition of forms that $\mu \circ g$ is a form when $\mu$ is a form. Here $(\mu \circ g)(y) = g^{-1}\mu(gy)$.

*Hint.* For $\gamma \in \Gamma'$, write $g\gamma = (g \gamma g^{-1})g$ and use the equivariance of $\mu$ under $g\gamma g^{-1} \in \Gamma'$. Compare your proof with `New.Lift.KummerChart.JumpLattice.conjForm_mem_forms`.

**Exercise 5.** Let $F$, $s \in B_{\mathrm{dR}}$, $x$, $d$, $r$, $t$ and a unit $w$ satisfy $Fx = s$, $F = (gF)w$, $gF - F = dr$ and $gs - s = dt$. Show that $F^2(gx - x) = w(Ft - rs)d$.

*Hint.* Apply $g$ to $Fx = s$ to get $(gF)(gx) = s + dt$. With $F = (gF)w$ this gives $F \cdot gx = w(s + dt)$, so $F^2 \cdot gx = wF(s + dt)$. Also $F^2 x = Fs = w(gF)s = w(F + dr)s$. Subtract. This is the computation in `New.Lift.KummerChart.JumpLattice.pow_smul_gal_sub_mem_span_of_dvd`.

**Exercise 6.** Explain the order of quantifiers in the uniform period bound. Which of these does the element $a$ depend on: the group $\Gamma$, the bound $h$, the lattice $T$, its rank, its basis $e$, the representation $\rho$? Why would a weaker statement, with $a$ chosen after $\rho$, not suffice for the limit theorem?

*Hint.* Read the statement of `New.Lift.uniform_period_bound`: the existential on $a$ comes before the universal on $T$. In the proof of the limit theorem, the same $\delta$ must serve every $T'_k$, and the number of the $T'_k$ is infinite.

**Exercise 7.** Let $r$ be a trace limit of the $\rho_{\eta, i}$ along a nontrivial filter, and let $\ell$ be a unit at $A$. Assume that $Q$ kills $s$ for every $\rho_{\eta,i}$, with $Q$ of degree less than $n$, and that the convergence of traces holds for every coefficient of $Q$. Show that the conclusion of `New.GaloisRep.IsTraceLimit.polyKillsAt` with $P = Q$ gives $Q(r(s)) = 0$.

*Hint.* Take $Q_{\eta, i} = Q$ for all $\eta, i$. The first clause of `New.GaloisRep.PolyKillsAt` is the equation $Q(r(s)) = 0$ when $\ell$ is a unit at $A$. The hypothesis on coefficients says that $\sum_i a_{\eta,i}\, Q_l\, \mathrm{tr}\, \rho_{\eta,i}$ converges uniformly to $Q_l\, \mathrm{tr}\, r$, which follows from the convergence of traces when $Q_l$ is a constant.

**Exercise 8.** Compare the frame theorem with Kisin's theorem. List the parts of Kisin's theorem that the frame theorem states, and the parts that it does not state.

*Hint.* The frame theorem gives a free $S$-module $N$ with $A_{\inf} N = M$, comparisons with $A_{\inf} \otimes L$ up to $\tau^a$, and $E_0^a \varphi(N) \subseteq N$. It does not give the finite-height inclusion $E^n N \subseteq S \varphi(N)$, full faithfulness, or an equivalence of categories. See the docstring of `New.Lift.KummerChart.JumpLattice.frame_theorem`.

## Notes and references

The classical theory of Kisin modules is in M. Kisin, Crystalline representations and F-crystals, in Algebraic Geometry and Number Theory, Progr. Math. 253 (2006), 459-496. The source cites its Lemma 1.2.6 for Dwork's trick in the radius lemma. The version over $A_{\inf}$ is in B. Bhatt, M. Morrow and P. Scholze, Integral $p$-adic Hodge theory, Publ. Math. IHÉS 128 (2018), 219-397, section 4. The source compares `New.Lift.KummerChart.JumpLattice.saturateBy_tau_span_kisinModule` with Lemma 4.26 there. The docstrings in `Lib/PadicHodge/Kisin` also cite Wach, Bull. SMF 124 (1996) 375-400, and Berger, Compositio Math. 140 (2004), for related constructions.

For limits of crystalline representations, the source cites L. Berger, Limites de représentations cristallines, Compositio Math. 140 (2004) 1473-1498, and T. Liu, Torsion $p$-adic Galois representations and a conjecture of Fontaine, Ann. Sci. ENS 40 (2007) 633-674. For the passage from traces to the image of the group ring, it cites P. Wake and C. Wang-Erickson, Deformation conditions for pseudorepresentations, Forum Math. Sigma 7 (2019).

The source differs from these texts in four ways. First, it uses Colmez's $B_{\max}$ in place of Fontaine's $B_{\mathrm{cris}}$, and it does not formalize the comparison of the two rings. Second, it does not use Kedlaya's slope theory or étale $\varphi$-modules. It works with explicit period matrices and with linear retractions of $A_{\inf}$ onto the image $S$ of a chart. Third, the frame theorem proves $E_0^a \varphi(N) \subseteq N$ but not finite $E$-height, and it states no equivalence of categories. Fourth, the limit theorem is stated with traces on the group ring $\mathbb{Z}_p[G]$, and the families of approximating representations can have any finite size and any dimension. In place of the Weil-Deligne representation, the local conditions use `New.Period.linearFrob`.

The chapter [Period rings and crystalline representations](/chapter/period-rings/) defines the rings, the jumps and the radius lemma. The chapter [The comparison theorems on test objects](/chapter/comparison-theorems/) uses the same rings. The frame theorem is used in `New/Congruences/Lifting` and in `New/Congruences/LocalLoss/LocalLattices`. The trace limit structure is used in `Lib/GaloisRep/Main`, in the files `AllRanks`, `SplitCase` and `CuspidalTypes`.

The source claims that all results in this chapter compile with no `sorry`. Lean accepts them, if the reported checks hold. This chapter does not claim more than that, and it does not claim that GRH is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
