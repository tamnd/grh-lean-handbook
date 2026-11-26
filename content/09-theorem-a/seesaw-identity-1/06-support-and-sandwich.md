---
title: The support of the stages
lean:
  - New/UpperBound/Seesaw/Sandwich.lean
  - New/UpperBound/Seesaw/UnfoldingStages.lean
decls:
  - New.Grading.LatticeSplitsAt
  - New.Grading.smul_latticeMinus_le_of_map_latticePlus
  - New.Grading.SpansLattice.hasLatticeBounds_or_latticeSplitsAt
  - New.Grading.LatticeSplitsAt.conj_scalarFin_mem
  - New.Data.unfoldStage_eq_zero_of_scalingGenerator
  - New.Data.unfoldStage_eq_zero_of_latticeSplitsAt
  - New.Data.hasLatticeBounds_of_unfoldStage_ne_zero
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The support of the stages

The coset sum of Section 7 runs over the classes of finite points $x$ with $\mathcal{W}_k(a, x) \neq 0$. This section shows that these points have lattices between two fixed lattices. The bound is proved by induction on $k$: the frequency theorem of Section 4 carries a bound on one space to the next, and the ramification of $\varphi$ at the places above $\pi_N$ removes the one case where the induction fails.

For a grading $\mathsf{Y}$ of $V$ and a finite point $x$, write $\Lambda'$ for the lattice of $x$ and $\Lambda$ for the lattice of $1$. Write $\Lambda'^{+}$ for the projection of $\Lambda'$ to $X^\perp$, the span of the string, and $\Lambda'^{-} = \Lambda' \cap X^\perp$, so $\Lambda'^- \subseteq \Lambda'^+$. Let $q$ be a finite idele. The pair of bounds

$$\bar q^{\,k}\Lambda^- \subseteq \Lambda'^-, \qquad q^k \Lambda'^- \subseteq \Lambda^-$$

is the structure `New.Grading.HasLatticeBounds`, with the fields `lower` and `upper`. The orbit of $x$ is bounded if some translate $r x$ by the finite Bessel group has a graded lattice with these bounds (`New.Grading.HasBoundedOrbit`). Both are defined in the file on [point lattices](/chapter/bessel-periods/) of Volume 6.

**Definition (Splitting at a place).** The lattice of $x$ splits along $X$ at the finite place $w$ if the component at $w$ of $\Lambda'^+$ lies in $\Lambda'^-$. Then the two are equal at $w$, and $\Lambda'_w$ is the direct sum of its parts in $X$ and in $X^\perp$.

Lean: `New.Grading.LatticeSplitsAt`.

### The sandwich

**Lemma (The lower bound moves to the next space).** Let $\mathsf{Y}'$ be the next grading, on $V'$, with lattices $M$ of $1$ and $M'$ of a point $x'$. Let $a$ and $q$ be finite ideles with

$$\mathrm{sh}\,\Lambda^+ = a\,M^-, \qquad (\bar q / a)\,\mathrm{sh}\,\Lambda'^+ \subseteq M'^-.$$

Then the upper bound $q^k \Lambda'^- \subseteq \Lambda^-$ gives the lower bound $\bar q^{\,k+1} M^- \subseteq M'^-$.

Lean: `New.Grading.smul_latticeMinus_le_of_map_latticePlus`.

*Proof.* Let $m \in M^-$. By the first hypothesis $a m = \mathrm{sh}\, z$ with $z \in \Lambda^+$. By duality the upper bound gives $\bar q^{\,k}\Lambda^+ \subseteq \Lambda'^+$ (Lean: `New.Grading.star_smul_latticePlus_le`). Hence $\bar q^{\,k} z \in \Lambda'^+$, and

$$\bar q^{\,k+1} m = (\bar q/a)\,\mathrm{sh}(\bar q^{\,k} z) \in M'^-$$

by the second hypothesis. $\square$

In the tower the first hypothesis is $\mathrm{sh}\,\Lambda_k^+ = \mathfrak a\,\Lambda_{k+1}^-$ of Section 3 (Lean: `New.Data.map_stringMapFin_latticePlus_gradingY`). The second hypothesis is the frequency theorem of Section 4, with $q = $ `New.Data.twistIdele` $\vartheta$, an idele that generates the product of the places of $\vartheta.Q$.

The other half of the induction gets the upper bound from the lower bound by duality. This fails in one case.

**Proposition (Both bounds, or a split).** Let the lattice of $1$ for a grading over $X \oplus \mathrm{Unit}$ have the glued basis of Section 3 with parameters $a$, $\pi$, $u$, where $N = \pi\bar\pi$ and $\pi$ is a uniformizer at the places of a set $P$ that contains no conjugate pair. Let $q$ be a unit at the places of $P$ and their conjugates, and suppose $\bar q^{\,k}\Lambda^- \subseteq \Lambda'^-$. Then either both bounds hold, or $s$ is odd and the lattice of $x$ splits at some $w \in P$.

Lean: `New.Grading.SpansLattice.hasLatticeBounds_or_latticeSplitsAt`.

*Proof.* Duality gives $q^k \Lambda'^+ \subseteq \Lambda^+$. Suppose the upper bound fails: there is $y \in \Lambda'^-$ with $q^k y \notin \Lambda^-$. As $q^k y \in \Lambda^+$, and $\Lambda^+/\Lambda^-$ is the quotient computed in Section 3, the vector $q^k y$ generates $\Lambda^+$ over $\Lambda^-$ at some place $w$ above $N$, and this quotient is nonzero only for odd $s$. At $w$, with $q$ a unit there,

$$\Lambda'^+_w \subseteq q^{-k}\Lambda^+_w = q^{-k}\Lambda^-_w + \hat{\mathcal O}_w\, y \subseteq \Lambda'^-_w$$

by the lower bound (Lean: `New.Grading.latticeSplitsAt_of_generates`). If $w \notin P$ then $\bar w \in P$, and the split passes to the conjugate place. $\square$

### Ramification kills the split case

**Lemma (Scalings preserve a split lattice).** If the lattice of $x$ splits along $X$ at $w \neq \bar w$, and $z$ is an integral unitary adele equal to $1$ off $w$ and $\bar w$, then $x^{-1}\,\iota(z)\,x$ is integral and trivial off $w$, $\bar w$. Here $\iota(z)$ scales $X$ by $z$ and fixes the string.

Lean: `New.Grading.LatticeSplitsAt.conj_scalarFin_mem`.

*Proof.* In rational coordinates $\iota(z)\,y = y + (z - 1)(y - p\,y)$, with $p$ the projection to $X^\perp$. At $w$ and $\bar w$ the split gives $y - p\,y \in \Lambda'$ for $y \in \Lambda'$, and off these places $z - 1 = 0$. $\square$

**Theorem (Vanishing at split points).** Let $\varphi$ be ramified: for each place $w$ of $\pi_N$, the sum over $0 \leq i < N - 1$ of the translates of $\varphi$ by $z_w^i$ is $0$, where $z_w$ is the chosen scaling. Let $\gamma$ be in the Bessel group of $Y_{2j+2}$ and $a$ an archimedean point.

1. If $x^{-1}\iota(z_w)x$ lies in the level $J_{2j+2}(\vartheta)$, then $\mathcal{W}_{2j+2}(\gamma(a, x)) = 0$.
2. If the lattice of $x$ splits along $X_{2j+2}$ at a place $w$ of $\pi_N$, then $\mathcal{W}_{2j+2}(\gamma(a, x)) = 0$.

Lean: `New.Data.unfoldStage_eq_zero_of_scalingGenerator`, `New.Data.unfoldStage_eq_zero_of_latticeSplitsAt`.

*Proof.* (1) Replace $(\xi, y)$ at the index $2j+2$ by $(a, x)$. By Section 5, $\mathcal{W}_{2j+2}(\gamma(a,x))$ is the source function of $\Theta_{j+1}\varphi$ at a form $l$ that does not depend on $\varphi$. By the invariance of the evaluated data, $(1, z_w)$ fixes the last datum, and the lifts commute with the central action. So the value does not change if $\varphi$ is translated by $z_w$, or by $z_w^i$. The mean over $i$ is the value at the sum of the translates, which is $0$, and $N - 1 \neq 0$. (2) The place $w$ is not chosen and is not in $\vartheta.Q$ (Lean: `New.Data.notMem_Q_of_mem_piNPlaces`), so the level is maximal above $w$, and the scaling lemma gives the hypothesis of (1). $\square$

**Remark (Formalization).** The chosen scaling `New.Data.scalingGenerator` is defined with `choose`. The theorem uses only its specified properties: it is integral, equal to $1$ off $w$ and $\bar w$, and of order $N - 1$ modulo $w$.

**Theorem (Support).** Let $\varphi$ be ramified, let $y_0$ lie in the chosen level, and let $k + 1 \leq 2\varrho + 1$. Suppose $\mathcal{W}_{k+1}(a, x) \neq 0$, and let $r'$ be a finite point of the Bessel group of $\mathsf{Y}_{k+1}$ such that the lattice of $r' x$ is graded. Then $r'x$ has the bounds with $q$ and $k + 1$:

$$\bar q^{\,k+1}\Lambda^- \subseteq \Lambda'^-, \qquad q^{k+1}\Lambda'^- \subseteq \Lambda^-.$$

Lean: `New.Data.hasLatticeBounds_of_unfoldStage_ne_zero`.

*Proof.* Strong induction on $k$. As $\mathcal{W}_{k+1}(a, x)$ is an integral that is not $0$, there is $\gamma$ with $\mathcal{W}_k(\gamma) \neq 0$ and a nonzero constant term at $\gamma g_k$ and $(a, x)$. The orbit of the finite part of $\gamma g_k$ is bounded with $k$: for $k = 0$ because $y_0$ is in the chosen level, which lies in the standard level (Lean: `New.Grading.SpansLattice.hasBoundedOrbit_zero`), and for $k > 0$ by the induction hypothesis, since every orbit has a graded point (Lean: `New.Grading.HasBoundedOrbit.of_forall`). The frequency theorem gives the second hypothesis of the sandwich lemma, and the sandwich lemma gives the lower bound with $k + 1$. The proposition gives both bounds, or a split at a place of $\pi_N$ with $k + 1$ even. The split case contradicts $\mathcal{W}_{k+1}(a, x) \neq 0$ by the vanishing theorem. $\square$
