---
title: Exercises and notes
lean:
  - New/Spanning/RemainingTerms/Sum.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $b \geq 2$ and $\tau = b^{kf/4}$. Show that $(b^{19}/2)^{kf} \geq \tau^{72}$. Conclude that one unit $(M/2)^{-kf}$ of gain pays for $\tau^{72}$.

*Hint.* $b^{19}/2 \geq b^{18}$ and $\tau^4 = b^{kf}$.

**Exercise 2.** In the proof of the theorem on [pairs not in one link class](/chapter/remaining-terms/#the-count-and-the-sum), the case $c^+ = 0$ takes $D = \tau^{-16}\mathcal{D}_{\mathrm{id}}$. Suppose that the second moment below the top cell were $\mathcal{D}_{\mathrm{main}}$. Show that the hypothesis $\tau^{l+6}D\eta^{-k} \leq \tau^{-10}\mathcal{D}_{\mathrm{id}}$ then fails for every $\eta \leq 1$ when $\mathcal{D}_{\mathrm{id}} > 0$.

*Hint.* $\mathcal{D}_{\mathrm{main}} \geq \tau^{44}\mathcal{D}_{\mathrm{id}}$ and $\tau \geq 1$. In this case there is no gain from the links.

**Exercise 3.** Show that the lemma on [one unit of gain](/decl/New.Filling.pow_mul_mainSecondMoment_div_le/) is false for $i = 0$ and $l = 1$ when $\mathcal{D}_{\mathrm{id}} > 0$.

*Hint.* For $i = 0$ the left side is $\tau^7\mathcal{D}_{\mathrm{main}}$.

**Exercise 4.** Let $z = 1$. Show that the second theorem gives $\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq \tau^8\mathcal{D}_{\mathrm{main}}\nu^2$ for every $\Omega$. In the proof, find the source of each factor of $\tau^8$.

*Hint.* $\tau^8 = b^{2kf}$. One factor $\tau$ is the number of coranks, $\tau^{l+2} \leq \tau^3$ comes from the count, and $\tau^4$ comes from the two sizes.

**Exercise 5.** Let $T \subset \Gamma^*$ be stable and assume that all terms of $T$ have $\mathsf{g} = 0$. Show that

$$\|\mathcal{A}^\flat_T(c, s, c')\|^2 \leq \nu^2\sum_{\gamma, \gamma'}\operatorname{termSize}(c, c', \gamma)\operatorname{termSize}(c, c', \gamma'),$$

where the sum is over all pairs of near representatives of $T$ over $(c, s, c')$.

*Hint.* Apply the [square of a block](/decl/New.Filling.enorm_amplitudeSum_sq_le/). The first sum is empty, and no pair lies in one link class.

## Notes and references

The bound of a block by a sum of sizes is a form of Schur's test, from I. Schur, *Bemerkungen zur Theorie der beschränkten Bilinearformen mit unendlich vielen Veränderlichen*, J. Reine Angew. Math. 140 (1911). The weight of the test is built from the volumes of the frames, in [Schur's test](/chapter/remaining-terms/#schurs-test).

The count of pairs by their common lattice is a lattice point count in the geometry of numbers. It enters through the sum over lattices of given corank and through the count of the frames over a lattice in [the chapter on frame counts](/chapter/frame-counts/). Siegel's lemma and Minkowski's second theorem stand behind both, as in [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/).

The second moment of a Poincaré series expands over pairs of terms that are congruent modulo the level. The source states that the removal of small cells and off diagonal terms by congruences and counts is known for Petersson type and relative trace formulas. It names, as related work, Michel, Ramakrishnan and Yang, *Bessel periods on U(2,1) × U(1,1)* (2023); Kowalski, Saha and Tsimerman, *Local spectral equidistribution for Siegel modular forms* (2012); and Blomer, *Density theorems for GL(n)* (2023). This book has not compared these citations with the statements of the source.

The file `Denominators.lean` is imported by the files of this chapter, but no result of it is used; [link vectors and the splitting](/chapter/remaining-terms/#link-vectors-and-the-splitting) states this. The plan of Theorem B says that the terms are counted by lattice points with Siegel's lemma. In the source, Siegel's lemma enters only through the height zeta function and the frame counts.

Status: drafted by a model. No person has checked this chapter against the Lean source.
