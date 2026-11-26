---
title: What the chapter proves
lean:
  - New/Spanning/RemainingTerms/Size.lean
  - New/Spanning/RemainingTerms/Sum.lean
decls:
  - New.Filling.secondMoment
  - New.Filling.linkSecondMoment
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter is part of layer 4 of the proof of Theorem B. Layer 3 writes the Hilbert-Schmidt norms of the translates of a Poincaré operator as sums of squared blocks $\mathcal{A}_T(c, s, c')$. A block is a sum of amplitudes over the terms $\gamma$ of a set $T$ that lie over the block. Layer 4 bounds these blocks. [The chapter on the anatomy of a term](/chapter/anatomy-of-a-term/) gives the data of one term. This chapter bounds the blocks of the remaining terms $\Gamma^*$, and it reduces the terms of the top cell to one link at a time. [The chapter on the main term](/chapter/main-term/) then bounds the sum over one link. The place of the chapter in the whole argument is shown in [the theorem and the plan](/chapter/theorem-and-plan/), and its place in the proof of Theorem B in [Theorem B and its plan](/chapter/theorem-b-plan/#unfolding-and-bounds).

### The two second moments

Fix admissible data $S$ over a CM field $E$ with a primitive root of unity of order $5040$. Write $\nu$ for the covolume `unipotentCovolume` of the unipotent group of a class. It is positive and does not depend on the class.

**Definition (Second moment of a family of blocks).** Let $A(c, s, c')$ be a family of vectors in a normed group, indexed by two classes $c, c'$ and a reduction $s \in \bar G$, and let $\Omega \subset \bar G$. The second moment of $A$ over $\Omega$ is

$$\mathsf{E}(A, \Omega) = \sum_{c, c'}\ \sum_{s \in \Omega} \frac{\|A(c, s, c')\|^2}{\nu^2}.$$

Lean: `New.Filling.secondMoment` (New/Spanning/RemainingTerms/Size.lean).

**Definition (Second moment link by link).** Let $T$ be a set of rational points of $G$ and $\Omega \subset \bar G$. Then

$$\mathsf{L}(T, \Omega) = \sum_{c, c'}\ \sum_{s \in \Omega}\ \sum_{\Lambda} \|\mathcal{A}^\flat_{T \cap \mathrm{link}^{-1}(\Lambda)}(c, s, c')\|^2,$$

where $\Lambda$ runs over all submodules of $E^{k+1} \times E^{k+1}$ and $\mathcal{A}^\flat$ is the block for the cut Bessel functions. The sum is taken in $[0, \infty]$.

Lean: `New.Filling.linkSecondMoment` (New/Spanning/RemainingTerms/Size.lean).

**Remark (Formalization).** The number $\mathsf{L}(T, \Omega)$ lies in $[0, \infty]$ and is not divided by $\nu^2$. So the hypothesis of the first theorem below has the factor $\nu^2$ on its right side. The sum over $\Lambda$ is a sum over an uncountable index set, but only countably many links occur, since there are countably many rational points. A sum of nonnegative terms in $[0, \infty]$ always has a value, so no convergence question arises. The number $\mathsf{E}(A, \Omega)$ is a real number: the index sets are finite.

### The two theorems

The chapter proves two theorems. They are stated in full and proved in [the count and the sum](/chapter/remaining-terms/#the-count-and-the-sum).

The first theorem is the one that [Theorem B and its plan](/chapter/theorem-b-plan/#unfolding-and-bounds) uses. Let $w \geq 0$. If the terms $\gamma$ with $\mathsf{g}(\gamma) \neq 0$, taken link by link, satisfy $\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq w\nu^2$, then

$$\mathsf{E}(\mathcal{A}^\flat_{\Gamma^*}, \Omega) \leq w + b^{-kf}\mathcal{D}_{\mathrm{id}}.$$

So the remaining terms cost the main estimate only a factor $1 + b^{-kf}$ on top of $\mathcal{D}_{\mathrm{id}}$, once the sum over one link is known.

The second theorem gives a crude bound for the sum over one link. If $z \neq 0$ and every $s \in \Omega$ has a meet norm at least $z$, then $\mathsf{L}(\{\mathsf{g} \neq 0\}, \Omega) \leq (b^{2f}/z)^k\mathcal{D}_{\mathrm{main}}\nu^2$. The meet norm of $s$ is the norm of the product of the chosen places at which, modulo the place, the span of the frame and its image under $s$ share a nonzero vector.

The set $\Gamma^*$ (`remainingTerms`) is defined in [the chapter on Poincaré series](/chapter/poincare-series/): it consists of the $\gamma$ with $\mathsf{g}(\gamma) \neq 0$, and of the $\gamma$ with $\mathsf{g}(\gamma) = 0$ whose characters agree and with $\gamma A \neq A$. This chapter uses only two facts about it. It is stable under $\gamma \mapsto u^{-1}\gamma u'$ for rational $u, u' \in \mathsf{U}$, and it contains no term of cell rank $0$. Both are proved in that chapter ([Lemma](/decl/New.Filling.isStable_remainingTerms/) and [Lemma](/decl/New.NormOnePairOccursFrom.notMem_remainingTerms/)).

### What the chapter uses

- The data of a term, its cell rank $j$, its gauges, its lattices and the size $\operatorname{orbitBound}$, from [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/). The notation of its [first section](/chapter/anatomy-of-a-term/#what-the-chapter-proves) is used here without change.
- The integral of the weight at one real place, the lattice of a link and the count of the frames over a lattice, from [the chapter on frame counts](/chapter/frame-counts/), which is being written now.
- The blocks, the stable sets, the cutoffs of the classes and the set $\Gamma^*$, from [the chapter on Poincaré series](/chapter/poincare-series/), which is being written now.
- The bound of the tail $W - W^\flat$ and the open cell bound for one pairing, from [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/).
- Minkowski's second theorem over a number field, in [the chapter on reduction theory](/chapter/reduction-theory/) of Volume 4. It enters through Siegel's lemma and the sums over sublattices of [the chapter on the anatomy of a term](/chapter/anatomy-of-a-term/#siegels-lemma-and-the-gauges-of-a-term).

No file of this chapter imports a file that a later chapter of Volume 10 explains.

### A sketch

The proof has four steps.

*Step 1: one block.* Fix a block $(c, s, c')$ and a stable set $T \subset \Gamma^*$. Split $T$ into orbits under $\mathsf{U}^0_c \times \mathsf{U}^0_{c'}$, the rational unipotent elements of the classes that fix the frame. On one orbit of cell rank $j \geq 1$ the sum of the absolute amplitudes is at most $\nu$ times the size $\operatorname{orbitBound}(j, x)$, for the gauge $x$ of the orbit. Two methods give this. If $\operatorname{termDiscNorm}$ is large, the open cell bound of [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/) bounds each term. Otherwise Schur's test with a weight from the volumes of the frames bounds the whole orbit. Only near orbits contribute. This is [Schur's test](/chapter/remaining-terms/#schurs-test) and [the size of a block](/chapter/remaining-terms/#the-size-of-a-block).

*Step 2: pairs.* Square the bound of Step 1. The square of a block is at most a sum over pairs $(\gamma, \gamma')$ of near representatives, of $\nu^2$ times the product of their sizes. Split the pairs into those with the same link and those with different links. The first kind is kept as it is, and gives $\mathsf{L}$. The second kind must be summed.

*Step 3: the gain.* A pair $(\gamma, \gamma')$ of near terms over one block has a common lattice $L_{12}$ in $X_0$, with a discriminant $d$ and a corank $l$. The congruence $\gamma \equiv \gamma' \pmod M$, which holds since both have the reduction $s$, forces $d$ to be small against the gauges: $d^2 \leq (2/M)^{2c^+f}$ times the product of the gauges, where $c^+$ is the codimension of the meet of the links. This is the gain. Its proof needs the link vectors and a splitting of the link lattices. This is [link vectors and the splitting](/chapter/remaining-terms/#link-vectors-and-the-splitting) and [the gain](/chapter/remaining-terms/#the-gain).

*Step 4: the count.* Sum $d^{-k}$ over the lattices of corank $l$ in $X_0$ of bounded discriminant, and over the pairs that give one lattice. The first sum is at most $\tau^{l+1}$ per class, by [lattices of given corank](/chapter/remaining-terms/#lattices-of-given-corank). The second is at most $\tau$ by the frame count. The gain pays for both losses. This is [the count and the sum](/chapter/remaining-terms/#the-count-and-the-sum).

The unit of loss is $\tau = b^{kf/4}$. Every loss in the chapter is a fixed power of $\tau$, or a power $b^e$ with $e \leq 10^5n^9f$, which is at most $\tau$ by [Lemma](/decl/New.Filling.pow_le_tailScale/). The gain is a power $(M/2)^{-ikf}$ with $M \geq b^{19}$. Since $(b^{19}/2)^{kf} \geq \tau^{72}$, one unit of gain pays for any fixed number of units of loss.
