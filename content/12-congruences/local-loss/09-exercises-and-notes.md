---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Check the lemma on reindexing low jumps of [Section 5](/chapter/local-loss/#letters-and-windows-for-the-data) for $h = 2$ and $J = \{-1, 0, 0, 9\}$.

*Hint.* The interval is $[-5, 5]$. The values $-u - 1$ for $u \in [-5, 5]$ are $[-6, 4]$, so the members $-1, 0, 0$ count and $9$ does not: the left side is $3$. The right side counts $|a| \leq 8$, which is also $3$.

**Exercise 2.** Let $L$ have the single jump $c = 2$, with $t = 5$. Find the jump of $L^\vee(1)$ and check the lemma on the dual of a character.

*Hint.* The jump is $-3$, and $-3 \in [-h_2^2 - 1, 0]$ since $h_2 \geq 3t$.

**Exercise 3.** In the lemma on the crystalline exponent of [Section 6](/chapter/local-loss/#the-defect-at-a-place-above), show where $x \leq t$ is used. What fails for $x > t$?

*Hint.* Only in $\lfloor 2\lambda/(kt) \rfloor \leq 2\lambda/(kx)$. For $x > t$ it can fail, for example when $2\lambda = kt$.

**Exercise 4.** Apply the lemma on tame type from roots of [Section 7](/chapter/local-loss/#local-lattices) to $M = \{1, -1\}$, $\ell = 3$, $r = 1$, $N = 2$. Give $e'$ and $q$.

*Hint.* $e' = 3 - 1 = 2$, and $(\pm 1)^2 = 1$. The minimal polynomials are $X - 1$ and $X + 1$, so $q = X^2 - 1$ of degree $2 \leq Nr$.

**Exercise 5.** In the duality bound of [Section 8](/chapter/local-loss/#tate-duality-and-ribet-cocycles), show that the reduction of every $c \in Z_f(L)$ comes from the class.

*Hint.* Take $Y = L$, $t = \tau$ and $a = c$; $\tau$ is equivariant and $L \in \mathcal{Q}$.

## Notes and references

Crystalline cocycles $Z_f$ and their rank are as in S. Bloch and K. Kato, *L-functions and Tamagawa numbers of motives*, Grothendieck Festschrift I (1990), Section 3, which the source cites for the rank formula. The heuristic for large $\ell$ in [Section 1](/chapter/local-loss/#what-the-chapter-proves) is the theory of J.-M. Fontaine and G. Laffaille, *Construction de représentations $p$-adiques*, Ann. Sci. ENS 15 (1982). The source does not use that theory; it proves the bounds it needs from the cup product estimates of [cup products](/chapter/cup-products/). This chapter does not compare the statements of the source with these texts.

The status. All four files of the chapter have full proofs in the source, with no `sorry` and no axiom. No file of the chapter imports a file of a later chapter of Volume 12. Two results of [the denominator bound](/chapter/denominator-bound/) use the chapter; they are stated once in Section 8.

Findings of the notes (`05-findings.md`):

- F-044 says that the local chart at a place above $\ell$ is chosen. It enters this chapter through the embedding $\sigma_{w,g}$ of Section 7. Every statement holds for every choice, but the jump sets depend on it. The finding stays open.
- F-152 says that the local loss uses the sparseness of the b-places. The chapter confirms this: the lemma on sparse letters of Section 5 is the only use, through the lemma on short arcs of [progression-free sets](/chapter/progression-free-sets/), and only for $\ell \leq kt$.
- F-031 says that the crystalline loss is an opaque definition. In the source only the three lemmas of [Section 3](/chapter/local-loss/#the-crystalline-loss-and-the-sizes) read its value.

The notes have small errors. Research note f-congr, Section 6, names the defect sum over the places above $\ell$ as the main output of the LocalLoss files. That result lives in FirstOrder/TraceRelations, in [the denominator bound](/chapter/denominator-bound/). The main output here is the defect at a place. The same note suggests about 3500 words for the chapter, which is too few for complete proofs of the three regimes.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
