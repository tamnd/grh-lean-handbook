---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $k$ be a finite field, $\chi \neq 1$ a character of $k^\times$ and $\lambda \neq 0$ in $k$. Show that $u \mapsto 1 + u\lambda$ is a bijection from $\{u : 1 + u\lambda \neq 0\}$ onto $k^\times$, and conclude that $\sum_s \chi(s)^{-1} = 0$ over these $s$.

*Hint.* This is the first step of the lemma on the hyperplane sum in [Section 8](/chapter/false-lifts/#three-special-cases).

**Exercise 2.** With $q = 2$ and $m = 2$, compute $\sum_U |c(X, U)|$ over the subspaces of $k^2$ and check the bound of the theorem on small roots when $q^3|X| = 1$.

*Hint.* There are $1$, $3$ and $1$ subspaces of dimensions $0$, $1$ and $2$. Compare with $(1 + |X|)(1 + 2|X|)$.

**Exercise 3.** Check the exponent computation at the end of [Section 5](/chapter/false-lifts/#small-roots) for $r = 1$, $l = 0$ and $n = 8$. Which of the two conditions $\sqrt q^{\,j}|X| \leq 1$ fails first when $n$ decreases?

*Hint.* Compute $d = r + 2(n - r - 1)$ and the two exponents $2n - r - 2l - 2$ and $n + r + 2l + 4$.

**Exercise 4.** In the proof of the theorem on theta periods (Section 7), explain why one cannot apply the theorem on descents and block periods to $y_1$ directly.

*Hint.* That theorem needs vanishing descents to $\mathbb{H}^N$, not to $W \oplus \mathbb{H}^N$. The factor $\vartheta$ absorbs $W$.

**Exercise 5.** Show that the conclusion of the theorem on descents to $W \oplus \mathbb{H}^N$ for $\zeta_0$ alone implies it for all $\zeta$, using only that the translates $x\zeta_0$ by real $x$ span the Weyl module.

*Hint.* A linear functional that vanishes on a spanning set is zero. Step 6 of the proof.

**Exercise 6.** In the lemma on conjugates of the second block, suppose a row of $e'$ lies in the block $l$. Find where the proof fails.

*Hint.* At a twist place the reduction of $(1, k)$ need not fix that row.

**Exercise 7.** Let $r = 1$, $\#M = 1$ and $\psi \neq 1$. Show directly that a form $\Xi$ with $s\,\Xi = \Xi$ for all $s \in GL_1(k_v)$ satisfies condition 1 of Section 1, and that the converse fails in general.

*Hint.* For the first part use Exercise 1. For the converse, a form on which $GL_1(k_v)$ acts by a character $\chi' \neq 1, \psi$ is also killed by every hyperplane sum.

## Notes and references

**Sources.** The source names as related work Wu, *Poles of Eisenstein series and theta lifts for unitary groups*, arXiv:2104.11954 (2021). The relation between first occurrence and periods goes back to Rallis, *On the Howe duality conjecture*, Compositio Math. 51 (1984). Related work on theta towers is Ginzburg, Jiang and Soudry, *Poles of L-functions and theta liftings for orthogonal groups* (2009), and Jiang and Wu, *On $(\chi, b)$-factors of cuspidal automorphic representations of unitary groups I* (2016). These are the references in the docstring of `PeriodsOfFalseLifts.lean`.

**What is specific to the source.** The three conditions, the block datum, the hyperplane sums and the exact Hecke root $x_w$ are specific to the source. In the literature, the bottom of the tower is usually the hypothesis that the lift to $W$ vanishes. Here condition 2 gives it only for one datum, and Sections 2 to 4 extend it to all data. In the related work of Wu the tower is controlled by poles of Eisenstein series. Here the plane step uses only the decay of the remainder of the kernel, the Hecke transfer and a maximum principle at one split place. This is why condition 3 is needed at one place only, and why the rank condition $2r + 2\#N + 3 < n$ appears: it makes the Hecke root small enough at every level of the tower.

**Errors in the notes and the plan.** The [plan of the volume](/chapter/theorem-c-plan/) says that this chapter defines point forms and false lifts and proves the projection bound. These are in [character lifts](/chapter/character-lifts/#point-forms-and-tested-forms), Section 8, as `volume.yaml` says. Some merged chapters say that this chapter uses the trivial lift facts of [twists and critical pairs](/chapter/twists-critical-pairs/) or the delta forms of [algebraic forms](/chapter/automorphic-forms/#algebraic-forms-on-definite-groups). The files of this chapter do not use them.

**The formalization.** The formalization remarks concern the explicit rank hypothesis `h_rank` (Section 1), the use of `choose` for the factorial ideles (Section 3) and for the kernel data (Section 7), boundedness without measurability (Section 5), the induction on the number of planes (Section 6) and the local option `respectTransparency` (Section 8). No statement of the chapter depends on a junk value.

**Imports.** No file of this chapter imports a file of a later chapter of Volume 11. The rank hypothesis `h_rank` is open as F-087 in the register of findings.
