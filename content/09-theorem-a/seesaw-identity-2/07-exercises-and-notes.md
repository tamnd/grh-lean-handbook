---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1 (Another neighbour).** Let $E = \mathbb{Q}(i)$, $L = \mathbb{Z}[i]$ and $N = 13 = \pi\bar\pi$ with $\pi = 3 + 2i$. Put $u = \pi/\bar\pi$ and $L' = uL$. Show that $L \cap L' = \pi L$, that $L'/(L\cap L')$ has order $13$, and that the classes of $ku$, $0 \leq k \leq 12$, represent it.

*Hint.* Follow the model case of Section 1. The primes $\pi$ and $\bar\pi$ are coprime, so $z\bar\pi/\pi \in L$ exactly when $\pi \mid z$.

**Exercise 2 (The neighbour at a split place).** In the model case of Section 1, compute $L_w$ and $L'_w$ in $E_w \cong \mathbb{Q}_5$ at the place $w$ of $\pi = 2 + i$, and $L_{\bar w}$, $L'_{\bar w}$ at the conjugate place. Show that $L'_{\bar w}/L_{\bar w}$ has order $5$ and that $L'_w \subseteq L_w$. Deduce again that $L'/(L\cap L')$ lives at $\bar w$.

*Hint.* At $w$, $\bar\pi$ is a unit, so $u$ is a uniformizer times a unit. At $\bar w$ the roles change.

**Exercise 3 (The constant of the identity).** Let $d = R^{2m}$ and $u = \mathrm{normUnit}(c_0C/d)$.

1. Show that $u^{-1} = c_0C/d$ if $c_0C \neq 0$, and $u^{-1} = 1$ if $c_0C = 0$.
2. Show that $u\,c_0\,\varphi_\xi = 0$ when $c_0C = 0$.
3. Explain why the formula $c = d/(c_0C)$ is wrong for the constant of the seesaw identity.

*Hint.* (1) On a field, $\mathrm{normUnit}(x) = x^{-1}$ for $x \neq 0$. (2) If $C = 0$, then $\varphi_\xi$ is a combination of the zero vectors $0\cdot\mathrm{Glue}(x)$. (3) The proof shows $\iota_\vartheta(u\,\mathcal P\varphi) = B_{\vartheta,\Psi}(\varphi)$, and the constant is the factor that multiplies $B_{\vartheta,\Psi}(\varphi)$.

**Exercise 4 (Sizes).** Show that $R^{2m}\cdot R^{2\varrho+2} = M^{3fmn_m^2}$ for $R = M^{fn_m^2}$ and $m = 2\varrho+2$. As a test of the arithmetic, take $f = 1$, $n_m = 2$, $\varrho = 0$ and $M = 65$, and compute the bound on the absolute sum of the values of a chain datum.

*Hint.* $2m + (2\varrho + 2) = 3m$. The bound is $65^{24}$ in the given case.

**Exercise 5 (The base case of the cut sum).** Let $J \subseteq J_M \subseteq J^\circ$ be open compact subgroups with $J^\circ$ compact. Show that $[J_M : J]$ is finite and nonzero, and that $[J^\circ : J] = [J^\circ : J_M][J_M : J]$. Use this to check the constant $[J^\circ : J_M]\,a(g, 1, \ldots)$ in the base case of the theorem on the pairing as a cut sum.

*Hint.* An open subgroup of a compact group has finite index. Index is multiplicative in towers.

**Exercise 6 (Transposes).** Let $K(g, h)$ be a continuous function on $X \times Y$ for compact spaces with finite measures. Define $(If)(h) = \int_X K(g, h) f(g)\,dg$ and $(I^tz)(g) = \int_Y K(g, h) z(h)\,dh$. Show that $\int_Y z\cdot If = \int_X I^t z\cdot f$, and compare with the lemma on lift and descent in Section 6.

*Hint.* Fubini. In Section 6 the kernel is the theta series of the datum $\phi_j$, and the index $[J^\circ : J_j(\vartheta)]$ appears on both sides.

**Exercise 7 (Invariance through the cut sum).** Let $T$ be a finite set with an action of a group $H$, and let $m : T \to \mathbb{N}$ be $H$-invariant. Let $S : T \to V$ and let $h \in H$. Show that $\sum_{t\in T} m(t)^{-1}S(ht) = \sum_{t\in T} m(t)^{-1}S(t)$. Explain how this gives the invariance of $\varphi_\xi$, once the evaluation is equivariant.

*Hint.* $t \mapsto ht$ is a bijection of $T$ that preserves $m$.

## Notes and references

The seesaw identity of this chapter is the classical seesaw principle, applied once for each pair of lifts in a chain of $m$ lifts. In the classical form, two dual pairs $(G, H')$ and $(G', H)$ with $G \subseteq G'$ and $H \subseteq H'$ give an equality of two inner products. Here the inner product with the Poincaré series is unfolded across the whole chain. [Part 1](/chapter/seesaw-identity-1/) does the unfolding, and this chapter computes the finite data and assembles them.

The module header of New/UpperBound/Seesaw/SeesawIdentity.lean names three works on the transfer of Bessel and Fourier-Jacobi periods under one theta lift: B. Wang, *Global theta lifting and periods associated to nilpotent orbits* (2025); R. Gomez and C.-B. Zhu, *Local theta lifting of generalized Whittaker models* (2014); and W. T. Gan and A. Ichino, *The Gross-Prasad conjecture and local theta correspondence* (2016). The REFERENCES file of the source records that the citation of Wang was compared and its place confirmed. It has no entry for the other two. This book has not compared them with the statements of the source.

The header also names three works on denominators of periods and congruences of theta lifts: B. Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999); M.-L. Hsieh and K. Namikawa, *Bessel periods and non-vanishing of Yoshida lifts modulo a prime* (2015); and X. Zhang, *Non-vanishing mod p of theta lifts for (O(2n+1), Mp(4n))* (2022). The point in common is that each period is a finite sum over cosets of a small level, with weights that divide powers of the conductor, so no new denominators appear away from it. The REFERENCES file records Gross (1999) at other places of the source. This book has not compared these citations with the statements of the source.

Neighbour lattices go back to Kneser's method of neighbours for the classification of lattices in a genus. The neighbours here are of the simplest kind: one unit vector is scaled by $\pi$ at the places of $P$ and by $\bar\pi^{-1}$ at their conjugates. The source files of this chapter do not cite Kneser, and the Lean proof does not use the general theory. It computes with the explicit unitary $\gamma$ of Section 2 and the representatives `neighbourTranslation`.

**Remark (Formalization).** The header of the source file and the docstring of `New.Data.seesaw_identity` call the constant "non-zero" and write $c \neq 0$. This is true, since $c$ is a unit of $\mathbb{C}^\times$. It can mislead. The identity has content only when $c_0C \neq 0$, and the source does not prove this. When $c_0C = 0$ both sides of the identity are $0$ (Section 6). The [register of findings](/chapter/register-of-findings/) lists this as F-068, and the same point about `seesawConst` as F-110 and F-122.

