---
title: Exercises
lean:
  - New/Derivatives/Vacuum/ShortVectors.lean
  - New/Derivatives/Vacuum/TightFrames.lean
  - New/Derivatives/Vacuum/IntegralVacuum.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Take the base field $\mathbb{Q}$ in place of $K$, $q_1 = 4$ and $\zeta = i$, so that $P = X^2 + 1$. Compute the quotient $P(X)/(X - i)$, its coefficients $b_0$, $b_1$, and the value $P'(i)$. Show that $b_0/P'(i) = 1/2$ and $b_1/P'(i) = -i/2$, and check Euler's lemma $\mathrm{tr}(b_k i^l / P'(i)) = \delta_{kl}$ for $k, l \in \{0, 1\}$ directly.

*Hint.* $P(X)/(X - i) = X + i$ and $P'(i) = 2i$. The trace from $\mathbb{Q}(i)$ to $\mathbb{Q}$ is $z \mapsto 2\,\mathrm{Re}(z)$.

**Exercise 2.** Let $q_0$ be a modulus whose primes include every prime of $q_1$. Show that $\Phi_{q_1}(X) = \Phi_{q_0}(X^{q_1/q_0})$. Check it for $q_0 = 6$ and $q_1 = 12$. Deduce part (1) of the bounds lemma of Section 7 from the bound $\binom{\varphi(q_0)}{k}$ for the coefficients of $\Phi_{q_0}$.

*Hint.* The roots of $\Phi_{q_0}(X^{q_1/q_0})$ are the $z$ with $z^{q_1/q_0}$ a primitive $q_0$-th root of unity. If every prime of $q_1/q_0$ divides $q_0$, these $z$ are exactly the primitive $q_1$-th roots of unity, and both sides have degree $\varphi(q_1) = (q_1/q_0)\varphi(q_0)$. For the example, $\Phi_{12} = X^4 - X^2 + 1$ and $\Phi_6 = X^2 - X + 1$.

**Exercise 3.** Let $\beta \in \mathcal{O}_K$ with $\beta + \bar\beta = 1$, and put $t_n = \beta^n + \bar\beta^n$. Show that $t_n = t_{n-1} - \beta\bar\beta\, t_{n-2}$. Show that $t_n \equiv 1 \pmod{\beta\bar\beta}$ for $n \ge 1$, without the use of primes of $K$. For $d = 7$, find the least $n \ge 1$ with $|t_n| > 10$.

*Hint.* For the congruence, use induction with $t_0 = 2$ and $t_1 = 1$: modulo $\beta\bar\beta$ the recurrence is $t_n \equiv t_{n-1}$. For $d = 7$ the list in Section 7 gives $n = 5$.

**Exercise 4.** In the construction of the frame of length prime to $q_1$, replace each pair $(\zeta^{-i}, e_i)$ by the difference $\zeta^{-i} - e_i$ instead of the sum. Show that the result is a tight frame of length $q_1(1 + \sum_i \nu_i) - t$. Is this length also prime to $q_1$? Is it always positive?

*Hint.* The cross terms change sign, and the lemma on replacing pairs works with $-t$ in place of $t$. The length is congruent to $-t$ modulo $q_1$. For positivity, take $\sigma = \tau$ in the frame identity: the length is $\sum_i |\sigma(w_i)|^2$, and the member $\zeta e_{f-1} \ne 0$ is still in the frame.

**Exercise 5.** Let $q, h \ge 1$ be coprime integers. Show that every $n \ge (q-1)(h-1)$ is of the form $aq + bh$ with $a, b \in \mathbb{N}$, and that $qh - q - h$ is not. Conclude that the threshold $q_1 h + R(q_1 + h)$ in the coin problem of Section 7 can be lowered to $(q_1 - 1)(h - 1) + R(q_1 + h)$. Why does the source not need this?

*Hint.* For the first part, take $b \in [0, q)$ with $bh \equiv n \pmod q$, and show that $n - bh \ge (q-1)(h-1) - (q-1)h = 1 - q$. As $n - bh$ is a multiple of $q$, it is not negative. For the second, suppose $qh - q - h = aq + bh$ and reduce modulo $q$ and $h$. The length $M$ is near $b^{20}$, far above both thresholds.

**Exercise 6.** Let $p$ be a prime that divides $q_1$, with $|\iota_p(\bar\beta)| < 1$. Show that $y = 1$ has no unit linear form at $p$, so that the second vector $\zeta e_{f-1}$ of Section 7 is needed.

*Hint.* By the proof in Section 7, $|\iota_p(\mathrm{periodFactor})| = |\phi_\tau(P'(\zeta))|$. Write $P'(\zeta) = \prod (\zeta - \zeta^a)$ over the $a \ne 1$ prime to $q_1$, modulo $q_1$, and choose $a$ so that $\zeta^{a-1}$ has order $p$. Then $1 - \zeta^{a-1}$ has norm a power of $p$ and is not a unit above $p$.

## Notes and references

The integral vacuum and the short frames are the objects of the source in New/Derivatives/Vacuum. The source states that the integrality of theta values via torsion values is known from the literature, and it lists as related work: J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices V* (1989); T. Finis, *Divisibility of anticyclotomic L-functions and theta functions with complex multiplication* (2006); and D. Mumford, *On the equations defining abelian varieties I*, Invent. Math. 1 (1966). The source gives no places in these works for the statements of this chapter, and this chapter does not compare them.

The formula for the area of a lattice with complex multiplication by $\mathcal{O}_K$ is the formula of A. Selberg and S. Chowla, *On Epstein's zeta-function*, J. reine angew. Math. 227 (1967). Section 3 uses it in the form of [the Chowla-Selberg formula](/decl/New.CMLattice.chowla_selberg/). The action of automorphisms of $\mathbb{C}$ on the values of theta functions with complex multiplication, used in Section 6, is the main theorem of complex multiplication; see G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), Chapter 5. The theta functions of one variable and their Fourier expansions are those of D. Mumford, *Tata Lectures on Theta I* (1983), Chapter I.

Euler's lemma of Section 7 is classical: see J.-P. Serre, *Local Fields*, Chapter III, §6, Lemma 2, where it gives the dual basis of the powers of a root of a separable polynomial under the trace. The proof here by Lagrange interpolation is the usual one. The construction of a frame of a length prime to $q_1$ by the cross terms $\beta^j + \bar\beta^{\,j}$ is that of the source. The term *tight frame* comes from the theory of frames in Hilbert spaces, where a finite family $(w_i)$ is a tight frame if $\sum_i \langle z, w_i\rangle w_i$ is a fixed multiple of $z$; the condition of Section 1 is this condition for the family $(\tau(w_i))_\tau$ in $\mathbb{C}^f$, together with the integrality $w_i \in \mathfrak{a}_0$.

The background on the Weil representation and its Fock model is in [the Weil representation](/chapter/weil-representation/), and the background on the field $E$ at the primes is in [the field E at the primes](/chapter/field-at-primes/). The frames of this chapter are used in [theta kernels and gauges](/chapter/theta-kernels-gauges/) and in [sharpness](/chapter/sharpness/). The sizes of the data that bound $h$ by $b$ and $q_1 h + R(q_1 + h)$ by $M$ are in [the data and their sizes](/chapter/data-and-sizes/).
