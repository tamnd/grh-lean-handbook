---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\rho_h = 1/\varphi(\ell^h)$. Show that $\sum_{h \leq H} \varphi(\ell^h) \rho_h$ grows linearly in $H$, while $\sum_{h > H} \rho_h$ tends to $0$. Explain why this lets the theorem on [roots of unity](/chapter/twisting-theorem/#roots-of-unity) take $h_0$ independent of the degrees.

*Hint.* $\varphi(\ell^h) = \ell^{h-1}(\ell - 1)$, so the tail is a geometric series.

**Exercise 2.** Let $g = a \prod_i (X - \alpha_i)$ over $\bar{\mathbb{Q}}_\ell$. Show that $v(g(\zeta - 1)) = v(a) + \sum_i v(\zeta - 1 - \alpha_i)$. Then show that the roots with $v(\alpha_i) \neq \rho_h$ give the same value at every primitive $\ell^h$-th root of unity $\zeta$.

*Hint.* $v(\zeta - 1) = \rho_h$, and $v(x - y) = \min(v(x), v(y))$ when $v(x) \neq v(y)$.

**Exercise 3.** In [the general twisting theorem](/chapter/twisting-theorem/#the-general-twisting-theorem), explain why the order of the choices $s_0$, $r$, $h_0$, $N$ cannot be changed. What fails if $h_0$ is chosen before $r$?

*Hint.* The loss $s_0 r$ must be at most $\varepsilon/2$, and $h_0$ depends on the bound $r/m$ for the points.

**Exercise 4.** Let $u$ be a lattice whose values span $M_n(O)$, and let $u(g) = y \cdot 1$. Use the trace identity $\mathrm{tr}\, u(x^c) = \mathrm{cyc}(x)^{1-t} \mathrm{tr}\, u(x^{-1})$ to compute the scalar of $(g^c)^{-1}$. Check the result for $n = 1$ and $t = 1$.

*Hint.* For $n = 1$ and $t = 1$ the identity reads $u(x^c) = u(x)^{-1}$.

**Exercise 5.** Show that $4 v(p_i - 1) + 2^{-\ell} \leq e'_\ell$ for each prime $p_i$ of the data. Which part of $e'_\ell$ pays for the $L$-value systems, and which for the Selmer data?

*Hint.* The term $(4f + 3) r V$ bounds both $\beta_{T_i}$ and $4 v(p_i - 1)$; the term $2^{-\ell}$ is the loss $\varepsilon$ of the general theorem.

**Exercise 6.** Let $\tau$ be a tame character and $\xi = \tau^j$. Show that if $\xi^{\mathrm{inv}}$ is nontrivial on inertia at every $w \in Q$ for each $1 \leq j \leq m$, then $\tau$ is an $m$-fold twist.

*Hint.* Use the lemma on tame parts in [main summands and the twisting theorem](/chapter/twisting-theorem/#main-summands-and-the-twisting-theorem) and the identity $(\tau^j)^{\mathrm{inv}} = (\tau^{\mathrm{inv}})^j$.

The exercises use only the statements of this chapter.

## Notes and references

The twisting theorem gives one finite order anticyclotomic character, tamely ramified at new primes, whose first $m$ powers make the Selmer groups of finitely many main summands short and keep the ratios of twisted to untwisted Hecke $L$-values barely divisible by $\ell$. The source names this related work: B. Mazur and K. Rubin, *Diophantine stability* (2018); D. Kriz and A. Nordentoft, *Horizontal $p$-adic $L$-functions* (2023); H. Hida, *Non-vanishing modulo $p$ of Hecke $L$-values* (2004). For the theorem on roots of unity, the source names V. Serban, *An infinitesimal $p$-adic multiplicative Manin-Mumford conjecture* (2018), and M. Kurihara, *The structure of Selmer groups of elliptic curves and modular symbols* (2014), together with the paper of Kriz and Nordentoft. These are the only references of this chapter.

The proof has three layers. [Twist measures](/chapter/twisting-theorem/#twist-measures-of-critical-pairs) and [the L-value systems](/chapter/twisting-theorem/#the-stickelberger-systems-of-the-l-values) turn the $L$-values into Stickelberger systems. [The line](/chapter/twisting-theorem/#stickelberger-systems-on-a-line) and [Selmer data on a line](/chapter/twisting-theorem/#selmer-data-on-a-line) turn the Selmer data and the systems into polynomials in the coordinates of a twist. [Roots of unity](/chapter/twisting-theorem/#roots-of-unity) finds points of high order where all the polynomials are small at once. The bound $e'_\ell$ has two parts. The term $(4f + 3) r V$ is the size of the error terms of the main summands, and it does not depend on the twist. The term $2^{-\ell}$ is the loss of the general theorem. Any fixed positive loss works there; the source takes $2^{-\ell}$ so that the bound tends to $(4f + 3) r V$ as $\ell$ grows. The twist itself is not explicit. It comes from a choice of points of high order, and the proof gives no bound for the norms of the primes in $Q$. The chain of the whole argument is in [the plan](/chapter/regular-families-plan/#the-chain-of-the-proof).

The crystalline relations at $\ell$ and the local lattices come from [the local loss at $\ell$](/chapter/local-loss/), chapter 9 of this volume. That chapter comes before this one in `volume.yaml`. No file of this chapter imports a file that `volume.yaml` places in a later chapter of Volume 12.

The lemma `New.Selmer.exists_chosen_notMem_placesDividing`, used in the last proof, gives a chosen place above $p_0$ or $p_1$ that is prime to $\ell$. No earlier chapter documents it. Its proof takes $i$ with $p_i \neq \ell$ and a chosen place above $p_i$; such a place has residue characteristic $p_i$, so it is not above $\ell$.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
