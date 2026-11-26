---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises and notes

### Exercises

1. (Section 4.) Let $G(z) = \sum_k a_k z^k$ be an entire function of one variable with $|G(z)| \le A\,e^{T|z|^2}$ for all $z$, where $A, T > 0$. Show that $|a_k| \le A\,(2eT/k)^{k/2}$ for $k \ge 1$. Compare $k!\,|a_k|$ with $\sqrt{k!}\,T^{k/2}$, the shape of the bound of Section 4. *Hint.* Cauchy's estimate on the circle of radius $r$ gives $|a_k| \le A e^{Tr^2} r^{-k}$. Take $r^2 = k/(2T)$. For the comparison use $k! \le e\sqrt{k}\,(k/e)^k$.

2. (Section 5.) Let $M$ be the $m \times m$ matrix with all entries $1$, and $\xi = (1, \dots, 1)$. Compute $\|M\xi\|/\|\xi\|$ for the maximum norm over $\mathbb{C}$ and over $\mathbb{C}_p$. Explain why the bound of the model case of Section 5 has no factor $m$, while the archimedean bounds of Section 4 carry factors such as $(2k+2)^{f|n'|}$. *Hint.* Over $\mathbb{C}_p$, $|m|_p \le 1$.

3. (Section 5.) Show that $\mathrm{raises}(d, d', c) \subseteq \mathrm{raises}(d, d', c')$ for $c \le c'$, and that $\mathrm{raises}(d, d', c) = \mathrm{raises}(d, d', 0)$ for $c < 0$. Show that $\mathrm{raises}(d, d', c)$ is closed under multiplication by $z \in \mathbb{C}$ with $|\iota_p z|_p \le 1$, if $c \ge 0$. *Hint.* $\max(c, 0)$ is monotone in $c$. For the last claim use the lemma on scalars with $B' = B$.

4. (Section 5.) Let $n = \{0, 1\}$, let $\Phi$ have one place $\tau$, and let $\kappa(\tau, 1) = k$ with no other columns. A filling $i$ puts one index $i(j) \in n$ in each column $j < k$. Let $u_\tau = (p, 1)$. Show that $\mathrm{dw}_e(u, i) = p^{-e - z}$, where $z$ is the number of columns $j$ with $i(j) = 0$. What does the theorem on gauges from an entrywise bound ask of the jet matrix at $d$ with $\iota_\tau(d) = \mathrm{diag}(p, 1)$? *Hint.* The first factor is $|p \cdot 1|_p^{e}$. A column of height $1$ has one box.

5. (Section 5.) Let $F$ be standard for $\delta = 1$ and let $|\iota_p c|_p \le 1$. Use the corollary on integer multiples to show that $d^{L} F \in \mathrm{raises}(1, 1, 1)$ for the theta kernel of scale $c\,t_0$, with $L = \mathrm{boxes}(\kappa, |n'|)$. For which primes $p$ is the factor $d^L$ needed by this argument? *Hint.* Take $N = d_0 = 1$ and $M = d^L$. The bound of the theorem on standard data is $(|\iota_p c|_p/|\iota_p d|_p)^L$, and $|\iota_p d|_p = 1$ for $p \ne d$.

6. (Section 6.) Show that $\mathcal{O}_{(0)} = \mathbb{C}$ and that $1/2 \in \mathcal{O}_{(2)}$ but $1/2 \notin \mathcal{O}_{(1)}$. Explain why the proposition on vacuum data as combinations states nothing about denominators. *Hint.* $\gcd(l, 0) = l$. For $l = 2$, $|1/2|_2 = 2$.

7. (Section 6.) Let $E = \mathbb{Q}(i)$, so $f = 1$, and $\mathfrak{m} = (2 + i)$. Check that $\mathfrak{m}$ is prime to its conjugate and that $5 \in \mathfrak{m}$. Compare $|\mathcal{O}_E/\mathfrak{m}|$ with the bound $5^{2f}$ of the lemma on residue rings. For $|n'||n| = 1$ and $\Psi = 1$, what size does the corollary on bounded values give? *Hint.* $(2+i)(2-i) = 5$, and the norm of $\mathfrak{m}$ is $5$. The field $\mathbb{Q}(i)$ is a CM field, but it is not a field $E = K(\zeta)$ of the argument; the lemmas of Section 6 that the exercise uses hold for it with the same proofs.

### Notes and references

The two halves of the chapter follow two classical ideas. The archimedean half bounds a derivative by Cauchy's estimate. In the Fock model of [the Weil representation](/chapter/weil-representation/) Cauchy's estimate takes the form of an integral against a Gaussian, as in the work of Bargmann on the space of entire functions of Gaussian growth. The novelty is only in the bookkeeping: the operator $L$ of Section 2 lets the same estimate bound every conjugate of a jet at once.

The $p$-adic half uses the integrality of the jets of theta functions of CM lattices, after a fixed period is divided out. This is the setting of algebraic theta functions and the $p$-adic interpolation of Eisenstein-Kronecker numbers. The source names as related work, in its documentation of New/UpperBound/Kernels/ThetaLiftGauge.lean: K. Bannai and S. Kobayashi, *Algebraic theta functions and the p-adic interpolation of Eisenstein-Kronecker numbers*, Duke Math. J. (2010); G. Kings and J. Sprang, *Eisenstein-Kronecker classes and integrality of critical values* (2019); and N. Katz, *p-adic L-functions for CM fields*, Invent. Math. (1978). The REFERENCES file of the source records the work of Bannai and Kobayashi as compared, with its place confirmed, for other files of the source. It does not record the other two works. This book has not compared these citations with the statements of this chapter. The divisibility of the jets themselves is proved in [the count and the divisibility of standard data](/chapter/normal-forms/), from the formal group of the CM curve in [the CM curve, its formal group and the normal form](/chapter/cm-formal-group/).

The gauge of [automorphic forms](/chapter/automorphic-forms/) measures a vector of a Weyl module at a point of the finite adelic group. Raising gauges is the form in which the divisibility of one kernel is summed over chains in [marked primes and the valuation of a chain](/chapter/chain-valuation/), and then compared prime by prime in [divisibility prime by prime](/chapter/divisibility/). The archimedean bound enters [the archimedean size of the composite lift](/chapter/archimedean-size/). The two together are the two sides of Theorem A, as planned in [Theorem A and its plan](/chapter/theorem-a-plan/).

The chapter states what the source states. The source contains a proof in Lean of each statement. This book does not claim that these proofs, or the argument they belong to, are free of error.

**Remark (Formalization).** The constants of this chapter that come from chosen objects are $C_{\mathrm{vac}}$ and $c_s$ of [the integral vacuum and tight frames](/chapter/integral-vacuum/), and the left inverse used to define $L$ in Section 2. Each statement holds for every choice, because only the stated properties of the choice enter its proof. The rational points of weak approximation in Section 5 are chosen inside a proof and do not appear in any statement. The number $c_s$ is nonzero. The size $B$ of a vacuum combination and the bound $B$ of a raising statement can be negative; the statements are then vacuous or reduce to the case $0$, as the remarks of Sections 4 and 5 explain.
