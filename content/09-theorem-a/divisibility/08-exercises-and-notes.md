---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $p$ be prime, $P = p^e$ with $0 < e \le r$, $m \le p^r$ and $r^2m \le k$. Show that $P^{-2r} \le 1/(mp)$ and $r^2/(kP) \le 1/(mp)$. Deduce that a Frobenius cycle with $N = 2\ell$ letters has $3c_{\mathrm{div}} \le 12a\ell/(mp)$, where $c_{\mathrm{div}} = Na(P^{-2r} + r^2/(kP))$.

*Hint.* $mp \le p^r\cdot p^r \le P^{2r}$, and $p \le P$. Then $3c_{\mathrm{div}} \le 3\cdot 2\ell\cdot a\cdot 2/(mp)$.

**Exercise 2.** Let $q_0 = 7$ and $p = 3$. Show that the order $o_0$ of $-3$ modulo $7$ is $3$, so it is odd. Let $\tau$ be an a-place, that is a place of class $1$ modulo $q_0$. Show that $[-3]^i\tau$ is an a-place if and only if $3 \mid i$, and that the a-places in the orbit of $\tau$ under $[-3]$ form one orbit under $[-3^3] = [-3]^3$.

*Hint.* $-3 \equiv 4$, $4^2 \equiv 2$ and $4^3 \equiv 1 \pmod 7$. The class of $[-3]^i\tau$ modulo $7$ is $4^i$. Since $3$ is odd, $-3^3 = (-3)^3$.

**Exercise 3.** Let $\Gamma$ act freely on the classes $X = \Gamma\backslash G_f/K_0$, let $\rho(x)$ represent the class $x$, and let $V$ be the Weyl module. Show that a form fixed by $K_0$ is determined by its values $\varphi(\rho(x))$, and that these values can be any vectors of $V$. Deduce $D_X = |X|\dim V$, as in the proof of Section 6.

*Hint.* $\varphi(\gamma\rho(x)u) = \gamma\cdot\varphi(\rho(x))$. The value at $\rho(x)$ is well defined for any choice because the only $\gamma$ with $\gamma\rho(x) \in \rho(x)K_0$ is $\gamma = 1$.

**Exercise 4.** Prove item 4 of the lemma on gauges in Section 7 from items 2 and 3: if $\mathrm{GaugeLe}(d, p^r, \varphi)$ and $\beta \le -r$, then $\mathrm{GaugeLe}(d, 1, p^{-\beta}\varphi)$.

*Hint.* $|\iota_p p^{-\beta}|_p = p^{\beta}$, so $p^{-\beta}\varphi$ has gauge at most $p^{\beta + r}$, and $\beta + r \le 0$.

**Exercise 5.** Let $y$ and $y'$ keep $M$, with $\mathrm{IsOntoUpToColength}(p, M, j, y, c)$ and $\mathrm{IsOntoUpToColength}(p, M, j, y', c')$. Show $\mathrm{IsOntoUpToColength}(p, M, j, yy', c + c')$. This is the step from one $Y_{\mathfrak l}$ to $Y^m$ in Section 7.

*Hint.* Apply $y$ to $y'(M) + p^jM$ and add $p^jM$: the image is in $yy'(M) + p^jM$. A colength relation passes to images under a linear map. Then chain $M \supseteq y(M) + p^jM \supseteq yy'(M) + p^jM$ and multiply the determinants.

**Exercise 6.** In the proof of the theorem on the image in Section 7, write out the two inequalities for lift $j$ and add them. Show that the term $\#(\Phi_a\cap\Phi_\Lambda)\,a/x_1$ cancels and that the result is $\#\Lambda\,\nu_p + \mathrm{liftLoss}(\Lambda, j) \le (2\,\mathrm{loss}(p) - \mathrm{gain}(p))/m$. Explain why the cancellation needs a full mark and not only a marked set.

*Hint.* For a marked set that is not full, the collision sum outside $\Phi_\Lambda$ need not be $0$, and the lower bound for $D_{p,j}(\Phi_\Lambda)$ then has the extra term $-\mathrm{coll}_p(\Phi_\Lambda)$.

## Notes and references

The chapter follows seven files of the source in New/UpperBound/Divisibility: SetupAtLevel.lean (Section 2), ColengthAtLevel.lean (Section 3), ValuationAtLevel.lean (Section 4), ValuationAtNonSplitPrimes.lean (Section 5), HeckeEdges.lean and MarkOperator.lean (Section 6) and LocalDivisibility.lean (Section 7). These are the files that volume.yaml gives to this chapter. The theorem on elementary divisors is in [elementary divisors of a Hecke operator](/chapter/elementary-divisors/), and the gain, the loss and the divisibility bound of one lift are in [short columns and the gain](/chapter/short-columns-gain/). Both are earlier chapters of this volume. No file of this chapter imports a file of a later chapter of this volume.

The source gives related work for the two parts of the argument in its file comments. For the integrality of single theta lifts it names X. Zhang (2022), Berger (2009) and Prasanna (2006). For Hecke operators passed through theta lifts and scaled by powers of $p$, it names Rallis (1982), V. Lafforgue (2011) and Z. Liu (arXiv 2510.21644, 2025). For integral scalings of Hecke operators and their slopes, it names Arsovski (2019), Liu, Truong, Xiao and Zhao (2023), and Fakhruddin and Pilloni (2021). This book does not compare the statements of this chapter with these works. The marks, the Hecke edges and the four cases are the method of the source.

Two points of the notes of the specification differ from the source. The plan of the handbook, Section 07.4, lists the chapters of Volume 9 in an older order; this book uses the order of volume.yaml. The research note puts the expansion of the gluing (ChainDatumExpansion.lean), the marked primes (MarkedPrimes.lean) and the jet exponent (JetExponent.lean) in this chapter. Volume.yaml puts the first two in [marked primes and the valuation of a chain](/chapter/chain-valuation/) and the third in [short columns and the gain](/chapter/short-columns-gain/), and this chapter states the results it uses from them.

Status: drafted by a model. No person has checked this chapter against the Lean source.
