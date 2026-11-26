---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $n = 1$ and $A = (a)$. Write out $D_A(Y) = \det((1 + Y)A - 1)$ and check that its coefficient at $Y^1$ is $\det A$. For which $a$ is $v(D_A(y)) = 0$ for every $y$ in the maximal ideal?

*Hint.* $D_A(Y) = (a - 1) + aY$. For $y$ in the maximal ideal, $D_A(y) \equiv a - 1$ modulo the maximal ideal, so the valuation is $0$ exactly when $a - 1$ is a unit.

**Exercise 2.** Let $\rho(g) = \alpha \cdot 1$ and let $c$ be a cocycle. Compute $\mathrm{aff}_c(g)^2(u)$ and $\mathrm{aff}_c(g)^3(u)$ directly. Show that if $\alpha = -1$ then $\mathrm{aff}_c(g)^2 = 1$.

*Hint.* $\mathrm{aff}_c(g)^2(u) = c(g) + \alpha(c(g) + \alpha u) = \alpha^2 u + (1 + \alpha)c(g)$. Add one more step for the cube. For $\alpha = -1$, $1 + \alpha = 0$ and $\alpha^2 = 1$.

**Exercise 3.** Let $\gamma$ commute with $\varphi$, let $\rho(\gamma) = \zeta \cdot 1$ and let $c$ be a cocycle with $c(\gamma) = 0$. Show that $(\zeta - 1) c(\varphi) = 0$. Compare with Sah's identity of [Sah's lemma](/chapter/tied-selmer-groups/#selmer-data-tied-selmer-groups-and-sahs-lemma).

*Hint.* Apply $c$ to $\varphi\gamma = \gamma\varphi$: $c(\varphi) + \rho(\varphi)c(\gamma) = c(\gamma) + \zeta c(\varphi)$. Sah's identity is the same computation with the commutator $[\varphi, \gamma]$ in place of $1$.

**Exercise 4.** Let $m = 1$, $B = C = (O/\varpi)^2$ with basis $e_1, e_2$, $\mathrm{ev}_\gamma(x_1, x_2) = x_1$ and $\mathrm{ev}_\varphi(x_1, x_2) = x_2$. Find the kernel of $a\,\mathrm{ev}_\gamma - \mathrm{ev}_\varphi$ for each $a$, and check the tilting lemma. Here no residue is bad.

*Hint.* The kernel is the line $x_2 = a x_1$, of length $1$. The right side of the lemma is $\ker \mathrm{ev}_\gamma$, the line $x_1 = 0$, also of length $1$, since $\mathrm{ev}_\gamma C$ is everything.

**Exercise 5.** Let a Selmer module modulo $\varpi^3$ be isomorphic to $O/\varpi^2$. Find the level $\varpi^i$ of passage to the exponent and a member with a unit value.

*Hint.* The exponent is $\varpi^2$, so $i = 2$. The module modulo $\varpi^2$ has the same length $2$. A generator $z$ has $\varpi z \neq 0$, so some coordinate of some $z(g)$ is not killed by $\varpi$ in $O/\varpi^2$, hence is a unit.

**Exercise 6.** In the descent, why does the bound $s = 1 + b$ not depend on $N$? Which inclusion of the section on [the descent](/chapter/tied-selmer-groups/#the-descent) gives this?

*Hint.* The start $\{P_0\}$ has all slopes $0$, so its tied groups lie in the groups $\mathrm{Sel}_i(\emptyset)$, which do not involve the auxiliary data. Each step adds one prime and lowers $\mathrm{tot}$ by at least $1$. So $\#J \leq 1 + \mathrm{tot}(\{P_0\}) \leq 1 + b$.

**Exercise 7.** Let $\mathrm{rank}\, T_i = 1$ and $e = 2$. How many residues can be bad in one step of the descent? Show that the condition $\#k > 2 \cdot 1 \cdot 2 + 1$ leaves a unit slope.

*Hint.* Tilting gives at most $2 \cdot 1$ bad residues for each of the two levels, so at most $4$ in all. If $\#k \geq 6$, there are at least $5$ nonzero residues, so one of them is the residue of a good unit. A smaller field may leave none.

The exercises use only the statements of this chapter.

## Notes and references

The Greenberg-Wiles formula is Theorem 2.19 of H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, in Current Developments in Mathematics (1995). For the local Euler characteristic and local duality the chapter cites J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, Chapter VII. The source names Sah's lemma as known and cites, for the method of adding primes, B. Mazur and K. Rubin, *Diophantine stability* (2018), and N. Fakhruddin, C. Khare and S. Patrikis, *Relative deformation theory, relative Selmer groups, and lifting irreducible Galois representations* (2021). This chapter does not compare the statements of the source with these texts.

The notes and the plan have errors for this chapter. The note f-congr, §5, lists AuxiliaryPrimes under this chapter. The `volume.yaml` of the volume puts it in [tied traces and even classes](/chapter/tied-traces/), and research note F-188 records this. Plan 07.4 has an older order of the chapters of Volume 12. The book follows `volume.yaml`.

No file of this chapter imports a file of a later chapter. The files Untied and OneSystem are used by the file Line of [Stickelberger systems and the twisting theorem](/chapter/twisting-theorem/), and the bound for the global term by its file MainSummands.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
