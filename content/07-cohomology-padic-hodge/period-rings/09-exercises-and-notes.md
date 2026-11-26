---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $K$ be a finite extension of $\mathbb{Q}_p$ of degree $n$, let $\Gamma = G_K$ with $j$ the inclusion, and let $T = \mathbb{Z}_p(r)$ for an integer $r$. Use the rank formula of Section 8 to compute $\operatorname{rank} Z_f(T)$ for every $r$. Compare the answer with the classical values $\dim H^1_f(K, \mathbb{Q}_p(r)) = n$ for $r \geq 1$, $1$ for $r = 0$ and $0$ for $r \leq -1$, through $\dim Z_f = \dim B^1 + \dim H^1_f$.

*Hint.* In the convention of Section 7, $\mathbb{Z}_p(r)$ has the single jump $-r$, and the index of $G_K$ in $G_p$ is $n$. So the formula gives $1 + n$ for $r \geq 1$ and $1$ for $r \leq 0$. The coboundaries $g \mapsto (\chi(g)^r - 1)x$ have rank $1$ for $r \neq 0$ and rank $0$ for $r = 0$. In each case the two counts agree.

**Exercise 2.** Let $c \in Z_f(\rho)$, with $T$ free over $\mathbb{Z}_p$. Deduce $c(1) = 0$ from the cocycle relation of Section 8. Then check that the formula $g(y, c) = (\rho(g)y + a(c)(g), c)$ for the extension defines an action, that is, that $g(h(y, c)) = (gh)(y, c)$.

*Hint.* Put $g = h = 1$ in $c(gh) = c(g) + \rho(g)c(h)$. For the action, the first coordinate of $g(h(y, c))$ is $\rho(g)\rho(h)y + \rho(g)a(c)(h) + a(c)(g)$, and the cocycle relation for $a(c)$ turns this into $\rho(gh)y + a(c)(gh)$. The source proves `map_one'` and `map_mul'` of `New.Period.extensionRep` in this way.

**Exercise 3.** Let $\rho$ be potentially crystalline, with $T$ finite free over $\mathbb{Z}_p$, and let $q : T \to T/p^mT$ be the quotient map. Show that $c \mapsto q \circ c$ on $Z_f(\rho)$ has the kernel $p^m Z_f(\rho)$, using only claim 4 of the basic properties of Section 8.

*Hint.* If $q \circ c = 0$, then every $c(g)$ is in $p^mT$. Since $T$ is torsion free, there is a unique map $b : \Gamma \to T$ with $c = p^m b$. Claim 4, with $a = p^m$, gives $b \in Z_f(\rho)$. The other inclusion is clear.

**Exercise 4.** In the theorem on Lang's equation of Section 8, suppose $y$ is a unit with $\alpha\varphi(y) = y$, where $\alpha = 1 \otimes a$, and every element of `FrobGal` fixes $\alpha$. Show by induction on $k$ that $\alpha^k \varphi^k(m(y)) = m(y)$ for every $m$ in `FrobGal`. Deduce that if $\varphi^k(s(y)) = y$, then $s(y) = \alpha^k y$. What is $y$ when $a = 1$?

*Hint.* For the step, write $\varphi^{k+1} m = \varphi^k m \varphi$ and apply $\varphi^k m$ to $\alpha\varphi(y) = y$. For the second claim, take $m = s$ and substitute $\varphi^k(s(y)) = y$. For $a = 1$ the element $y = 1$ satisfies $\varphi(y) = y$, and the theorem allows any unit with these properties.

**Exercise 5.** Explain why the theorem on positive jumps of Section 8 cannot hold with $t = 1$ in general. Let $p$ be odd, let $\Gamma$ be the open subgroup of $G_p$ on which $\chi(g) \equiv 1 \bmod p$, with $j$ the inclusion, and let $T = \mathbb{Z}_p(-1)$. Consider the map $c(g) = (\chi(g)^{-1} - 1)/p$.

*Hint.* The values of $c$ are in $\mathbb{Z}_p$ by the choice of $\Gamma$. The map $pc$ is the coboundary of $x = 1$, so $pc \in Z_f$, and $c \in Z_f$ by claim 4 of the basic properties. If $c$ were the coboundary of some $x \in T$, then $(\chi(g)^{-1} - 1)(x - 1/p) = 0$ for all $g \in \Gamma$. Since $\chi$ is not trivial on $\Gamma$, this gives $x = 1/p$, which is not in $\mathbb{Z}_p$. So $t = 1$ fails, and $t = p$ works.

**Exercise 6.** The definition of `New.Period.linearFrob` uses `Classical.epsilon`. Let $\rho$ be potentially crystalline and let $(s, m)$ be a pair that is not a Weil pair. Explain why the source proves nothing about $\beta_{s,m}$ for such a pair, and why the theorems of Section 6 and Section 8 on Weil pairs do not have this problem.

*Hint.* The source proves that a map with the defining property exists only for Weil pairs, by the theorem `New.Period.linearFrob_apply` of Section 6. For other pairs it may not exist, and then the epsilon value is an unspecified endomorphism, a junk value. For a Weil pair, the map exists, and it is unique since $D_{\mathrm{pcris}}$ spans. So every statement on $\beta_{s,m}$ is about $\rho$ only when $(s, m)$ is a Weil pair.

## Notes and references

The source of this chapter is the folder `Lib/PadicHodge` of `grh/` at the pin 72fead1. Section 2 follows `PeriodRings/Ainf.lean`. Section 3 follows `PeriodRings/AxTheorem.lean` and `TateSen.lean`. Section 4 follows `PeriodRings/CrystallineRings.lean`, `PeriodRings/DeRhamPeriods.lean` and `Crystalline/FixedRatios.lean`. Sections 5 and 6 follow `Crystalline/Basic.lean`, `Crystalline/Regularity.lean` and `Crystalline/FixedRatios.lean`. Section 7 follows `Crystalline/HodgeTateForms.lean` and `Crystalline/HodgeTateJumps.lean`. Section 8 follows `BlochKato.lean` and `Characters.lean`. The chapters on [Kisin frames](/chapter/kisin-frames/) and the [comparison theorems](/chapter/comparison-theorems/) use the objects of this chapter.

The classical theory is in J.-M. Fontaine, *Le corps des périodes p-adiques* and *Représentations p-adiques semi-stables*, both in Astérisque 223 (1994), and in O. Brinon and B. Conrad, *CMI summer school notes on p-adic Hodge theory* (2009). The ring $B_{\max}$ is the ring of P. Colmez, *Théorie d'Iwasawa des représentations de de Rham d'un corps local*, Ann. of Math. 148 (1998), Sections III.2 and III.3. The theorem of Ax is in J. Ax, *Zeros of polynomials over local fields: the Galois action*, J. Algebra 15 (1970), and the theorem of Tate is in J. Tate, *p-divisible groups*, Proceedings of a Conference on Local Fields (Driebergen, 1966), Springer (1967), Section 3. The rank formula is a form of S. Bloch and K. Kato, *L-functions and Tamagawa numbers of motives*, Grothendieck Festschrift I (1990), Proposition 3.8 and Corollary 3.8.4. J. Bellaïche, *An introduction to the conjecture of Bloch and Kato*, Clay summer school notes (2009), explains the classical formula. The header of `DeRhamPeriods.lean` also names X. Caruso, *An introduction to p-adic period rings* (2019), Section 3.

The source never uses $B_{\mathrm{cris}}$, $B_{\mathrm{st}}$, $D_{\mathrm{dR}}$ or filtered $\varphi$-modules. It does not prove that $B_{\max}$-admissibility agrees with crystallinity in the sense of Fontaine. The register of findings records this as F-056 and the junk value of `New.Period.linearFrob` as F-051, in [the register of findings](/chapter/register-of-findings/).

This chapter found these points in the notes and the plan.

1. The background note, at the entry for `crysCocycles.finrank_eq`, calls it "the Bloch-Kato rank formula for crystalline classes". The theorem counts crystalline cocycles, coboundaries included, not classes. Section 8 gives the conversion.
2. The source list of this chapter in the volume plan has `Lib/PadicHodge/PeriodRings`, `Lib/PadicHodge/Crystalline` and `Lib/PadicHodge/BlochKato`. It does not list `TateSen.lean` and `Characters.lean`, which the proposed chapter in research note h, §11, item 9 includes and which this chapter uses. The entry `Lib/PadicHodge/BlochKato` is a single file, not a folder.
3. The docstrings of `Characters.lean` cite "Caruso" with no title. The work is probably the one named in the header of `DeRhamPeriods.lean`.
4. The header of `TateSen.lean` cites "Brinon-Conrad §14". This chapter has not checked that section number against the notes of Brinon and Conrad.
5. The lemma `New.Lift.mu_sq_dvd_smul_mu_sub` is in `PeriodRings/DeRhamPeriods.lean` but in the namespace `New.Lift`, not `New.Period`. A search for it under `New.Period` fails.

The chapter does not check that the source builds. It reports what the declarations state. Nothing in this chapter claims that the proof is correct or that the generalized Riemann hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
