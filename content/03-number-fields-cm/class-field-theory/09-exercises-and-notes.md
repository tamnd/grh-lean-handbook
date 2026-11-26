---
title: Exercises and notes
lean:
  - Lib/ClassField/Global/ArtinReciprocity.lean
  - Lib/ClassField/Global/AlbertBrauerHasseNoether.lean
  - Lib/ClassField/Global/NormTheorems.lean
  - Lib/ClassField/Global/ExistenceTheorem.lean
  - Lib/ClassField/Global/Chebotarev.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $K = \mathbb{Q}$ and let $\chi$ be the character of $\Gamma$ that cuts out $\mathbb{Q}(i)$. Show that $\chi$ is nonzero on every complex conjugation. Use the sign law to find the $b \in \mathbb{Q}^\times$ with $\chi(\operatorname{artinMap}(b)) = 1$. Check the answer for $b = -1$ and for $b = 3$ with the product formula of Section 5.

*Hint.* For $b = 3$, the local symbol at $3$ is the inverse of a Frobenius, and $3 \equiv 3 \pmod 4$, so $\chi$ takes the value $1/2$ there. At $p = 2$ the component $3$ is a unit, and its symbol is the image of $3$ under $\mathbb{Z}_2^\times \to (\mathbb{Z}/4)^\times$. The two values cancel.

**Exercise 2.** Show that $-1 = N(1 + \sqrt{2})$ in $\mathbb{Q}(\sqrt{2})$. Show that `New.hasse_norm` does not prove this. Find a totally positive $x \in \mathbb{Q}^\times$ that is not a norm from $\mathbb{Q}(\sqrt{2})$, and find the finite place where the hypothesis of `New.hasse_norm` fails.

*Hint.* Try $x = 3$. A norm $a^2 - 2b^2$ with $a, b \in \mathbb{Q}$ that equals $3$ gives a solution modulo $3$ that contradicts the fact that $2$ is not a square modulo $3$, after one clears denominators.

**Exercise 3.** Use the Example of Section 2, $(\mathbb{A}_{\mathbb{Q},f})^\times = \mathbb{Q}_{>0} \times \hat{\mathbb{Z}}^\times$, and let $\chi$ cut out $\mathbb{Q}(i)$. Describe the kernel of $\chi \circ \operatorname{artinMap}$ as a subgroup of $\mathbb{Q}_{>0} \times \hat{\mathbb{Z}}^\times$. Check that it has index $2$, as `New.index_ker_abelianLift_comp_artinMap` says. Check that it is the group of `New.abelianLift_artinMap_eq_one_iff`.

*Hint.* The kernel is $\mathbb{Q}_{>0} \times \{u : u \equiv 1 \bmod 4\}$. For a character of order $2$, the sign convention does not matter. A norm $N(y)$ from $\mathbb{Q}(i)$ at an odd prime $p \equiv 3 \pmod 4$ has even valuation.

**Exercise 4.** Let $m \geq 1$ and $a$ be integers with $\gcd(a, m) = 1$. Apply `New.chebotarev` with $K = \mathbb{Q}$ and $W$ the set of $g$ whose cyclotomic character modulo $m$ is $a$. Deduce Dirichlet's theorem that there are infinitely many primes $p \equiv a \pmod m$.

*Hint.* $W$ is open and nonempty. An arithmetic Frobenius at a prime $p \nmid m$ acts on $\mu_m$ as $\zeta \mapsto \zeta^p$. Put the primes that divide $m$ into $S$. To get infinitely many primes, apply the theorem again with the primes already found put into $S$ as well.

**Exercise 5.** Let $K$ be totally complex with class number $1$. Use `New.OddPart.exists_detecting_points_hom` with $S = \emptyset$ and $m = 0$ to show that every locally constant homomorphism $x : \Gamma \to B$ that vanishes on all inertia groups is $0$.

*Hint.* The index of `idelesPowAt ∅ 0` is $1$. Each $n_i \geq 2$ and $\prod_i n_i$ divides $1$, so the index type $\iota$ is empty.

**Exercise 6.** Let $K$ be totally complex and not imaginary quadratic, so that $\mathcal{O}_K^\times$ is infinite. Show that the image of $K^\times$ in $(\mathbb{A}_{K,f})^\times$ is not closed. Let $C$ be the quotient of the finite ideles by the image of $K^\times$, with the quotient topology, and let $\theta$ be the quotient map. Show that the conclusion of `New.exists_comp_artinMap` fails for $\theta$. Which hypothesis fails?

*Hint.* $K^\times$ meets $\prod_v \mathcal{O}_v^\times$ in $\mathcal{O}_K^\times$, which is infinite and not closed there, since that product is compact. Take $x$ in the closure of $K^\times$ but not in $K^\times$. Then $\operatorname{artinMap}(x) = 1$, since the Artin map is continuous and kills $K^\times$, but $\theta(x) \neq 1$. The space $C$ is not $T_1$. For $K$ imaginary quadratic, $K^\times$ is discrete in the finite ideles, so it is closed.

## Notes and references

The classical references are in Section 2. The source cites Milne, *Class Field Theory*, VI 4.9, VII 4 to 9, and VIII 4, and Tate's chapter in Cassels and Fröhlich, for the global theory. It cites Hasse, *Die Struktur der R. Brauerschen Algebrenklassengruppe*, Math. Ann. 107 (1933), for the deduction of reciprocity from the sum formula. For Chebotarev it cites Milne, VIII 7.4, and Stevenhagen and Lenstra, *Chebotarëv and his density theorem*, Math. Intelligencer 18 (1996). This book has not compared these citations with the source line by line.

The proof of reciprocity in Section 7 is Artin's method from cyclotomic characters, in E. Artin, *Beweis des allgemeinen Reziprozitätsgesetzes*, Abh. Math. Sem. Univ. Hamburg 5 (1927). The covering argument uses B. H. Neumann's lemma that a group is not a finite union of cosets of subgroups of infinite index, from *Groups covered by finitely many cosets*, Publ. Math. Debrecen 3 (1954). The source takes this lemma from Mathlib.

The source has no Weil group, no local existence theorem, no full idele class group, and no density in Chebotarev. The later volumes use `New.chebotarev`, `New.exists_comp_artinMap` and `New.IsHeckeOfType.eulerProd_ne_zero`, as Section 1 lists.

Status: drafted by a model. No person has checked this chapter against the Lean source.
