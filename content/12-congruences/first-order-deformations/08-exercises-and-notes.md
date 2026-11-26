---
title: Exercises and notes
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\ell = 5$ and $\gamma$ with $\mathrm{cyc}(\gamma) = u = 1 + 5 = 6$. Take $t = 3$. Compute the $5$-adic valuation of $\prod_{k < 3,\, k \neq e} (u^e - u^k)$ for $e = 0, 1, 2$, and find the least $b$ for which the separation condition of [the triangle of primes](/chapter/first-order-deformations/#the-triangle-of-primes) holds.

*Hint.* $u^e - u^k = u^k (u^{e-k} - 1)$ for $k < e$, and $v_5(6^a - 1) = 1 + v_5(a)$. All three products have valuation $2$.

**Exercise 2.** In the lemma that conjugation separates the exponents, take $s = \{a\}$. Check directly that $g' = (\gamma g \gamma^{-1})^m g^k$, with $m \equiv \bar c^{-1}$ and $k \equiv -\bar c^{\,a}$, satisfies $\psi(g') = (\bar c^{\,d} - \bar c^{\,a}) \psi(g)$ for every $\psi$ of Kummer type with exponent $d$.

*Hint.* A map of Kummer type is additive on $G_\nu$ and satisfies $\psi(\gamma h \gamma^{-1}) = \bar c^{\,d+1} \psi(h)$ there.

**Exercise 3.** Let $n = 3$ and $r = 1$, so $t = 2$. Suppose that the Satake parameters at $w$ of a unitary spherical representation are $X_0, X_0 q, \beta$ with $|X_0|^2 = q$. Show that the chain lemma forces this shape once $X_0$ is a root. Then write the rescaled Hecke polynomial as $(X - 1)(X - q) T$, and find $T$.

*Hint.* $|X_0|^2 q^2 = q^3$. Then $T = X - \beta / X_0$, up to the normalization of the leading coefficient.

**Exercise 4.** Prove the lemma on integral divisors when $B = 1$. Show by an example that the hypothesis $\|A'(1)\| \geq 1$ cannot be dropped.

*Hint.* For $B = 1$ the hypotheses say $A \equiv C \equiv A'$. Take $A = A' = C = X - 1$. Then $A(1) = 0$, and no $e$ with $e(1) = 1$ is a multiple of $A$.

**Exercise 5.** In [the deformed norm](/chapter/first-order-deformations/#the-operator-at-one-place-and-the-deformed-norm), take two places $J = \{1, 2\}$. Expand $(\mathrm{Nm}_1 + \alpha_1 \partial_1)(\mathrm{Nm}_2 + \alpha_2 \partial_2)$, and write the coefficient of $\alpha_1\alpha_2$ in its product with $\tau_1 - \alpha_1 \rho_1$. Show that it is $\equiv 0$.

*Hint.* The coefficient is $(\partial_1 \tau_1 - \mathrm{Nm}_1 \rho_1)\, \partial_2$, since the local operators commute. Use condition 2 of the operator $\partial$.

**Exercise 6.** Find where the proof of the top coefficient uses that $\mathcal{D}_S y = 0$ for $S \neq J$. What does the proof give without this hypothesis?

*Hint.* It is the lemma that only the top term survives. Without it, the left side is $\sum_S$ of terms $n_1 d c\, Y_{J \setminus S} A \mathcal{D}_S y$, and only their sum is integral.

## Notes and references

**Ribet's method.** The construction of a Galois extension from a congruence between an Eisenstein series and a cusp form is due to Ribet, *A modular construction of unramified p-extensions of $\mathbb{Q}(\mu_p)$*, Invent. Math. 34 (1976). Wiles, *The Iwasawa conjecture for totally real fields*, Ann. of Math. 131 (1990), carried it to Hilbert modular forms with a pseudo-representation in place of a representation. This chapter follows the source. It deforms the norm from a deep auxiliary level to the base level in one parameter $\alpha_j$ for each place. The top coefficient of Ribet's element in these parameters then clears the denominator of the projection to the lifts. The orders of the even classes do not enter the bound. The source names Lecouturier (2019) and Dotto and Thorne (2026) for first-order derivatives in diamond operators in other settings.

**Taylor-Wiles places.** Places of norm $1$ modulo $\ell^\nu$, equally many at every level, are the places of Taylor and Wiles, *Ring-theoretic properties of certain Hecke algebras*, Ann. of Math. 141 (1995). They are chosen there with the Greenberg-Wiles formula, in the form of Darmon, Diamond and Taylor, *Fermat's Last Theorem*, Theorem 2.19. Here the count runs over the real subfield $F$ and gives reciprocity laws for even classes in Tate twists. The choice is triangular: each new Frobenius element kills the earlier Kummer maps but not the new one. The source names Gras and Munnier (1998) and Hajir, Maire and Ramakrishna (2022) for tame ramification governed by Frobenius in Kummer fields of units.

**Root chains.** The unitary spherical dual of $\mathrm{GL}_n$ over a $p$-adic field is classified in Tadić, *Classification of unitary representations in irreducible representations of general linear group (non-archimedean case)*, Ann. Sci. ENS 19 (1986). Chains of Satake parameters follow from it. The source proves the form it needs directly ([Iwahori exponents and the chain lemma](/chapter/iwahori-satake/)). The use of the chain at a place where a lift has eigenvalue $1$ is close to Clozel, Harris and Taylor, *Automorphy for some l-adic lifts*, Publ. Math. IHES 108 (2008), Section 3.4.

**Higman's criterion.** The operator $\Psi$ with $\sum_g g^{-1} \Psi g = c$ is Higman's criterion for projectivity up to $c$. See [building the representations](/chapter/building-representations/).

**Back-edges.** Three files of this chapter import files of later chapters. KummerMaps imports `New/Congruences/FirstOrder/EvenClasses`, and AuxiliaryPrimeTie imports `New/Congruences/FirstOrder/TiedTraces`. Both belong to [tied traces and even classes](/chapter/tied-traces/). HeckeStrings imports `New/Congruences/GaloisRepresentations/SelmerHypotheses`, which belongs to [the main summands of the attached Galois representations](/chapter/main-summands/). This chapter states the definitions of even classes, tame generator families and the triangle condition, because it uses them first. It recalls the other objects in words and takes the results of those chapters as known.

**Errors in the plan.** The `plan:` line of this chapter in `volume.yaml`, and the map of files in the first chapter of this volume, leave out AuxiliaryPrimeTie, which the source list of the chapter includes. The research note places EvenClasses, OnePrime and TiedTraces in this chapter. They belong to the next chapter.
