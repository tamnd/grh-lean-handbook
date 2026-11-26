---
title: Exercises and notes
lean:
  - Lib/Adelic/Hecke/ClassSums.lean
  - Lib/Adelic/AutomorphicForms/AutomorphicAsAlgebraic.lean
  - Lib/Adelic/AutomorphicForms/PAdicGauge.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $\mathbf{G}$ be a reductive group over a number field $F$ with $\mathbf{G}(F_\infty)$ compact, let $K \subset \mathbf{G}(\mathbb{A}_f)$ be an open compact subgroup, and let $(\rho, W)$ be a finite-dimensional representation of $\mathbf{G}(F)$. Let $g_1, \dots, g_h$ represent the finite set $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A}_f) / K$, and put $\Gamma_i = \mathbf{G}(F) \cap g_i K g_i^{-1}$. Show that the map $f \mapsto (f(g_1), \dots, f(g_h))$ is an isomorphism from the space of functions $f$ on $\mathbf{G}(\mathbb{A}_f)$ with $f(\gamma g k) = \rho(\gamma) f(g)$ onto $W^{\Gamma_1} \oplus \dots \oplus W^{\Gamma_h}$.

*Hint.* A value $f(g_i)$ fixes the value of $f$ on the whole double coset. The value is in $W^{\Gamma_i}$, because $\gamma g_i = g_i k$ for $\gamma \in \Gamma_i$. Conversely, a vector in $W^{\Gamma_i}$ gives a well defined function on the double coset. This is Gross's decomposition (Section 2 of Gross).

**Exercise 2.** In the setting of Exercise 1, show that each $\Gamma_i$ is finite. Let $K' \subset K$ be a normal open subgroup. Show the mass relation $\sum_j 1/\#\Gamma'_j = [K : K'] \sum_i 1/\#\Gamma_i$, where the left sum is over the classes of level $K'$.

*Hint.* $\Gamma_i$ is discrete in the compact group $\mathbf{G}(F_\infty) \times g_i K g_i^{-1}$. For the mass, the finite group $K/K'$ acts on the classes of level $K'$ above the class of $g_i$. Count the orbit with the stabilizer, which is the image of $\Gamma_i$ in $g_i K g_i^{-1} / g_i K' g_i^{-1}$. Compare the change of level in [Section 3](/chapter/automorphic-forms/).

**Exercise 3.** On the space of Exercise 1 with $W$ unitary, put $\langle f, f' \rangle = \sum_i \langle f(g_i), f'(g_i) \rangle / \#\Gamma_i$. For $a \in \mathbf{G}(\mathbb{A}_f)$, let $T_a$ be the Hecke operator of the double coset $K a K$. Show that the adjoint of $T_a$ is $T_{a^{-1}}$. Conclude that $T_a$ is self-adjoint when $K a K = K a^{-1} K$.

*Hint.* Write the inner product as the integral of $\langle f, f' \rangle$ over $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A}_f)$ for a Haar measure with $\operatorname{vol}(K) = 1$. Then change variables $g \mapsto g a^{-1}$. This is the class sum of Section 3 against the class integral.

**Exercise 4.** Let $f \in S_k(\mathrm{SL}_2(\mathbb{Z}))$ be a normalized eigenform with $T_p f = a_p f$, and let $\alpha, \beta$ be the roots of $X^2 - a_p X + p^{k-1}$. Use that $a_p$ is real. Show that $|\alpha| = |\beta| = p^{(k-1)/2}$ if and only if $|a_p| \leq 2 p^{(k-1)/2}$.

*Hint.* If the discriminant $a_p^2 - 4p^{k-1}$ is negative, then $\beta = \bar\alpha$ and $|\alpha|^2 = \alpha\beta = p^{k-1}$. If it is not negative, the roots are real with product $p^{k-1} > 0$, and they have the same absolute value only if $\alpha = \beta$. The real coefficients come from the self-adjointness of $T_p$ (Diamond and Shurman, Theorem 5.5.4).

**Exercise 5.** Let $K$ be a compact group with Haar probability measure, and let $(\rho, W)$ be an irreducible unitary representation of dimension $d$. Show that $\int_K |\langle \rho(k) v, v \rangle|^2 \, dk = \|v\|^4 / d$ for every $v \in W$. Use this to give a second proof that the map $\varphi \mapsto \varphi^\natural$ of Section 7 is injective.

*Hint.* This is the Schur orthogonality relation (Bröcker and tom Dieck, Chapter II, Section 4) with all four vectors equal to $v$. In Section 7 apply it with $v = v^+$, which is not zero.

**Exercise 6.** In the setting of Exercise 3, let $\mathcal{O}$ be the ring of integers of a $p$-adic field, and let $f, f'$ take values in an $\mathcal{O}$-lattice $L$ on which the form $\langle \cdot, \cdot \rangle$ is $\mathcal{O}$-valued. Let $N$ be the least common multiple of the $\#\Gamma_i$. Show that $N \langle f, f' \rangle \in \mathcal{O}$. Show by an example with one class that the factor $N$ can be necessary.

*Hint.* Each term $N/\#\Gamma_i$ is an integer. For the example, take $h = 1$, $\#\Gamma_1 = p$, $W$ trivial and $f = f' = 1$. Compare the integrality of the inner product in Section 9.

## Notes and references

The adelic definition of automorphic forms and the relation to classical forms follow Borel and Jacquet, *Automorphic forms and automorphic representations*, in Proc. Sympos. Pure Math. 33, Part 1 (1979). Classical modular forms and their Hecke operators are in Diamond and Shurman, *A First Course in Modular Forms* (Springer GTM 228, 2005), Chapters 1 and 5, and in Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), Chapters 2 and 3. Bump, *Automorphic Forms and Representations* (Cambridge, 1997), Chapter 3, gives the adelic theory for $\mathrm{GL}(2)$.

For groups that are compact at infinity, the forms are functions on a finite set of double cosets. This is the theory of Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999). The source uses this model: its spaces of forms of a fixed type and level are finite-dimensional spaces of functions on the finite set of classes, and its integrals are finite class sums. Section 7 states the isomorphism between the two models for standard spaces.

Schur orthogonality is in Bröcker and tom Dieck, *Representations of Compact Lie Groups* (1985), Chapter II, Section 4. The spectral theorem for commuting normal operators is in Axler, *Linear Algebra Done Right*, 3rd edition, Chapter 7.

The chapter uses the adeles, Hermitian spaces and the standard level of [Adeles and Hermitian spaces](/chapter/adeles-hermitian-spaces/), and the finiteness of classes of [Reduction theory](/chapter/reduction-theory/). The next chapters of this volume are [Discrete series](/chapter/discrete-series/), [Weyl modules](/chapter/weyl-modules/) and [Iwahori and Satake](/chapter/iwahori-satake/).

Status: drafted by a model. No person has checked this chapter against the Lean source.
