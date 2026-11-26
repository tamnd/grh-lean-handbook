---
title: Exercises and notes
lean:
  - Lib/Cyclotomic/OddSha.lean
  - Lib/GaloisRep/Main/SelmerModules.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $E$ be a CM field with maximal real subfield $E^+$, let $\ell$ be an odd prime, and let $A$ be the $\ell$-part of $\mathrm{Cl}(E)$, with $A = A^+ \oplus A^-$ the splitting by the eigenvalues $\pm 1$ of complex conjugation. Show that the extension of ideals and the norm identify $A^+$ with the $\ell$-part of $\mathrm{Cl}(E^+)$. Deduce that $|A^-|$ is the $\ell$-part of $h_E^- = h_E / h_{E^+}$.

*Hint.* The norm after the extension is multiplication by $2$ on $\mathrm{Cl}(E^+)$. The extension after the norm is $1 + c$ on $\mathrm{Cl}(E)$, and it is multiplication by $2$ on $A^+$. As $\ell$ is odd, $2$ is a unit on $\ell$-groups.

**Exercise 2.** Let $E$ be a CM field, $\ell$ a prime and $\mathcal{O}$ as in Section 7. Show that $\text{Ш}_{\mathrm{odd}}(\ell, E, \mathcal{O}, 0, n)$ is isomorphic to $\mathrm{Hom}(\mathrm{Cl}(E), \mathcal{O}/\ell^n)$. Compute its length when $\mathrm{Cl}(E) \cong \mathbb{Z}/\ell^k$, and show that the bound of Section 7 by $v_{\mathcal{O}}(h_E)$ is an equality for $n \ge k$.

*Hint.* For $e = 0$ the cocycle rule makes $z$ a homomorphism, and conditions 2 and 3 make it unramified at every finite place. Use class field theory for the maximal unramified abelian extension. A homomorphism $\mathbb{Z}/\ell^k \to \mathcal{O}/\ell^n$ is determined by an element of the $\ell^k$-torsion of $\mathcal{O}/\ell^n$.

**Exercise 3.** Let $G$ be a group, $c \in G$ with $c^2 = 1$, $\Upsilon : G \to \mathcal{O}^\times$ a character with $\Upsilon(c) = -1$, and $x$ a cocycle for $\Upsilon^{-1}$ with values in an $\mathcal{O}$-module $V$. Show that $2x + \delta a$ vanishes at $c$, where $a = x(c)$ and $\delta a(g) = \Upsilon(g)^{-1} a - a$. Deduce that the normalization $x(c) = 0$ in the component $C_\nu$ of Section 5 loses at most a factor $2$ in the length, for every odd prime $\ell$.

*Hint.* $\delta a(c) = -2a$. For the length, the map $x \mapsto 2x + \delta x(c)$ is $\mathcal{O}$-linear, and for $\ell$ odd multiplication by $2$ is injective on $V = \mathcal{O}/\ell^\nu$.

**Exercise 4.** Let $N \ge 1$, $\ell$ a prime, $y$ an integer with $N \le y$ and $\ell \le y^2$, and $M = N\ell^2$. Show that $y \ge 2$, that $M \le y^5$, and that $\varphi(M) + M^3 + 5M^2 + M \le y^{20}$. This is the count of detecting points in Section 7.

*Hint.* $\ell \ge 2$ gives $y^2 \ge 2$. Then $\varphi(M) + M^3 + 5M^2 + M \le y^{15} + 5y^{10} + 2y^5$, and $y^{20} \ge 32\, y^{15}$ for $y \ge 2$.

**Exercise 5.** In the main theorem of Section 7, put $y = N + t + 3$ and assume $X_e \le 2^{(N+e+3)^6}$ for $0 < e < t$. Show that $4\varphi(N) \cdot 4X_e^2 \le 2^{4y^6}$ and that $\big(\prod_{0 < e < t} 4\varphi(N) \cdot 4X_e^2\big)^{y^{20}} \le 2^{4y^{27}}$. What is the integer $X$ for $t = 0$ and for $t = 1$? Which parts of the theorem are then empty or trivial?

*Hint.* $16\varphi(N) \le 16y \le 2^{2y^6}$. There are fewer than $y$ factors. For $t \le 1$ the product is empty, so $X = h_E$, and only the case $e = 0$ remains.

**Exercise 6.** Let $N = 5$ and $\ell = 3$, and let $\mathcal{O} = \mathbb{Z}_3$. Show that $\mathbb{Z}_3$ does not have enough roots of unity for the characters mod $5$, in the sense of Section 7. Find all characters of $(\mathbb{Z}/5)^\times$ with values in $\mathbb{Z}_3^\times$, and show that the orthogonality relation $\sum_\psi \psi(t) = 0$ for $t \ne 1$ fails at $t = 4$. Which step of the proof of the lemma on character components fails? How does the argument avoid this case?

*Hint.* The roots of unity in $\mathbb{Z}_3$ are $\pm 1$, and $(\mathbb{Z}/5)^\times$ is cyclic of order $4$. Only the two characters of order dividing $2$ have values in $\mathbb{Z}_3$. For the last question, read the lemma on large coefficient rings at the end of Section 7.

## Notes and references

The classical theory of Sections 2 to 4 is in L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Graduate Texts in Mathematics 83, Springer, 1997. Chapter 4 has the generalized Bernoulli numbers, the class number formula and the minus part (Theorem 4.17). Chapter 5 has the $p$-adic L-functions. Chapter 6 has the Gauss sums and Jacobi sums (Section 6.2) and Stickelberger's theorem (Theorem 6.10). Chapter 7 builds the $p$-adic L-functions from Stickelberger elements. Chapter 15 proves the main conjecture by the method of Thaine, Kolyvagin and Rubin.

The annihilation of Section 5 has the shape of the theorem of J. Coates and W. Sinnott, An analogue of Stickelberger's theorem for the higher K-groups, Invent. Math. 24 (1974), and of its continuation by G. Banaszak and W. Gajda, J. Number Theory 58 (1996). The source does not use K-theory. It works with cocycles for the twisted characters $\mathrm{cyc}^e\psi$, and its annihilator $4X^2$ comes from one Jacobi quotient and Artin reciprocity.

The Euler system method of Section 6 is due to V. A. Kolyvagin, Euler systems, in *The Grothendieck Festschrift*, Vol. II, Progress in Mathematics 87, Birkhäuser, 1990. K. Rubin wrote the version for class groups of cyclotomic fields in Kolyvagin's system of Gauss sums, in *Arithmetic Algebraic Geometry* (Texel 1989), Progress in Mathematics 89, Birkhäuser, 1991, and the general theory in *Euler Systems*, Annals of Mathematics Studies 147, Princeton University Press, 2000. The source cites Chapter III, Section 4 of the book for the Kolyvagin derivative classes. The source uses Kolyvagin's descent only to find few points that detect a module. It does not compute the order of an eigenspace.

The bound of Section 7 is an upper bound for the length of a module of cocycles. For large $\ell$ the order of the corresponding odd parts follows from the main conjecture: B. Mazur and A. Wiles, Class fields of abelian extensions of $\mathbb{Q}$, Invent. Math. 76 (1984), and, for abelian fields, C. Greither, Class groups of abelian fields, and the main conjecture, Ann. Inst. Fourier 42 (1992), Theorem 3.2. The source proves neither statement, and it does not compare its module with $\text{Ш}^1$. It needs one integer $X$, explicit in size, that works for all $\ell$ at once, and it pays for this with the crude exponents $y^6$, $y^{20}$ and $y^{27}$. Only $\log X$ enters the argument, through the negligible error terms in [the denominator bound](/chapter/denominator-bound/).

For the CM fields and their complex conjugation, see [CM fields](/chapter/cm-fields/). For class field theory, used in the case $e = 0$ and in the count of detecting points, see [class field theory](/chapter/class-field-theory/).
