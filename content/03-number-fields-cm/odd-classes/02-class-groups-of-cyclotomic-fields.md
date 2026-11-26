---
title: Class groups of cyclotomic and CM fields
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Class groups of cyclotomic and CM fields

This section recalls the classical theory behind the bound of this chapter. It has no new results and no proofs of the deep theorems. It fixes the notation, and it shows which classical results the source replaces by weaker statements. The source of each result is given in the text. The notes in Section 7 collect them.

### Class groups and unramified homomorphisms

Let $K$ be a number field with ring of integers $\mathcal{O}_K$. The class group $\mathrm{Cl}(K)$ is the group of fractional ideals modulo principal ideals. It is finite (Neukirch, *Algebraic Number Theory*, Ch. I, Theorem 6.3), and its order $h_K$ is the class number. By class field theory, the Hilbert class field $H$ of $K$ is the maximal abelian extension of $K$ that is unramified at all places, and the Artin map is an isomorphism $\mathrm{Cl}(K) \cong \mathrm{Gal}(H/K)$ (Neukirch, Ch. VI). This volume treats class field theory in [class field theory on finite ideles](/chapter/class-field-theory/).

For a finite abelian group $A$ of exponent dividing $m$, homomorphisms out of $\mathrm{Gal}(\bar K/K)$ that factor through $\mathrm{Gal}(H/K)$ are the same as homomorphisms out of $\mathrm{Cl}(K)$. So for a prime $\ell$ and $n \ge 0$,
$$\mathrm{Hom}_{\mathrm{cont}}^{\mathrm{unr}}(\mathrm{Gal}(\bar K/K), \mathbb{Z}/\ell^n) \cong \mathrm{Hom}(\mathrm{Cl}(K), \mathbb{Z}/\ell^n),$$
where the left side is the group of continuous homomorphisms that are trivial on every inertia group. The order of the right side divides $h_K$. This is the case $e = 0$ of the bound of this chapter. The source proves it in this form, with coefficients in $\mathcal{O}/\ell^n$ for a ring $\mathcal{O}$ of integers of a finite extension of $\mathbb{Q}_\ell$: the length over $\mathcal{O}$ is at most the valuation of $h_K$ in $\mathcal{O}$. Section 6 states it.

### The minus part of a CM field

A CM field is a totally complex quadratic extension $E$ of a totally real field $E^+$. The chapter [CM fields](/chapter/cm-fields/) of this volume defines them and gives criteria. Complex conjugation induces one automorphism $j$ of $E$, the same for every complex embedding, and $E^+$ is its fixed field. The cyclotomic field $\mathbb{Q}(\mu_N)$ with $N > 2$ is a CM field, and $j$ is $\zeta \mapsto \zeta^{-1}$ on roots of unity. Each subfield of $\mathbb{Q}(\mu_N)$ that is not real is a CM field.

The class number $h_{E^+}$ divides $h_E$ (Washington, *Introduction to Cyclotomic Fields*, second edition, Ch. 4). The quotient $h_E^- = h_E / h_{E^+}$ is the relative class number, or minus class number. Let $\ell$ be an odd prime, and let $A$ be the $\ell$-part of $\mathrm{Cl}(E)$. The automorphism $j$ acts on $A$ with $j^2 = 1$, and $2$ is invertible on $A$, so
$$A = A^+ \oplus A^-, \qquad A^\pm = \{a \in A : j a = \pm a\}.$$
The norm map and the extension of ideals identify $A^+$ with the $\ell$-part of $\mathrm{Cl}(E^+)$, so $|A^-|$ is the $\ell$-part of $h_E^-$ (Exercise 1). The minus part is the part that analytic formulas control. For $E = \mathbb{Q}(\mu_N)$ there is the formula
$$h_E^- = Q w \prod_{\chi \text{ odd}} \Big( -\frac{1}{2} B_{1,\chi} \Big),$$
where the product is over the odd Dirichlet characters $\chi$ of $\mathrm{Gal}(E/\mathbb{Q}) \cong (\mathbb{Z}/N)^\times$, $w$ is the number of roots of unity in $E$, and $Q \in \{1, 2\}$ is the unit index (Washington, Theorem 4.17). The plus part has no such formula in terms of Bernoulli numbers. Its size is tied to the units, and it is much harder to control.

### Generalized Bernoulli numbers and L-values

Let $\chi$ be a Dirichlet character of conductor $f$. The generalized Bernoulli numbers $B_{k,\chi}$ are defined by
$$\sum_{a=1}^{f} \chi(a) \frac{T e^{aT}}{e^{fT} - 1} = \sum_{k \ge 0} B_{k,\chi} \frac{T^k}{k!}.$$
For each multiple $F$ of $f$ one has $B_{k,\chi} = F^{k-1} \sum_{a=1}^{F} \chi(a) B_k(a/F)$, where $B_k(X)$ is the Bernoulli polynomial (Washington, Proposition 4.1). For $k \ge 1$ one has $L(1-k, \chi) = -B_{k,\chi}/k$ (Washington, Theorem 4.2). For $\chi \ne 1$, $B_{k,\chi} = 0$ when $\chi(-1) \ne (-1)^k$. In particular $B_{1,\chi} = \frac{1}{f}\sum_{a=1}^{f} \chi(a) a$ for $\chi \ne 1$, and it is $0$ for $\chi$ even. So only odd characters appear in the formula for $h^-$.

The source uses the values $L(\chi, -e)$ for $e \ge 1$ and $\chi$ not necessarily primitive. They vanish exactly when $\chi(-1) = (-1)^e$. Section 3 states this as [Lemma](/decl/New.OddPart.LFunction_neg_nat_eq_zero_iff/), and it proves the relation between $L(\chi, -e)$ and the twisted Bernoulli sums. Dirichlet L-functions are the subject of [Dirichlet L-functions](/chapter/dirichlet-l-functions/) in Volume 2.

### Stickelberger's theorem

Let $G = \mathrm{Gal}(\mathbb{Q}(\mu_N)/\mathbb{Q})$, and let $\sigma_a \in G$ be the element with $\sigma_a(\zeta) = \zeta^a$ for $\zeta \in \mu_N$. Write $\{y\} = y - \lfloor y \rfloor$ for the fractional part. The Stickelberger element is
$$\theta = \sum_{\substack{0 < a < N \\ (a, N) = 1}} \Big\{ \frac{a}{N} \Big\} \sigma_a^{-1} \in \mathbb{Q}[G].$$
**Stickelberger's theorem.** If $\beta \in \mathbb{Z}[G]$ and $\beta\theta \in \mathbb{Z}[G]$, then $\beta\theta$ annihilates $\mathrm{Cl}(\mathbb{Q}(\mu_N))$ (Washington, Theorem 6.10; Ireland and Rosen, *A Classical Introduction to Modern Number Theory*, second edition, Ch. 14).

The proof factors Gauss sums. For a prime $p \equiv 1 \bmod N$ and a prime $\mathfrak{P}$ above $p$ in $\mathbb{Q}(\mu_{Np})$, let $\mathfrak{p}$ be the prime of $\mathbb{Q}(\mu_N)$ below $\mathfrak{P}$. The $N$-th power of the Gauss sum of a character of order $N$ of $\mathbb{F}_p^\times$ lies in $\mathbb{Q}(\mu_N)$, and the ideal that it generates is $\mathfrak{p}^{N\theta}$, for a suitable choice of the character (Washington, §6.2). Every ideal class contains prime ideals of degree one, so this gives the annihilation.

An element $\beta$ of the required kind is $c - \sigma_c$ for an integer $c$ prime to $N$. A direct computation gives
$$(c - \sigma_c)\theta = \sum_{a} \Big( c\Big\{\frac{a}{N}\Big\} - \Big\{\frac{ca}{N}\Big\} \Big) \sigma_a^{-1} = \sum_{a} \Big\lfloor \frac{ca}{N} \Big\rfloor \sigma_a^{-1},$$
for $a$ in $(0, N)$ prime to $N$. The integers $\lfloor ca/N \rfloor$ are the coefficients of the Stickelberger sums of the source. For a character $\chi$ of $G$, the image of $\theta$ under $\chi$ is $B_{1,\bar\chi}$ when $\chi$ is primitive of conductor $N$. So, on the $\chi$-part of the class group, Stickelberger's theorem gives annihilation by $(c - \chi(c)) B_{1, \bar\chi}$, up to the passage between $G$ and its characters. This is the model for the source. The source replaces the class group by a module of Galois cocycles, the Gauss sums by Jacobi-type quotients, and $B_{1,\chi}$ by $B_{e+1,\chi}$.

### Eigenspaces and the theorems of Herbrand and Ribet

Let $p$ be an odd prime, $F = \mathbb{Q}(\mu_p)$ and $\Delta = \mathrm{Gal}(F/\mathbb{Q})$. Let $\omega : \Delta \to \mathbb{Z}_p^\times$ be the Teichmüller character, the character with $\sigma(\zeta) = \zeta^{\omega(\sigma)}$ for $\zeta \in \mu_p$. Let $A$ be the $p$-part of $\mathrm{Cl}(F)$. As $|\Delta| = p - 1$ is prime to $p$, $A$ is the direct sum of the eigenspaces
$$A(\omega^i) = \{ a \in A : \sigma a = \omega(\sigma)^i a \text{ for all } \sigma \in \Delta \}, \qquad 0 \le i \le p - 2.$$
Complex conjugation acts on $A(\omega^i)$ by $(-1)^i$, so $A^-$ is the sum of the odd eigenspaces. Stickelberger's theorem, applied eigenspace by eigenspace, gives the following.

**Herbrand's theorem.** Let $i$ be odd with $3 \le i \le p - 2$. If $A(\omega^i) \ne 0$, then $p \mid B_{p-i}$ (Washington, §6.3).

**Ribet's theorem.** The converse holds: if $p \mid B_{p-i}$, then $A(\omega^i) \ne 0$ (K. Ribet, A modular construction of unramified p-extensions of $\mathbb{Q}(\mu_p)$, Invent. Math. 34 (1976)).

Ribet's proof uses congruences between Eisenstein series and cusp forms, and the Galois representations attached to the cusp forms. It is a model for the method of the whole source, which also builds Galois representations from congruences. The present chapter needs only the direction of Herbrand: an upper bound for odd eigenspaces in terms of Bernoulli numbers.

### The main conjecture

The main conjecture of Iwasawa theory for $\mathbb{Q}$, proved by Mazur and Wiles (B. Mazur, A. Wiles, Class fields of abelian extensions of $\mathbb{Q}$, Invent. Math. 76 (1984)), says that the characteristic ideal of an odd eigenspace of the inverse limit of the $p$-parts of the class groups of $\mathbb{Q}(\mu_{p^k})$ is generated by a Kubota-Leopoldt $p$-adic L-function. A consequence at the bottom level is an exact formula: for odd $i \ne 1$, the order of $A(\omega^i)$ is the $p$-part of $B_{1,\omega^{-i}}$. Washington, Ch. 15, gives a proof of the main conjecture by the Euler systems of Thaine, Kolyvagin and Rubin. The $p$-adic L-functions are in Washington, Ch. 5 and Ch. 7. Greither extended the main conjecture to abelian fields, the prime $2$ included (C. Greither, Class groups of abelian fields, and the main conjecture, Ann. Inst. Fourier 42 (1992)).

The source does not prove the main conjecture. It proves only an upper bound at finite level. The upper bound is the half of the main conjecture that the Euler system method gives, and the source takes that method in a form at finite level, with explicit sizes. Kolyvagin's Euler system of Gauss sums gives upper bounds for the odd eigenspaces (K. Rubin, Kolyvagin's system of Gauss sums, in *Arithmetic Algebraic Geometry*, Texel 1989, Progr. Math. 89, 1991). Section 5 explains the version of the source.

### Twists and the odd part of Ш

The source needs a bound not only for $\mathrm{Cl}(E)$ but for Galois cohomology with coefficients in the Tate twists $\mathcal{O}/\ell^n(-e)$. Here is the classical link. Let $F = E(\mu_{\ell^n})$, and suppose that $\ell \nmid [F : E]$. Inflation and restriction identify $H^1(E, \mathbb{Z}/\ell^n(-e))$ with the classes in $\mathrm{Hom}(\mathrm{Gal}(\bar F/F), \mathbb{Z}/\ell^n)$ on which $\mathrm{Gal}(F/E)$ acts through one power of the cyclotomic character. Over $F$ the twist is trivial. So the classes that are unramified at all places and trivial at the places above $\ell$ correspond to one eigenspace of a quotient of the $\ell$-part of $\mathrm{Cl}(F)$. These classes form the Tate-Shafarevich group $\text{Ш}^1(E, \mathbb{Z}/\ell^n(-e))$, up to the local conditions above $\ell$. The odd part, for the action of complex conjugation, corresponds to a minus part of the class group of a cyclotomic field. So the odd part is the part that Stickelberger elements, Bernoulli numbers and the main conjecture control.

For $e \ge 1$ the relevant Stickelberger elements carry a factor $a^e$, and the relevant L-values are $L(\psi, -e)$. The analogue of Stickelberger's theorem in this setting is due to Coates and Sinnott (J. Coates, W. Sinnott, An analogue of Stickelberger's theorem for the higher K-groups, Invent. Math. 24 (1974)). The source works with exactly these twisted sums,
$$\sum_{0 \le a < Nm} \Big\lfloor \frac{ca}{Nm} \Big\rfloor a^e \psi(a),$$
for a Dirichlet character $\psi$ mod $N$ with $\psi(-1) = -(-1)^e$. Section 3 links them to $B_{e+1,\psi}$.

The source does not prove the identification of this paragraph. It defines a module of cocycles directly, with the conditions of $\text{Ш}^1$ written as conditions on cocycles, and it bounds that module. Section 6 gives the definition, and its remark on the formalization explains why the argument needs no more.
