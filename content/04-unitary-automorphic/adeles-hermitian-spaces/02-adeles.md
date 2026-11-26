---
title: Adeles of a number field
lean:
  - Lib/Adelic/Adeles/Basic.lean
  - Lib/Adelic/Adeles/AdditiveCharacter.lean
  - Lib/Adelic/Adeles/StrongApproximation.lean
  - Lib/Adelic/Adeles/IdeleModulus.lean
decls:
  - New.𝔸f
  - New.PlaceEmbedding
  - New.CMType
  - New.𝔸
  - New.toAdele
  - New.Ô
  - New.uniformizer
  - New.isCompact_Ô
  - New.denseRange_algebraMap_finAdele
  - New.exists_sub_mem_Ô
  - New.strong_approximation
  - New.stdAddChar
  - New.stdAddChar_toAdele
  - New.mem_ratAdeles_of_stdAddChar_eq_one
  - New.volume_Ô
  - New.isCovolOneLattice_ratAdeles
  - New.ideleAbs_toAdele
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Adeles of a number field

This section recalls the adeles of a number field and gives the form in which the source defines them. The classical facts are the local compactness of the adeles, the discreteness and cocompactness of the field, strong approximation, the self-duality of the field under the standard character, and the product formula. The source proves each of these for a totally complex field. Every field in this book to which they apply is a CM field, so it is totally complex.

### The classical adele ring

Let $K$ be a number field with ring of integers $\mathcal{O}_K$. A *place* of $K$ is a class of absolute values. The finite places correspond to the nonzero prime ideals $\mathfrak{p}$ of $\mathcal{O}_K$. The infinite places correspond to the real embeddings $K \to \mathbb{R}$ and to the pairs $\{\sigma, \bar\sigma\}$ of complex embeddings $K \to \mathbb{C}$. Let $r_1$ and $r_2$ be the numbers of real and complex places, so that $r_1 + 2r_2 = [K : \mathbb{Q}]$. For a place $v$, let $K_v$ be the completion. For a finite place, let $\mathcal{O}_v$ be the ring of integers of $K_v$ and let $q_v = \#(\mathcal{O}_v/\mathfrak{p}_v)$ be the norm of the place.

The *adele ring* $\mathbb{A}_K$ is the restricted product of the fields $K_v$ with respect to the subrings $\mathcal{O}_v$. An element is a family $(x_v)$ with $x_v \in \mathcal{O}_v$ for all but finitely many $v$. The open sets of the product $\prod_{v \mid \infty} K_v \times \prod_{v < \infty} \mathcal{O}_v$ and their translates are a base of the topology. The *finite adeles* $\mathbb{A}_{K,f}$ are the same restricted product over the finite places only, and $\mathbb{A}_K = K_\infty \times \mathbb{A}_{K,f}$ with $K_\infty = \prod_{v \mid \infty} K_v = \mathbb{R}^{r_1} \times \mathbb{C}^{r_2}$. Weil, *Basic Number Theory*, Chapter IV, and Cassels, *Global fields*, Chapter II of Cassels and Fröhlich, *Algebraic Number Theory*, give the standard account.

The classical facts are these.

1. $\mathbb{A}_K$ is a locally compact ring. The subring $\hat{\mathcal{O}}_K = \prod_{v < \infty} \mathcal{O}_v$ of $\mathbb{A}_{K,f}$ is compact and open.
2. The diagonal embedding $K \to \mathbb{A}_K$ has a discrete image, and the quotient $\mathbb{A}_K / K$ is compact.
3. *Strong approximation.* For every place $v_0$, the field $K$ is dense in the restricted product over the places $v \neq v_0$. In particular $K$ is dense in $\mathbb{A}_{K,f}$.
4. *Self-duality.* Let $\psi = \prod_v \psi_v$ be the standard character of Tate, with $\psi_v(x) = e(-\mathrm{tr}_{K_v/\mathbb{R}}\, x)$ at an infinite place and $\psi_v(x) = e(\lambda_v(x))$ at a finite place, where $e(t) = e^{2\pi i t}$ and $\lambda_v(x)$ is a rational number that is congruent to $\mathrm{tr}_{K_v/\mathbb{Q}_p}(x)$ modulo $\mathbb{Z}_p$. Then $\psi$ is trivial on $K$, and an adele $y$ with $\psi(ay) = 1$ for all $a \in K$ lies in $K$.
5. *Measures.* Let $\mu$ be the measure that is self-dual for $\psi$. At a complex place it is twice the Lebesgue measure $dx\,dy$. At a finite place it gives $\mathcal{O}_v$ the mass $N(\mathfrak{d}_v)^{-1/2}$, where $\mathfrak{d}_v$ is the local different. Then the quotient $\mathbb{A}_K / K$ has mass $1$.
6. *Product formula.* For $x \in K^\times$, $\prod_v |x|_v = 1$, where $|x|_v$ is the normalized absolute value. At a complex place, $|x|_v$ is the square of the usual absolute value.

Facts 2, 4 and 5 are in Tate's thesis, Section 4.1, which is Chapter XV of Cassels and Fröhlich. Fact 3 is in Cassels, *Global fields*, §15.

### The adeles of the source

The source defines the finite adeles as in Mathlib. It defines the adeles by one copy of $\mathbb{C}$ at each infinite place.

**Definition (Finite adeles).** Let $E$ be a number field. A *finite place* of $E$ is a nonzero prime ideal of $\mathcal{O}_E$. The *finite adeles* $\mathbb{A}_{E,f}$ are the restricted product of the completions $E_w$ over the finite places $w$, with respect to the rings of integers $\mathcal{O}_w$. For a finite place $w$, the number $q_w$ is the absolute norm of the prime ideal.

Lean: `New.𝔸f`, `New.FinPlace`, `New.LocField`, `New.LocInt`, `New.FinPlace.q` (Lib/Adelic/Adeles/Basic.lean).

**Definition (Place embeddings and CM types).** A *choice of place embeddings* of a field $E$ is a complex embedding $\Phi_w : E \to \mathbb{C}$ for each infinite place $w$, such that $\Phi_w$ induces $w$. The source calls a CM number field with a choice of place embeddings a field with a *CM type*.

Lean: `New.PlaceEmbedding`, `New.CMType` (Lib/Adelic/Adeles/Basic.lean).

**Definition (The adeles of the source).** Let $E$ be a number field. The ring $\mathbb{A}_E$ of the source is the product $\mathbb{C}^{\{w \mid \infty\}} \times \mathbb{A}_{E,f}$ of one copy of $\mathbb{C}$ for each infinite place of $E$ with the finite adeles. Given place embeddings, the *diagonal embedding* $E \to \mathbb{A}_E$ sends $x$ to $((\Phi_w(x))_w, x)$.

Lean: `New.𝔸`, `New.toAdele` (Lib/Adelic/Adeles/Basic.lean).

**Remark (Formalization).** The ring `New.𝔸 E` is the adele ring of $E$ only if $E$ is totally complex. At a real place $w$ the classical factor is $\mathbb{R}$, and the source puts $\mathbb{C}$ there. For a field with a real place, the image of $E$ in `New.𝔸 E` is still discrete, but the quotient is not compact, since $\mathbb{C}/\mathbb{R}$ is not. So each result of this section that needs Fact 2 has the hypothesis that $E$ is totally complex. A CM field is totally complex, so the argument loses nothing. The name of the ring does not show the hypothesis; the findings of the plan record this as F-057.

**Remark (Formalization).** The diagonal embedding depends on the choice of $\Phi_w$. If one replaces $\Phi_w$ by its conjugate $\bar\Phi_w$, the component at $w$ changes by complex conjugation. The source has a global instance of low priority that takes for $\Phi_w$ the embedding that Mathlib attaches to $w$. A field with a CM type carries its own choice. Every later object that uses the infinite components, such as the standard character and the forms at the infinite places, depends on this choice. The source also has a global instance, made by choice, that decides the equality of infinite places.

**Definition (Integral adeles).** The ring $\hat{\mathcal{O}}_E$ is the subring of finite adeles $x$ with $|x_w|_w \leq 1$ at every finite place $w$.

Lean: `New.Ô`, `New.mem_Ô` (Lib/Adelic/Adeles/Basic.lean).

**Proposition.** The ring $\hat{\mathcal{O}}_E$ is compact and open in $\mathbb{A}_{E,f}$.

Lean: `New.isCompact_Ô`, `New.isOpen_Ô` (Lib/Adelic/Adeles/Basic.lean).

*Proof.* By the definition of the restricted product, $\prod_w \mathcal{O}_w$ is open in it, with the product topology. Each $\mathcal{O}_w$ is compact, so the product is compact by Tychonoff's theorem. $\square$

**Definition (Uniformizer).** For each finite place $w$, a *uniformizer* $\varpi_w$ is an element of $E_w$ of valuation $1$. The source fixes one for each $w$ by choice.

Lean: `New.uniformizer`, `New.v_uniformizer` (Lib/Adelic/Adeles/Basic.lean).

**Remark (Formalization).** The uniformizer is chosen with `choose`, so the source knows nothing about it beyond its valuation. Results that are true for every uniformizer do not depend on the choice. One field of the Weil data of Volume 6 asks that a character takes the value $-1$ at the chosen uniformizer of each place that is fixed by conjugation. For an unramified character this value does not depend on the choice.

### Density

The source proves the density of $E$ in its finite adeles directly, by the Chinese remainder theorem.

**Theorem (Density in the finite adeles).** Let $E$ be a number field. The image of $E$ is dense in $\mathbb{A}_{E,f}$. The image of $\mathcal{O}_E$ is dense in $\hat{\mathcal{O}}_E$.

Lean: `New.denseRange_algebraMap_finAdele`, `New.denseRange_algebraMap_Ô` (Lib/Adelic/Adeles/Basic.lean).

*Proof.* A base of neighbourhoods of $0$ in $\hat{\mathcal{O}}_E$ is the family of ideals $N\hat{\mathcal{O}}_E$ for integers $N \geq 1$. The map $\mathcal{O}_E / N\mathcal{O}_E \to \hat{\mathcal{O}}_E / N\hat{\mathcal{O}}_E$ is onto by the Chinese remainder theorem, since only the finitely many places above the primes dividing $N$ matter. So for every $x \in \hat{\mathcal{O}}_E$ and every $N$ there is $b \in \mathcal{O}_E$ with $b - x \in N\hat{\mathcal{O}}_E$. This is the second claim. For the first, let $x$ be a finite adele. Some integer $N \geq 1$ has $Nx \in \hat{\mathcal{O}}_E$, since $x_w$ is integral at all but finitely many $w$. Approximate $Nx$ by elements of $\mathcal{O}_E$ and divide by $N$. Multiplication by $1/N$ is a homeomorphism of $\mathbb{A}_{E,f}$. $\square$

**Corollary.** Every finite adele $x$ is the sum $x = a + y$ of an element $a$ of $E$ and an integral adele $y \in \hat{\mathcal{O}}_E$.

Lean: `New.exists_sub_mem_Ô` (Lib/Adelic/Adeles/Basic.lean).

*Proof.* The set $x + \hat{\mathcal{O}}_E$ is open and not empty, so it meets the dense set $E$. $\square$

Strong approximation in the full adeles is a statement about the infinite components too. The source proves it by duality, in the following form.

**Theorem (Strong approximation).** Let $E$ be totally complex, with place embeddings. Let $S$ be a nonempty set of finite places of $E$, and let $e_S$ be the adele that is $1$ at the places of $S$ and $0$ at the other finite places and at the infinite places. Then the sums $r + e_S u$, with $r \in E$ and $u \in \mathbb{A}_E$, are dense in $\mathbb{A}_E$.

Lean: `New.strong_approximation`, `New.Exchange.idemAdele` (Lib/Adelic/Adeles/StrongApproximation.lean).

*Proof.* Let $B$ be the closure of the subgroup of the sums, and suppose that $B \neq \mathbb{A}_E$. A continuous function $f$ on $\mathbb{A}_E / B$ separates a point from $0$. It is periodic under $E$, so it is a function on the compact group $\mathbb{A}_E / E$. Its Fourier coefficients are indexed by $E$, through the characters $y \mapsto \psi(ay)$ of the self-duality theorem below. The function is also invariant under the adeles $e_S u$, and a character $y \mapsto \psi(ay)$ that is trivial on all of them has $a = 0$, since $S$ is not empty. So $f$ minus its mean has all Fourier coefficients $0$, and it is $0$. This contradicts the choice of $f$. $\square$

**Remark (Formalization).** The classical theorem omits one place $v_0$, which may be infinite. The source omits a nonempty set $S$ of finite places. If $S$ is one finite place $v_0$, the two statements are the same, since $E + E_{v_0}$ is dense in $\mathbb{A}_E$ exactly when $E$ is dense in the restricted product over $v \neq v_0$. The source does not prove the case of an infinite place $v_0$, and the argument does not use it. The source applies the theorem through its form for matrices, `New.Exchange.denseRange_rat_matrix_add`, in the proof of weak approximation for unitary groups (Section 4).

### The standard character and the measures

**Definition (Standard character).** Let $E$ be a number field with place embeddings. The finite character $\psi_f$ of $\mathbb{A}_{E,f}$ is trivial on $\hat{\mathcal{O}}_E$ and equals $e(\mathrm{tr}_{E/\mathbb{Q}}\, a)$ at $a \in E$. The standard character of $\mathbb{A}_E$ is
$$\psi(x) = e\Big(-\sum_{w \mid \infty} 2 \operatorname{Re} x_w\Big)\, \psi_f(x_f).$$

Lean: `New.stdAddChar`, `New.ψf`, `New.ψf_coe`, `New.ψf_eq_one_of_mem` (Lib/Adelic/Adeles/AdditiveCharacter.lean).

The finite character is well defined by the corollary above: two decompositions $x = a + y = a' + y'$ have $a - a' \in E \cap \hat{\mathcal{O}}_E = \mathcal{O}_E$, and $e(\mathrm{tr}\, b) = 1$ for $b \in \mathcal{O}_E$. At a complex place $2 \operatorname{Re} x = \mathrm{tr}_{\mathbb{C}/\mathbb{R}}\, x$. So $\psi$ is Tate's character of Fact 4.

**Theorem (Self-duality).** Let $E$ be totally complex, with place embeddings. Then $\psi(a) = 1$ for every $a \in E$. If an adele $x$ has $\psi(ax) = 1$ for every $a \in E$, then $x$ is in the image of $E$.

Lean: `New.stdAddChar_toAdele`, `New.mem_ratAdeles_of_stdAddChar_eq_one` (Lib/Adelic/Adeles/StrongApproximation.lean).

*Proof.* For $a \in E$, the trace $\mathrm{tr}_{E/\mathbb{Q}}\, a$ is the sum of $\Phi_w(a) + \overline{\Phi_w(a)} = 2 \operatorname{Re} \Phi_w(a)$ over the infinite places, since $E$ is totally complex. So the two factors of $\psi(a)$ cancel. For the converse, let $T(b) = \sum_w 2 \operatorname{Re}(\Phi_w(b)\, x_w)$ for $b \in E$. The values of $\psi_f$ are $e(q)$ with $q$ rational, so the hypothesis at $b$ gives that $T(b)$ is rational for every $b$. Write the infinite part of $x$ in the real basis $(\Phi_w(v_i))_w$ of $\mathbb{C}^{r_2}$, where $(v_i)$ is an integral basis of $E$. Pairing with the trace-dual basis shows that the coordinates are rational. So the infinite part of $x$ is that of some $a \in E$. Then $\psi_f(bx_f) = \psi_f(ba)$ for every $b \in E$. By density, $\psi_f(tx_f) = \psi_f(ta)$ for every finite adele $t$, and the pairing $\psi_f(t\,\cdot)$ separates the points of $\mathbb{A}_{E,f}$. So $x_f = a$. $\square$

**Theorem (Measures).** Let $E$ be a number field with $r_2$ complex places and discriminant $d_E$. The source puts on $\mathbb{A}_{E,f}$ the Haar measure with
$$\operatorname{vol}(\hat{\mathcal{O}}_E) = \frac{2^{r_2}}{\sqrt{|d_E|}}.$$
It puts on $\mathbb{A}_E$ the product of this measure with the Lebesgue measure $dx\,dy$ on each copy of $\mathbb{C}$. If $E$ is totally complex, the image of $E$ is a lattice of covolume one in $\mathbb{A}_E$: it is discrete, the quotient is compact and has mass $1$, and some compact set meets every coset.

Lean: `New.volume_Ô`, `New.volÔ`, `New.isCovolOneLattice_ratAdeles`, `New.IsCovolOneLattice` (Lib/Adelic/Adeles/AdditiveCharacter.lean).

*Proof.* The first claim is the definition of the measure. For the second, the map $\mathcal{O}_E \to \mathbb{C}^{r_2}$ by the place embeddings has image a lattice of covolume $2^{-r_2}\sqrt{|d_E|}$ for the Lebesgue measure. A fundamental domain for $E$ in $\mathbb{A}_E$ is a fundamental domain $D$ of this lattice times $\hat{\mathcal{O}}_E$, by the corollary above and $E \cap \hat{\mathcal{O}}_E = \mathcal{O}_E$. Its mass is $2^{-r_2}\sqrt{|d_E|} \cdot 2^{r_2}/\sqrt{|d_E|} = 1$. $\square$

**Remark (Formalization).** The measure of the source is Tate's self-dual measure $\mu$ of Fact 5, but its local factors are not Tate's. Tate puts $2\,dx\,dy$ at each complex place and $|d_E|^{-1/2}$ on $\hat{\mathcal{O}}_E$, since $\prod_w N(\mathfrak{d}_w) = |d_E|$. The source puts $dx\,dy$ at each complex place and moves the factor $2^{r_2}$ to the finite part. The two product measures are the same. So the global statements agree, but a local computation at a complex place must use the Lebesgue measure.

### The idele modulus

For an idele $x \in \mathbb{A}_E^\times$, the source defines $|x| = \prod_{w \mid \infty} |x_w|^{m_w} \prod_{w < \infty} \|x_w\|_w$, where $m_w = 2$ at a complex place and $\|\cdot\|_w$ is the normalized absolute value of $E_w$.

**Theorem (Product formula).** Let $E$ be totally complex, with place embeddings. For $x \in E^\times$, the idele modulus of the image of $x$ is $1$.

Lean: `New.ideleAbs_toAdele`, `New.ideleAbs` (Lib/Adelic/Adeles/IdeleModulus.lean).

*Proof.* The product of the finite factors is $|N_{E/\mathbb{Q}}(x)|^{-1}$, by the factorization of the principal ideal $(x)$. The product of the infinite factors is $|N_{E/\mathbb{Q}}(x)|$. $\square$
