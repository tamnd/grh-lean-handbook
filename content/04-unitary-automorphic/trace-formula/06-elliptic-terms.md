---
title: The elliptic terms and the comparison
lean:
  - Lib/Adelic/TraceFormula/TraceComparison.lean
  - Lib/Adelic/TraceFormula/ChangingSigns.lean
  - Lib/Adelic/TraceFormula/OrbitalUnfolding.lean
  - Lib/DiscreteSeries/Character/FormalDegree.lean
decls:
  - New.Space.orbitalIntegral_eq_prod_mul
  - New.signedClasses
  - New.Variety.exists_hasSignType_mul_iff
  - New.Space.exists_perm_signedClasses
  - New.Space.exists_classIntegral_eq
  - New.Orbital.harish_chandra_degree_and_orbital
  - New.Space.sum_prod_integral_dsKernel
  - New.Space.exists_geometricSide_singleton_eq
  - New.trace_comparison
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The elliptic terms and the comparison

The terms that remain are those of the irreducible $R$ with all complex roots on the unit circle. For these the rational points are elliptic, and their orbital integrals split into a real and a finite factor. This section shows that the term $I_R$ is a number $c_R$ that does not depend on the space, times a product of characters of compact unitary groups. Two ingredients make the comparison work. The first is a bijection of conjugacy classes between spaces of different signs, which keeps the finite orbital integrals. The second is Harish-Chandra's formula, which turns the sum of the real orbital integrals over the orders of the eigenvalues into a character of the compact form. The section ends with the comparison of traces.

### Notation at infinity

At an infinite place $v$ the group $G_v$ is $U(\operatorname{diag} s)$, a group $U(p, q)$ with $p$ signs $+1$ and $q$ signs $-1$. For $z = (z_i) \in (\mathbb{C}^1)^n$ let $\operatorname{diag}_s(z)$ be the diagonal element of $U(\operatorname{diag} s)$ and $\operatorname{diag}_K(z)$ the same element of the compact group $U(N)$. A doubled Harish-Chandra parameter $l : n \to \mathbb{Z}$ for the signs $s$ gives the kernel $e_l$ of the discrete series of $U(\operatorname{diag} s)$ (`New.HCParam.dsKernel`), and the kernel $e_\lambda = \prod_v e_{l_v}$ on $G_\infty$ (`New.typeKernel`). The *gap condition with constant $A$* asks that the entries of $l$ are distinct, have the parity of $N - 1$, and that entries $l_i, l_j$ with $s_i \neq s_j$ satisfy $|l_i - l_j| \geq 2(500 N^3 + A)$ (`New.HCParam.HasLargeGap`). For definite signs the last part is empty. Under the gap condition with constant $B$, $e_\lambda$ is a cusp kernel of order $B$ (`New.isCuspKernel_typeKernel`). For the parameter $l$ read for the signs $1$, let $\chi_{l}$ be the character of the irreducible representation of $U(N)$ whose highest weight is the lowest $K$-type of $l$ for the compact group $U(N)$ (`New.HCParam.lowestKType`, `New.HCParam.kTypeChar`). The discrete series and these objects are the subject of [the discrete series](/chapter/discrete-series/).

### Splitting an orbital integral

**Proposition.** Let $\varphi$ be a test function and $l$ a family of parameters with $e_\lambda$ measurable. Let $\gamma$ be a rational point with $\gamma = g\, (t, y)\, g^{-1}$ in $G$ for some $g \in G$, $t \in G_\infty$ and $y \in G_f$. Let $\beta : G_f \to [0, \infty]$ be a function such that $x \mapsto \beta((g^{-1} x)_f)$ is a cutoff for counting measure on $\Gamma_\gamma$. Then
$$ O_\gamma(e_\lambda \otimes \varphi) = \Big( \prod_{v \mid \infty} \int_{G_v} e_{l_v}(h^{-1} t_v h)\, dh \Big) \cdot \int_{G_f} \beta(u)\, \varphi(u^{-1} y u)\, du. $$
Here $\beta(u)$ is read as a real number, with $\infty$ read as $0$.
Lean: `New.Space.orbitalIntegral_eq_prod_mul` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* Substitute $x \mapsto g x$. The integrand is then a product of a function of $x_\infty$ and a function of $x_f$, and the cutoff depends on $x_f$ only. Apply Fubini. $\square$

The factor at infinity is an integral over all of $G_v$, not over $G_v$ modulo a torus. The cutoff $\beta$ depends only on the finite part, so it takes the place of the quotient by $\Gamma_\gamma$.

**Remark (Formalization).** The finite factor is written with a cutoff $\beta$, not with a quotient measure. So the finite factor depends on $\beta$, and the identity holds for every admissible $\beta$. In the comparison the same $\beta$ is used for two spaces whose rational centralisers have the same image in $G_f$ (`New.Space.map_embFin_centralizer_eq`). Then the finite factors agree.

### Signed classes and the change of signs

Let $\gamma$ be an elliptic isometry of a hermitian form $J$ over $E$: $\chi_\gamma$ is irreducible, $\gamma^* J \gamma = J$, and all complex roots of $\chi_\gamma$ have absolute value $1$ (`New.Variety.IsEllipticSimilitude` with multiplier $1$). At an infinite place $v$ the eigenvalues of $\gamma_v$ are distinct, and the eigenlines are orthogonal for $J_v$. The *sign* of $J$ on the eigenline of the $i$-th root is $\pm 1$. In other words, the signs are $\varepsilon_v(i) = \pm 1$ such that $J_v\, p(\gamma_v)$ is positive definite, where $p$ is the polynomial with $p(\lambda_i) = \varepsilon_v(i)$ at the roots $\lambda_i$.

**Definition (Signed classes).** For $R \in E[X]$ and signs $\varepsilon : \{\text{infinite places}\} \times n \to \{\pm 1\}$, the set $\mathcal{C}(R, \varepsilon)$ consists of the frame classes $[x, y]$ such that $\chi_y = R$, and $y$ is an elliptic isometry of a form $J$ with signs $\varepsilon$ on its eigenlines, for which $x$ is an orthonormal frame at the finite places ($x^* J x = 1$).
Lean: `New.signedClasses` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

The source's form of the change of signs is the following.

**Theorem (Change of signs).** Let $Z$ be a set of marks and $L$ a subgroup of $\mathrm{GL}_N(\mathbb{A}_{E,f})$. Let $\eta_\mu$, for $\mu \in Z$, be families of signs with $\prod_v \prod_i \eta_\mu(v, i) = 1$. There is a permutation $f$ of the $\mathrm{GL}_N(E)$-orbits of triples $(q, y, \mu)$, $q \in \mathrm{GL}_N(\mathbb{A}_{E,f}) / L$, $y \in \mathrm{GL}_N(E)$, $\mu \in Z$, with the following property. For every $y$ and $\mu$ there is $U \in \mathrm{GL}_N(\mathbb{A}_{E,f})$ such that:

1. for every multiplier $\nu$, all signs $\varepsilon$, every condition $F$ on Gram matrices and every $x$, the pair $(y, x)$ has type $\varepsilon \eta_\mu$ if and only if $(y, U x)$ has type $\varepsilon$;
2. $U$ commutes with every rational matrix that commutes with $y$;
3. $f$ sends the orbit of $(q, y, \mu)$ to the orbit of $(U q, y, \mu)$.

Lean: `New.Variety.exists_hasSignType_mul_iff` (Lib/Adelic/TraceFormula/ChangingSigns.lean).

Here "type $\varepsilon$" means `New.Variety.HasSignType`: there is a form $\beta$ for which $y$ is an elliptic similitude with multiplier $\nu$, the Gram matrix $x^* \beta x$ satisfies $F$, and the signs at infinity are $\varepsilon$.

*Proof sketch.* Fix $P = \chi_y$ and $\mu$. If $y$ is an elliptic similitude with multiplier $\nu$, there are polynomials $\delta, c \in E[X]$ and $g \in \mathbb{A}_{E,f}[X]$ such that: $\delta$ is prime to $P$; $\eta_\mu(v, i)\, \delta(\lambda_{v,i}) > 0$ at each numbered root $\lambda_{v,i}$ of $P$; $X c \equiv \nu \pmod P$; and $\bar g(c)\, g \equiv \delta \pmod P$ (`New.Variety.exists_coprime_sign_dvd_norm_sub`). The last congruence says that $\delta$ is a norm at the finite places. It comes from a principal idele with prescribed signs whose product with a norm is $1$, and this is where $\prod \eta_\mu = 1$ is used. Put $U = g(y)$. Since $c(y)$ is the adjoint of $y$ for $\beta$, the Gram matrix of $\beta$ in the frame $U x$ is the Gram matrix of $\beta\, \delta(y)$ in the frame $x$ (`New.Variety.gram_aeval_eq_map_mul_aeval`). The form $\beta\, \delta(y)$ has the signs of $\beta$ times $\eta_\mu$ on the eigenlines. This gives item 1. Since $U$ is a polynomial in $y$, item 2 holds. The polynomial $g$ depends only on $P$ and $\mu$, so $U$ is compatible with conjugation of $y$, and item 3 defines a permutation of the orbits. $\square$

**Remark (Formalization).** The source states the change of signs for marked triples with an arbitrary set of marks and a general condition $F$, since it is used elsewhere. Here only one mark, $\nu = 1$ and $F = \{1\}$ are used. The sketch above follows the steps of the source. This chapter does not give the construction of the principal idele in full.

**Corollary (Matching the classes).** Let $E$ contain a primitive $5040$-th root of unity. Let $\varepsilon, \varepsilon'$ be families of signs, each with product $1$, and let $R \in E[X]$. Then there is a permutation $f$ of the frame classes with $f(\mathcal{C}(R, \varepsilon)) = \mathcal{C}(R, \varepsilon')$, such that: if $y$ is an elliptic isometry of type $\varepsilon$ for the frame $u$, then $f([u, y]) = [x, y]$ for some $x$ such that $(y, x)$ has type $\varepsilon'$ and $u^{-1} a u = x^{-1} a x$ for every rational $a$ that commutes with $y$.
Lean: `New.Space.exists_perm_signedClasses` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* Apply [the change of signs](/decl/New.Variety.exists_hasSignType_mul_iff/) to $\eta = \varepsilon'^{-1} \varepsilon$, which has product $1$, with one mark and with $L$ the unitary group of the identity form over $\mathbb{A}_{E,f}$. Put $x = U u$. Item 2 gives $u^{-1} a u = x^{-1} a x$. $\square$

For a space $V$ of signs $s$ and a family of permutations $\sigma = (\sigma_v)$, the signs $s \circ \sigma_v^{-1}$ list the signs of $V$ in the order of the roots given by $\sigma$. If the number of infinite places is even, the family $(s \circ \sigma_v^{-1})_v$ has product $(\prod_i s_i)^{\#\{v\}} = 1$ (`New.Space.prod_prod_comp_symm_eq_one`). So [the matching](/decl/New.Space.exists_perm_signedClasses/) applies to it and to the family $1$.

### The class integral

**Theorem.** Let $N \geq 1$, $B \geq 13 N^3$, and let $E$ contain a primitive $5040$-th root of unity. Let $\varphi$ be a test function. Let $y$ be an elliptic isometry of type $1$ for the frame $u$, and let $z_v$ list the roots of $\chi_y$ at $v$, in the numbering of the source. Then there is $c \in \mathbb{C}$ with the following property. Let $V$ be a space of signs $s$, $l$ a family of parameters with $e_\lambda$ a cusp kernel of order $B$, $\sigma$ a family of permutations, and $x$ a frame such that $(y, x)$ has type $(s \circ \sigma_v^{-1})_v$ and $u^{-1} a u = x^{-1} a x$ for every rational $a$ that commutes with $y$. Then
$$ J_{\chi_y, [x, y]}(e_\lambda \otimes \varphi) = \Big( \prod_v \int_{G_v} e_{l_v}\big(h^{-1} \operatorname{diag}_s(z_v \circ \sigma_v)\, h\big)\, dh \Big) \cdot c. $$
Lean: `New.Space.exists_classIntegral_eq` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* There is a space $W$ of signs $s$ with finite frame $x$ in which $y$ is an isometry with real components $\operatorname{diag}_s(z_v \circ \sigma_v)$ (`New.Space.exists_ratEmbed_eq_diagTorus`). By Landherr's theorem, as used in [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/), $W$ and $V$ are rationally isometric, and the class integral of $V$ is an orbital integral of $W$ (`New.Space.exists_x_eq_and_ratEmbed_conj_eq`). [Split](/decl/New.Space.orbitalIntegral_eq_prod_mul/) the orbital integral. The finite factor uses a cutoff for the image in $G_f$ of the centraliser of $y$. This image is the same for all frames $x$ that conjugate the centraliser as $u$ does. So the finite factor is one number $c$, defined from $u$ and $y$ alone. $\square$

### Harish-Chandra's formula

The classical form is the following. Let $G = U(p, q)$ with $p + q = N$, let $\pi$ be a discrete series representation with Harish-Chandra parameter $\lambda$, and let $T$ be the compact diagonal torus. Then the elliptic orbital integrals of a suitably normalised coefficient of $\pi$ are given by the character of the finite-dimensional representation of the compact form with the same infinitesimal character, up to a sign $(-1)^{q(G)}$ and a sum over the Weyl group. For the character of the discrete series on the compact Cartan subgroup the source cites Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966), Theorem 16, with part I, Acta Math. 113 (1965), Theorem 3, and Knapp, *Representation theory of semisimple groups* (1986), Theorem 12.7. These citations are not marked as compared in the source.

The source proves the following form for its kernels.

**Theorem (Harish-Chandra's formulas, stable form).** Let $N \geq 1$, let $\varepsilon : n \to \{\pm 1\}$ be signs, and let $l$ be a doubled Harish-Chandra parameter for $\varepsilon$ with the gap condition with constant $10 N^5$. Then:

1. the formal degree of the discrete series of parameter $l$ equals the Weyl dimension polynomial at $l$;
2. for every $x : n \to \mathbb{C}^1$ that is injective,
$$ (-1)^{p q} \sum_{\sigma \in S_n} \int_{U(\operatorname{diag} \varepsilon)} e_l\big(g^{-1} \operatorname{diag}_\varepsilon(x \circ \sigma)\, g\big)\, dg = \#\{\sigma : \varepsilon \circ \sigma = \varepsilon\} \cdot \overline{\chi_l(\operatorname{diag}_K(x))}, $$
where $p q$ is the number of pairs $(a, b)$ with $\varepsilon_a = 1$ and $\varepsilon_b = -1$.

Lean: `New.Orbital.harish_chandra_degree_and_orbital` (Lib/DiscreteSeries/Character/FormalDegree.lean).

**Remark (Formalization).** The Lean form is a special case of the classical result: the group is $U(p, q)$, the parameter has a large gap, and the function is the kernel $e_l$, the formal degree times the conjugate of one matrix coefficient. The sum over all of $S_n$ is the stable form. The number $\#\{\sigma : \varepsilon \circ \sigma = \varepsilon\} = p!\, q!$ is the order of the Weyl group of $K = U(p) \times U(q)$. The proof is in [the discrete series](/chapter/discrete-series/).

**Lemma.** Let the number of infinite places of $E$ be even. Let $l$ be a family of parameters for $s$, each with the gap condition with constant $10 N^5$, and let $z_v : n \to \mathbb{C}^1$ be injective. Then
$$ \sum_{\sigma} \prod_v \int_{G_v} e_{l_v}\big(h^{-1} \operatorname{diag}_s(z_v \circ \sigma_v)\, h\big)\, dh = \Big( \prod_v \#\{\tau : s \circ \tau = s\} \Big) \prod_v \overline{\chi_{l_v}(\operatorname{diag}_K(z_v))}, $$
the sum over all families $\sigma = (\sigma_v)$ of permutations.
Lean: `New.Space.sum_prod_integral_dsKernel` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* The sum of products is the product of the sums over each $\sigma_v$. Apply [Harish-Chandra's formula](/decl/New.Orbital.harish_chandra_degree_and_orbital/) at each place. The signs give $((-1)^{pq})^{\#\{v\}} = 1$, since the number of places is even. $\square$

The right side does not depend on $s$ except through the counting factor.

### The elliptic terms

A class with $J_{R,c} \neq 0$ is the class of an elliptic $\gamma$ of $V$. It lies in $\mathcal{C}(R, (s \circ \sigma_v^{-1})_v)$ for exactly $\prod_v \#\{\tau : s \circ \tau = s\}$ families $\sigma$ (`New.Space.card_mem_signedClasses`). At each place the signs of $V$ on the eigenlines of $\gamma_v$ are a rearrangement of $s$, and the $\sigma_v$ that give this rearrangement form a coset of the stabiliser of $s$.

**Theorem (Elliptic terms).** Let $N \geq 1$ and $B \geq 13 N^3$. Let $E$ contain a primitive $5040$-th root of unity and have an even number of infinite places. Let $\varphi$ be a test function, let $R$ be irreducible, and let $z_v : n \to \mathbb{C}^1$ list the roots of $R$ at each infinite place $v$, in the numbering of the source. Then there is $c \in \mathbb{C}$ such that, for every space $V$ of signs $s$ and every family $l$ of parameters for $s$ with the gap condition with constant $10 N^5$ and with $e_\lambda$ a cusp kernel of order $B$,
$$ I_R(\varphi) = c \cdot \prod_v \overline{\chi_{l_v}(\operatorname{diag}_K(z_v))}. $$
Lean: `New.Space.exists_geometricSide_singleton_eq` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* Let $M = \prod_v \#\{\tau : s \circ \tau = s\} \neq 0$. By [the summation theorem](/decl/New.Space.hasSum_classIntegral/) and the count above,
$$ M \cdot I_R(\varphi) = \sum_\sigma \sum_{a \in \mathcal{C}(R, (s \circ \sigma_v^{-1})_v)} J_{R, a}. $$
For each $\sigma$, [the matching](/decl/New.Space.exists_perm_signedClasses/) carries the classes of signs $1$ onto those of signs $(s \circ \sigma_v^{-1})_v$, and [the class integral theorem](/decl/New.Space.exists_classIntegral_eq/) gives $J_{R, f(a)} = (\prod_v \int e_{l_v}(\cdots))\, C_a$, with $C_a$ independent of $V$, $s$, $l$ and $\sigma$. Put $c = \sum_a C_a$, the sum over the classes of signs $1$. Then the inner sum is $(\prod_v \int e_{l_v}(\cdots)) \cdot c$ (`New.Space.exists_tsum_signedClasses_eq`). Sum over $\sigma$ with [the lemma](/decl/New.Space.sum_prod_integral_dsKernel/). This gives $M \cdot I_R(\varphi) = M \cdot c \prod_v \overline{\chi_{l_v}(\operatorname{diag}_K(z_v))}$. Cancel $M$. $\square$

**Remark (Formalization).** The numbers $C_a$ are `choose`n, one for each class $a$ of signs $1$, together with a representative $(u_a, y_a)$. The number $c$ is the sum $\sum_a C_a$ in the sense of `tsum`, which is $0$ if the family is not summable. The proof uses only that `tsum` is unchanged by a bijection of the index set and commutes with multiplication by a constant. Both facts hold in $\mathbb{C}$ with or without summability. So the theorem holds as stated in all cases, but the value of $c$ has a meaning as a sum of finite orbital integrals only when the family is summable. The roots $z_v$ come from a numbering (`New.Variety.numberedRoots`); $c$ depends on it, but the product of characters does not, as a character is a class function.

### The comparison

**Theorem (Comparison of traces).** Let $E$ contain a primitive $5040$-th root of unity and have an even number of infinite places. Let $N \geq 2$, and let $V$ and $V'$ be spaces of signs $s$ and $s'$. Let $l$ be a family of doubled parameters with the gap condition with constant $10 N^5$ for $s$ and for $s'$. Let $K$ be a level and $a \in \mathbb{C}[G_f]$. Let $w$ be a split finite place and $w'$ a finite place. Suppose that $a \star 1_K$ is cuspidal at $w$, and that $(a \star 1_K)(g) \neq 0$ implies that $g_{w'}$ has a simple zero. Let $T$ and $T'$ be operators that act as $a$ on the forms of type $e_\lambda$ and level $K$ for $V$ and for $V'$. Then $\operatorname{tr} T = \operatorname{tr} T'$.
Lean: `New.trace_comparison` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* Put $B = 10 N^5$. Since $N \geq 2$, $13 N^3 \leq 10 N^5$. So $e_\lambda$ is a cusp kernel of order $B$ for both sign families, with $B \geq 13 N^3$. Write $\varphi = a \star 1_K$. For each $R$, $I_R^V(\varphi) = I_R^{V'}(\varphi)$:

1. if $R$ is not irreducible, both are $0$ by [the theorem of Section 4](/decl/New.Space.geometricSide_singleton_eq_zero/);
2. if $R$ is irreducible with a root off the unit circle, both are $0$ by [the corollary of Section 5](/decl/New.Space.geometricSide_singleton_eq_zero_of_norm_ne_one/);
3. otherwise both are $c \prod_v \overline{\chi_{l_v}(\operatorname{diag}_K(z_v))}$ with the same $c$, by [the elliptic terms theorem](/decl/New.Space.exists_geometricSide_singleton_eq/).

By [the trace identity](/decl/New.Space.volume_mul_trace_eq/) and [the sum over $R$](/decl/New.Space.hasSum_geometricSide/), $\operatorname{vol}(K) \operatorname{tr} T = \sum_R I_R^V(\varphi) = \sum_R I_R^{V'}(\varphi) = \operatorname{vol}(K) \operatorname{tr} T'$. Since $\operatorname{vol}(K) > 0$ (`New.measureReal_pos_of_isLevel`), $\operatorname{tr} T = \operatorname{tr} T'$. $\square$

In case 3 the character $\chi_{l_v}$ belongs to $l_v$ read for the definite signs, so it is the same for $V$ and $V'$.

**Remark (Formalization).** The hypothesis $N \geq 2$ is used only to get $13 N^3 \leq 10 N^5$. The hypothesis that the number of infinite places is even is implied by the $5040$-th roots of unity: $E$ then contains $\mathbb{Q}(\zeta_{5040})$, of degree $\varphi(5040) = 1152$, so $[E : \mathbb{Q}]$ is divisible by $1152$, and the number of infinite places $[E : \mathbb{Q}]/2$ is divisible by $576$. This is finding F-140, and it is an exercise at the end of the chapter. The theorem asks for no condition on $a$ beyond cuspidality and the simple zero. [The main theorem of the chapter](/decl/New.trace_eq_of_isCuspidalAt/) removes the simple zero by the line stabiliser of Section 7.
