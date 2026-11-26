---
title: Discrete series of unitary groups
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Discrete series of unitary groups

This section gives the classical theory that the chapter replaces by one explicit function. It states the facts on the discrete series of $U(p,q)$ that the source proves for its function $c_\lambda$: the parameters, the lowest $K$-type, the Casimir eigenvalue, Schur orthogonality, the formal degree, the character on the compact torus and the holomorphic case. It ends with the model case $U(1,1)$, which later sections use as a check. Nothing in this section is formalized in the source. The statements are classical, and the citations are at the end of each paragraph and in [the notes](/chapter/discrete-series/#notes-and-references).

### Square integrable representations

Let $G$ be a unimodular locally compact group with a Haar measure $dg$. An irreducible unitary representation $(\pi, H)$ of $G$ is *square integrable* if one matrix coefficient $g \mapsto \langle \pi(g)u, v\rangle$ with $u, v \ne 0$ is in $L^2(G)$. Then all matrix coefficients are in $L^2(G)$, and there is a number $d_\pi > 0$, the *formal degree*, with

$$\int_G \langle \pi(g)u, v\rangle\,\overline{\langle \pi(g)u', v'\rangle}\,dg = d_\pi^{-1}\,\langle u, u'\rangle\,\overline{\langle v, v'\rangle}$$

for all $u, v, u', v' \in H$. These are the Schur orthogonality relations. For a compact group with total mass $1$ the formal degree is the dimension. The formal degree depends on the Haar measure: if $dg$ is multiplied by $c$, then $d_\pi$ is divided by $c$. The square integrable representations are the irreducible subrepresentations of $L^2(G)$. Together they form the *discrete series* of $G$. (Knapp, *Representation Theory of Semisimple Groups*, Chapter IX.)

Two consequences of the relations are used in this chapter. Let $v$ be a unit vector and $c(g) = \langle \pi(g)v, v\rangle$. First, $c(1) = 1$ and $c(g^{-1}) = \overline{c(g)}$. Second, the function $e = d_\pi \overline{c}$ satisfies $e * e = e$ for convolution, and more generally

$$d_\pi \int_G c(xya)\,\overline{c(y)}\,dy = c(x)\,c(a).$$

To see this, write $c(xya) = \langle \pi(y)\pi(a)v, \pi(x)^{-1}v\rangle$ and apply the relations with $u = \pi(a)v$, $v' = v$, $u' = v$. The source proves exactly this identity for its function $c_\lambda$ ([Theorem](/decl/New.dsCoeff_schur_orthogonality/)).

### The group and its compact torus

From now on $G = U(p,q)$. Fix signs $\varepsilon_1, \dots, \varepsilon_n \in \{\pm 1\}$, with $p$ signs $+1$ and $q$ signs $-1$, and let $J = \operatorname{diag}(\varepsilon_1, \dots, \varepsilon_n)$. Then $G = \{g \in GL_n(\mathbb C) : g^* J g = J\}$. The subgroup $K = G \cap U(n)$ is the group of block diagonal unitary matrices, so $K \cong U(p) \times U(q)$. It is a maximal compact subgroup. The diagonal unitary matrices form a maximal torus $T$ of $K$, and $T$ is also a Cartan subgroup of $G$. So $G$ and $K$ have equal rank. By Harish-Chandra's theorem, this is the condition for $G$ to have a discrete series.

The roots of $T$ in the complexified Lie algebra $\mathfrak{gl}_n(\mathbb C)$ are $e_i - e_j$ for $i \ne j$. The root $e_i - e_j$ is *compact* if $\varepsilon_i = \varepsilon_j$ and *noncompact* if $\varepsilon_i \ne \varepsilon_j$. The Weyl group of $G$ for $T$ is the symmetric group $S_n$. The Weyl group of $K$ is the subgroup $W_K = S_p \times S_q$ of the permutations that preserve the signs.

### The parameters

A *Harish-Chandra parameter* for $U(p,q)$ is a vector $\lambda = (\lambda_1, \dots, \lambda_n)$ with all $\lambda_i$ in $\frac{n-1}{2} + \mathbb Z$ and with distinct entries. The second condition says that $\lambda$ is regular. The first says that $\lambda - \rho$ is a weight of $T$, where $\rho$ is half the sum of the positive roots: for any order of the indices, the entries of $\rho$ are $\frac{n-1}{2}, \frac{n-3}{2}, \dots, -\frac{n-1}{2}$.

Fix $\lambda$. The roots $e_i - e_j$ with $\lambda_i > \lambda_j$ form a positive system. Let $\rho$, $\rho_c$ and $\rho_n$ be half the sums of the positive roots, of the positive compact roots and of the positive noncompact roots. So $\rho = \rho_c + \rho_n$.

**Theorem (Harish-Chandra).** For each Harish-Chandra parameter $\lambda$ there is a discrete series representation $\pi_\lambda$ of $U(p,q)$. Every discrete series representation is some $\pi_\lambda$. Two of them, $\pi_\lambda$ and $\pi_\mu$, are equivalent if and only if $\mu = w\lambda$ for some $w \in W_K$. The Casimir operator $\Omega = \sum_{a,b} E_{ab}E_{ba}$ of $\mathfrak{gl}_n$ acts on $\pi_\lambda$ by the scalar $|\lambda|^2 - |\rho|^2$.

So the discrete series with a given infinitesimal character $\lambda$ are counted by $W / W_K$, a set with $\binom{n}{p}$ elements. Each of them corresponds to a choice of which entries of $\lambda$ have sign $+1$. (Harish-Chandra, *Discrete series for semisimple Lie groups II*, Acta Math. 116 (1966); Knapp, Chapters IX and XII.)

### The lowest $K$-type

The representation $\pi_\lambda$ restricted to $K$ is a direct sum of irreducible representations of $K$, each with finite multiplicity. Irreducible representations of $K$ are labelled by their highest weights, for the positive compact roots.

**Theorem (Schmid; Hecht and Schmid).** Let $\Lambda = \lambda + \rho_n - \rho_c$. The representation of $K$ with highest weight $\Lambda$ occurs in $\pi_\lambda$ with multiplicity one. Every $K$-type of $\pi_\lambda$ has a highest weight of the form $\Lambda + \beta$, where $\beta$ is a sum of positive noncompact roots.

The weight $\Lambda$ is the *lowest $K$-type*, also called the Blattner parameter. Blattner's formula gives the multiplicities of all $K$-types; it was proved by Hecht and Schmid. (W. Schmid, *Some properties of square-integrable representations of semisimple Lie groups*, Ann. of Math. 102 (1975) 535-564; H. Hecht and W. Schmid, *A proof of Blattner's conjecture*, Invent. Math. 31 (1975) 129-154.)

Let $v$ be a unit highest weight vector in the lowest $K$-type. Its matrix coefficient $c_\lambda(g) = \langle \pi_\lambda(g)v, v\rangle$ is the function of this chapter. It has three properties that come from the theorems above. On $K$ it is a coefficient of the representation of $K$ with highest weight $\Lambda$. It is an eigenfunction of $\Omega$ with eigenvalue $|\lambda|^2 - |\rho|^2$. By Schur orthogonality and the multiplicity one, its projection to the lowest $K$-type is a product $c_\lambda(x)c_\lambda(b)$ times a constant (see the proof of [Theorem](/decl/New.integral_conj_weightMinors_lowestKType_mul_dsCoeff/)).

### The formal degree and the character

The Lie algebra of $G$ is $\mathfrak k \oplus \mathfrak p$, with $\mathfrak p$ the hermitian matrices in it. The compact dual of $G$ is $U(n)$, with Lie algebra $\mathfrak k \oplus i\mathfrak p$. A Haar measure on $G$ and a Haar measure on $U(n)$ are *compatible* if they come from the same Lebesgue measure on $\mathfrak k \oplus \mathfrak p \cong \mathfrak k \oplus i\mathfrak p$. Give $U(n)$ the mass $1$, and give $G$ the compatible measure.

**Theorem (Harish-Chandra's formula for the formal degree).** For this measure the formal degree of $\pi_\lambda$ is

$$d_\lambda = \prod_{\lambda_j < \lambda_i} (\lambda_i - \lambda_j) \Big/ \prod_{k=0}^{n-1} k!.$$

The right side is Weyl's formula for the dimension of the representation of $U(n)$ with highest weight $\lambda - \rho$, since $\prod_{i<j}(j - i) = \prod_{k=0}^{n-1} k!$. So with compatible measures the formal degree of $\pi_\lambda$ is the dimension of a representation of the compact dual. (Harish-Chandra, Acta Math. 116 (1966); the source cites Theorem 16 there, with Theorem 3 of part I, Acta Math. 113 (1965), and Knapp, Theorem 12.7.)

The global character $\Theta_\lambda$ of $\pi_\lambda$ is a locally integrable function on $G$. On the regular elements of the compact torus it is given by a formula like Weyl's.

**Theorem (Harish-Chandra's character formula).** For $t = \operatorname{diag}(t_1, \dots, t_n)$ in $T$ with distinct entries,

$$\Theta_\lambda(t) = (-1)^{pq}\,\frac{\sum_{w \in W_K} \operatorname{sgn}(w)\, t^{w\lambda}}{t^{\rho}\prod_{\lambda_i > \lambda_j}(1 - t_j/t_i)}.$$

Here $t^\mu = \prod t_i^{\mu_i}$, and the expression is a well defined function of $t$ although $\lambda$ and $\rho$ may have half integral entries. The sign is $(-1)^{\dim(G/K)/2}$, and $\dim G/K = 2pq$. If the sum ran over all of $S_n$, the right side would be $(-1)^{pq}$ times Weyl's character of $U(n)$ with highest weight $\lambda - \rho$. The source proves a form of this formula through orbital integrals: the orbital integrals of $\overline{c_\lambda}$ summed over all $\sigma \in S_n$ give the conjugate of Weyl's character ([Theorem](/decl/New.Orbital.harish_chandra_degree_and_orbital/)).

### The holomorphic discrete series

Say that $\lambda$ is in the *holomorphic chamber* if $\lambda_i < \lambda_j$ whenever $\varepsilon_i = +1$ and $\varepsilon_j = -1$. Then every positive noncompact root is $e_j - e_i$ with $\varepsilon_j = -1$ and $\varepsilon_i = +1$. These roots span an abelian subalgebra $\mathfrak p^+$ of $\mathfrak p_{\mathbb C}$, and $G/K$ is the bounded domain $\{Z \in M_{p \times q}(\mathbb C) : 1 - Z^*Z > 0\}$. For $\lambda$ in this chamber, $\pi_\lambda$ is a *holomorphic discrete series*. It acts on a Hilbert space of holomorphic functions on the domain with values in the lowest $K$-type. The lowest $K$-type is killed by one of the two abelian subalgebras $\mathfrak p^{\pm}$, and it generates the representation under the other. The lowest $K$-type $\Lambda$ is then the weight of the representation, in the sense of modular forms. (Harish-Chandra, *Representations of semisimple Lie groups IV, V, VI*, Amer. J. Math. 77 (1955) and 78 (1956); Knapp, Chapter VI.)

For holomorphic discrete series the coefficient of a highest vector is explicit. It is a product of powers of leading principal minors of $g$, in an order that puts the signs $+1$ first. Section 6 gives the source's form ([Theorem](/decl/New.dsCoeff_eq_holMinors/)).

### The model case $U(1,1)$

Let $n = 2$, $\varepsilon = (1, -1)$. Then $G = U(1,1)$ and $K = U(1) \times U(1)$. Every $g \in G$ can be written $g = k a_t k'$ with $k, k' \in K$, $t \ge 0$ and

$$a_t = \begin{pmatrix} \cosh t & \sinh t \\ \sinh t & \cosh t \end{pmatrix}.$$

So $|g_{11}| = \cosh t \ge 1$, and the operator norm is $\|g\| = e^t$.

Let $w_1, w_2$ be integers and $k = w_2 - w_1 \ge 2$. Take the subgroup $SU(1,1)$ first, with elements $g = \begin{pmatrix} a & b \\ \bar b & \bar a\end{pmatrix}$, $|a|^2 - |b|^2 = 1$. It acts on the unit disc $D$ by $g \cdot z = (az + b)/(\bar b z + \bar a)$. Let $H_k$ be the space of holomorphic $f$ on $D$ with

$$\|f\|^2 = \frac{k-1}{\pi}\int_D |f(z)|^2 (1 - |z|^2)^{k-2}\,dA(z) < \infty,$$

and let $(\pi_k(g)f)(z) = (a - \bar b z)^{-k} f(g^{-1} \cdot z)$. This is the holomorphic discrete series of weight $k$. The constant $1$ is a unit vector, since $\int_D (1 - |z|^2)^{k-2}\,dA = \pi/(k-1)$. Its coefficient is

$$\langle \pi_k(g)1, 1\rangle = \frac{k-1}{\pi}\int_D (a - \bar b z)^{-k} (1 - |z|^2)^{k-2}\,dA(z) = a^{-k},$$

by the mean value property of the holomorphic function $z \mapsto (a - \bar b z)^{-k}$ on circles about $0$. So the coefficient is $g_{11}^{-k}$. On $U(1,1)$ the representation extends by a character of the centre. With the central character $\det^{w_2}$ the coefficient becomes

$$c(g) = g_{11}^{-k}\,(\det g)^{w_2}, \qquad |c(g)| = |g_{11}|^{-k} = (\cosh t)^{-k}.$$

In the notation above, $\lambda = (w_1 + \frac12, w_2 - \frac12)$. This is a Harish-Chandra parameter, since $n - 1 = 1$ and the entries are distinct. It lies in the holomorphic chamber, since $\lambda_1 < \lambda_2$. The only positive root is $e_2 - e_1$, and it is noncompact. So $\rho = \rho_n = (-\frac12, \frac12)$, $\rho_c = 0$, and $\Lambda = \lambda + \rho_n = (w_1, w_2)$. The Casimir eigenvalue is $|\lambda|^2 - |\rho|^2 = w_1^2 + w_1 + w_2^2 - w_2$.

The formal degree needs the measure. In the coordinates $g = k a_t k'$, the Haar measure is a constant times $\sinh 2t\,dt\,dk\,dk'$, with $dk$, $dk'$ of mass $1$. The compact dual $U(2)$ has the polar coordinates $g = k \exp(iX_t) k'$, where $X_t$ is the hermitian matrix with $0$ on the diagonal and $t$ off the diagonal, and $|g_{11}| = \cos t$. The polar formulas for $G$ and for its compact dual have the same constant, with $\sinh 2t$ for $G$ and $\sin 2t$ for $U(2)$, $t \in [0, \pi/2]$. Since $\int_0^{\pi/2}\sin 2t\,dt = 1$, the compatible normalisation is the constant $1$. (Exercise 5 checks this against the uniform distribution of $|g_{11}|^2$ on $U(2)$.) With $u = \cosh^2 t$, so $du = \sinh 2t\,dt$,

$$\int_G |c(g)|^2\,dg = \int_1^\infty u^{-k}\,du = \frac{1}{k-1}.$$

So $d_\lambda = k - 1$. This agrees with Harish-Chandra's formula: $\lambda_2 - \lambda_1 = k - 1$, and $\prod_{k'=0}^{1} k'! = 1$. For $k = 1$ the integral diverges, and $\pi_1$ is not in the discrete series. Its parameter $\lambda = (w_1 + \frac12, w_1 + \frac12)$ is singular.

The decay in this example shows the role of the gap. The parameter has $|\lambda_1 - \lambda_2| = k - 1$, and $|c(g)| = (\cosh t)^{-k} \le 2^k e^{-kt} = (2/\|g\|)^k$. So a larger gap between the entries of opposite sign gives a faster decay. The source proves the same bound in general, with the exponent bounded by the gap ([Theorem](/decl/New.DiscreteSeries.norm_dsCoeff_le_pow/)).
