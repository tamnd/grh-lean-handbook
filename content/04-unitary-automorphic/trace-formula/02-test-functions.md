---
title: Test functions and cuspidality
lean:
  - Lib/Adelic/TraceFormula/TestFunction.lean
  - Lib/Adelic/TraceFormula/CuspidalType.lean
decls:
  - New.TestFunction
  - New.convIndicator
  - New.IsCuspidalAt
  - New.IsCuspidalAt.exists_sum_translate_eq_zero
  - New.IsCuspidalAt.convIndicator_mul
  - New.HasSimpleZero
  - New.HasSimpleZero.charpoly_ne_pow
  - New.isCuspidalAt_convIndicator_tupleIdem
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Test functions and cuspidality

The trace formula of this chapter uses test functions of the form $e \otimes \varphi$ on $G = G_\infty \times G_f$. The real factor $e$ is a cusp kernel. The finite factor $\varphi$ is a locally constant function of compact support on $G_f$. This section defines the finite factors and the two local conditions that the proof puts on them: cuspidality at one split place, and a simple zero at a second place. It ends with a model case for $\mathrm{GL}_2$ and with the source of cuspidal test functions in the argument.

### Test functions

Let $H$ be a topological group. In this chapter $H$ is $G_f$, $\mathrm{GL}_N(E_w)$ or a product of such groups.

**Definition (Test function).** A *test function* on $H$ is a function $f : H \to \mathbb{C}$ that is locally constant and has compact support. The test functions form a complex vector space. The group $H \times H$ acts on it by $(a, b) \cdot f = \big(x \mapsto f(a^{-1} x b)\big)$.
Lean: `New.TestFunction` (Lib/Adelic/TraceFormula/TestFunction.lean).

The action is `New.TestFunction.translate`. Conjugation by $g$ is the action of $(g, g)$: it sends $f$ to $x \mapsto f(g^{-1} x g)$.

Hecke operators of a level $K$ come from the group algebra $\mathbb{C}[G_f]$ of finite formal combinations of points of $G_f$. Each such combination gives a test function.

**Definition.** Let $K$ be a compact open subgroup of $G_f$ and let $a = \sum_b a(b)\, b$ be an element of $\mathbb{C}[G_f]$. The test function $a \star 1_K$ is
$$ (a \star 1_K)(x) = \sum_{b} a(b)\, 1_K(b^{-1} x) = \sum_b a(b)\, 1_{bK}(x). $$
Lean: `New.convIndicator` (Lib/Adelic/TraceFormula/TestFunction.lean).

The map $a \mapsto a \star 1_K$ is linear. For $c \in \mathbb{C}$ and $b \in G_f$ the product $(c\, b) \cdot a$ gives $c$ times the left translate of $a \star 1_K$ by $b$, that is $x \mapsto c\, (a \star 1_K)(b^{-1} x)$ (`New.convIndicator_single_mul`). No factor $\operatorname{vol}(K)^{-1}$ appears. So the factor $\operatorname{vol}(K)$ appears in the trace formula of Section 3.

### Cuspidality at a split place

Let $w$ be a finite place of $E$ that splits over $F$, with conjugate $\bar w \neq w$. Then the part of $G_f$ at the pair $\{w, \bar w\}$ is a copy of $\mathrm{GL}_N(E_w)$. The embedding $\iota_w : \mathrm{GL}_N(E_w) \to G_f$ puts $g$ at $w$, the inverse conjugate transpose of $g$ at $\bar w$, and $1$ at the other places (`New.ofSplitPlace`). Let $\mathcal{O}_w$ be the ring of integers of $E_w$, let $k_w$ be its residue field, with $q$ elements, and let $\mathrm{red} : \mathrm{GL}_N(\mathcal{O}_w) \to \mathrm{GL}_N(k_w)$ be the reduction.

For a set $T$ of indices, let $\varepsilon_T$ be the diagonal projector on the coordinates in $T$. For a matrix $Z$ over a ring, put $r_T(Z) = 1 + \varepsilon_T Z (1 - \varepsilon_T)$. If $T$ is neither empty nor all of $n$, the matrices $r_T(Z)$ over $k_w$ make up the unipotent radical $U_T$ of the proper parabolic subgroup $P_T$ that keeps the span of the basis vectors $e_i$, $i \in T$. As $Z$ runs over all $N \times N$ matrices over $k_w$, each element of $U_T$ is met $q^{N^2 - |T|(N - |T|)}$ times.

**Definition (Cuspidal at $w$).** A test function $\varphi$ on $G_f$ is *cuspidal at the split place $w$* if the following holds. Let $T$ be a set of indices with $T \neq \emptyset$ and $T \neq n$, let $t \in \mathrm{GL}_N(k_w)$, and let $\ell$ assign to each matrix $Z$ over $k_w$ an element $\ell(Z) \in \mathrm{GL}_N(\mathcal{O}_w)$ with $\mathrm{red}(\ell(Z)) = r_T(Z)\, t$. Then for every $g \in G_f$,
$$ \sum_{Z \in M_N(k_w)} \varphi\big(g\, \iota_w(\ell(Z))\big) = 0. $$
Lean: `New.IsCuspidalAt` (Lib/Adelic/TraceFormula/TestFunction.lean).

In words: the right translates of $\varphi$ by lifts of the coset $U_T t$ have sum zero, for every proper coordinate parabolic, every coset and every choice of lifts. The sum runs over all matrices $Z$, not over the elements of $U_T$. Each element of the coset is met equally often, so the condition is the same as a zero sum over the coset itself.

**Remark (Formalization).** The definition quantifies over every choice of lifts $\ell$. If $\varphi$ is right invariant under the kernel of the reduction at $w$, which holds when $K$ contains this kernel and $\varphi = a \star 1_K$, the sum does not depend on the lifts. In general it can, and the definition then asks for more than one choice. The proofs below need only one family of lifts, which they get by `choose`, so the stronger definition does no harm. The sum is a `finsum` over the finite set $M_N(k_w)$.

The proof in Section 4 uses cuspidality in the following form, with one fixed family of lifts in $\mathrm{GL}_N(E_w)$ and right translation by all of $\mathrm{GL}_N(\mathcal{O}_w)$.

**Lemma.** Let $\varphi$ be cuspidal at the split place $w$, and let $T$ be a set of indices that is neither empty nor all of $n$. Then there are a finite nonempty index set $I$ and matrices $\kappa_i$ over $E_w$, $i \in I$, such that for every $k \in \mathrm{GL}_N(\mathcal{O}_w)$,
$$ \sum_{i \in I} (1, \iota_w(r_T(\kappa_i)\, k)) \cdot \varphi = 0, $$
that is, $\sum_i \varphi(x\, \iota_w(r_T(\kappa_i) k)) = 0$ for all $x \in G_f$.
Lean: `New.IsCuspidalAt.exists_sum_translate_eq_zero` (Lib/Adelic/TraceFormula/TestFunction.lean).

*Proof.* Take $I = M_N(k_w)$. For each $Z \in M_N(k_w)$ choose a matrix $\kappa_Z$ over $E_w$ such that $r_T(\kappa_Z)$ lies in $\mathrm{GL}_N(\mathcal{O}_w)$ and reduces to $r_T(Z)$. Such a matrix exists: lift $Z$ entrywise to $\mathcal{O}_w$ (`New.exists_radicalHom_reduceGL_eq`). Fix $k$. The lifts $\ell(Z) = r_T(\kappa_Z) k$ satisfy $\mathrm{red}(\ell(Z)) = r_T(Z)\, \mathrm{red}(k)$. Apply the definition with $t = \mathrm{red}(k)$. $\square$

Cuspidality is a condition on the right. So it survives products on the left in the group algebra.

**Lemma.** Let $K$ be a compact open subgroup of $G_f$ and let $a, b \in \mathbb{C}[G_f]$. If $a \star 1_K$ is cuspidal at the split place $w$, then so is $(b a) \star 1_K$.
Lean: `New.IsCuspidalAt.convIndicator_mul` (Lib/Adelic/TraceFormula/TestFunction.lean).

*Proof.* By linearity in $b$ it suffices to take $b = c\, y$ for one point $y$. Then $(b a) \star 1_K (x) = c\, (a \star 1_K)(y^{-1} x)$, and the sum in the definition at $g$ is $c$ times the sum for $a \star 1_K$ at $y^{-1} g$. $\square$

### The simple zero

The second local condition is a condition on characteristic polynomials at a place $w'$. Let $\mathrm{red}(c)$ denote the residue of an element $c$ of $\mathcal{O}_{w'}$.

**Definition (Simple zero).** An element $g \in \mathrm{GL}_N(E_{w'})$ *has a simple zero* if all its entries lie in $\mathcal{O}_{w'}$ and $0$ is a root of multiplicity exactly one of the characteristic polynomial of the reduced matrix $\mathrm{red}(g)$ over $k_{w'}$.
Lean: `New.HasSimpleZero` (Lib/Adelic/TraceFormula/TestFunction.lean).

**Remark (Formalization).** The reduction of a matrix is taken entrywise with `residueOrZero`, which sends an element of $E_{w'}$ that is not integral to $0$. The first condition of the definition makes all entries integral, so this junk value never enters.

The use of the condition is the following lemma. It excludes the characteristic polynomials that are proper powers, which the argument of Section 4 cannot treat.

**Lemma.** If $g \in \mathrm{GL}_N(E_{w'})$ has a simple zero, then the characteristic polynomial of $g$ is not of the form $Q^j$ with $Q \in E_{w'}[X]$ and $j > 1$.
Lean: `New.HasSimpleZero.charpoly_ne_pow` (Lib/Adelic/TraceFormula/TestFunction.lean).

*Proof.* Let $M$ be $g$ as a matrix over $\mathcal{O}_{w'}$, and suppose $\chi_g = Q^j$. The polynomial $\chi_M$ is monic over the integrally closed domain $\mathcal{O}_{w'}$, and its image over the fraction field is $Q^j$. Then $Q$ divides a monic integral polynomial, so $Q$ is a constant times an integral polynomial $P_0$, and comparing leading coefficients gives $\chi_M = P^j$ for an integral $P$ (`New.exists_eq_pow_of_monic_of_map_eq_pow`). Reduce modulo $w'$. The multiplicity of $0$ as a root of $\chi_{\mathrm{red}(M)} = \mathrm{red}(P)^j$ is $j$ times the multiplicity of $0$ in $\mathrm{red}(P)$. It is $1$ by hypothesis. So $j = 1$, a contradiction. $\square$

**Example.** Let $\varpi$ be a uniformiser of $E_{w'}$ and put $t = \operatorname{diag}(\varpi, 1, \dots, 1)$. Its reduction is $\operatorname{diag}(0, 1, \dots, 1)$, with characteristic polynomial $X (X - 1)^{N-1}$. So $t$ has a simple zero. In contrast the scalar matrix $\varpi \cdot 1$ is integral, but its reduction is $0$, with characteristic polynomial $X^N$. Its own characteristic polynomial $(X - \varpi)^N$ is a proper power for $N \geq 2$. Section 7 uses elements of the first kind to force the simple zero.

### A model case

Take $N = 2$. The proper coordinate parabolics of $\mathrm{GL}_2$ are the upper and the lower triangular groups, for $T = \{1\}$ and $T = \{2\}$. For $T = \{1\}$ the matrix $r_T(Z)$ is $\begin{pmatrix} 1 & z_{12} \\ 0 & 1 \end{pmatrix}$, so each element of the radical is met $q^3$ times. Let $\varphi$ be right invariant under the kernel of reduction at $w$. Then cuspidality at $w$ says that for all $g \in G_f$ and $t \in \mathrm{GL}_2(k_w)$,
$$ \sum_{z \in k_w} \varphi\Big(g\, \iota_w\Big(\widetilde{\begin{pmatrix} 1 & z \\ 0 & 1 \end{pmatrix} t}\Big)\Big) = 0, $$
and the same with lower triangular matrices. Here the tilde is any lift. Suppose that $\varphi = \psi \otimes \varphi^w$, where $\varphi^w$ lives away from $w$ and $\psi$ is supported on $\mathrm{GL}_2(\mathcal{O}_w)$ and inflated from a function $\bar\psi$ on $\mathrm{GL}_2(k_w)$. Then the condition says that $\bar\psi$ has sum zero over every coset $N t$ of the upper and of the lower unipotent group. A matrix coefficient or the character of a cuspidal representation of $\mathrm{GL}_2(k_w)$ has this property. The reason is that a cuspidal representation $\pi$ has no nonzero vector fixed by the unipotent radical $U$ of a proper parabolic subgroup. So $\sum_{u \in U} \pi(u) = 0$, and the sum of $\operatorname{tr}\pi(u t)$ over $u \in U$ is zero.

### Cuspidal test functions in the argument

The argument gets its cuspidal test functions from Green's theory of the characters of $\mathrm{GL}_N(\mathbb{F}_q)$, which [finite general linear groups](/chapter/finite-gln/) explains. A *label* of degree $N$ over a finite field is a monic squarefree polynomial of degree $N$ with nonzero constant term. Green's class function of an irreducible label has mean zero on the unipotent radical of every proper coordinate parabolic. Its idempotent $\mathrm{labelIdem}(c)$ in the group algebra of $\mathrm{GL}_N$ over the residue field then has coefficient sums zero over each coset of such a radical. For a family of labels, one for each place of a family, $\mathrm{tupleIdem}(c)$ is the tensor product of these idempotents.

**Example.** Let $(w_i)_{i \in I}$ be a family of finite places of $E$ that are pairwise distinct, such that no conjugate $\bar w_i$ is a place $w_j$ of the family. Let $K$ be the kernel of the reduction of $K_0$ at all $w_i$, and let $\tilde u$ denote the lift to $G_f$, through a fixed section of the reduction, of an element $u$ of $\mathbb{C}[\prod_i \mathrm{GL}_N(k_{w_i})]$. Let $c = (c_i)$ be a family of polynomials over the residue fields whose member $c_x$ is an irreducible label of degree $N$. Then for every $b \in \mathbb{C}[G_f]$ the test function $(b\, \widetilde{\mathrm{tupleIdem}(c)}) \star 1_K$ is cuspidal at the split place $w_x$.
Lean: `New.isCuspidalAt_convIndicator_tupleIdem` (Lib/Adelic/TraceFormula/CuspidalType.lean).

The proof first removes $b$ by the lemma on products above. For the lifted idempotent it reduces the sum over a coset to the coefficient sum of $\mathrm{labelIdem}(c_x)$ over a coset of a radical, which is zero by Green's theory. The condition that no place of the family is conjugate to another makes each $w_i$ split, and it makes the components at different places independent.
