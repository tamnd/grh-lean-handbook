---
title: Classical automorphic forms
lean:
  - Lib/Adelic/AutomorphicForms/Basic.lean
  - Lib/Adelic/AutomorphicForms/Cuspidality.lean
  - Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean
  - Lib/Adelic/Hecke/Basic.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Classical automorphic forms

This section recalls the classical theory that the rest of the chapter follows. It starts with modular forms on the upper half plane, then gives the adelic definition of Borel and Jacquet, then cusp forms and the finite dimension theorem, then the special case of a group that is compact at infinity, and last the Hecke operators. Each statement has a Lean line that names the form of the statement in the source. The later sections state the source forms in full.

### Modular forms

Let $\mathfrak{H} = \{z \in \mathbb{C} : \operatorname{Im} z > 0\}$. The group $\mathrm{SL}_2(\mathbb{R})$ acts on $\mathfrak{H}$ by $\gamma z = (az + b)/(cz + d)$ for $\gamma = \begin{pmatrix} a & b \\ c & d \end{pmatrix}$. For an integer $k$ and a function $f$ on $\mathfrak{H}$, put $(f|_k \gamma)(z) = (cz + d)^{-k} f(\gamma z)$. For an integer $N \geq 1$, the group $\Gamma_0(N)$ is the group of $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ with $c \equiv 0 \pmod N$.

**Definition (Modular form).** A *modular form of weight $k$ and level $\Gamma_0(N)$* is a holomorphic function $f$ on $\mathfrak{H}$ with $f|_k \gamma = f$ for all $\gamma \in \Gamma_0(N)$, such that $f|_k \alpha$ is bounded on $\{\operatorname{Im} z > 1\}$ for every $\alpha \in \mathrm{SL}_2(\mathbb{Z})$. It is a *cusp form* if, in addition, the constant term $\int_0^h (f|_k \alpha)(x + iy)\, dx$ is $0$ for every $\alpha \in \mathrm{SL}_2(\mathbb{Z})$, where $h$ is the width of the cusp $\alpha \infty$. The spaces are $M_k(\Gamma_0(N))$ and $S_k(\Gamma_0(N))$.

Lean: the source works with unitary groups and has no form for $\mathrm{SL}_2$. Its adelic analogue is `New.Space.IsForm` (Lib/Adelic/AutomorphicForms/Basic.lean).

This is the definition of Diamond and Shurman, *A First Course in Modular Forms* (Springer GTM 228, 2005), Chapter 1, and of Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), Chapter 2. The three conditions are of three kinds. The first is analytic: $f$ is holomorphic, which means that $f$ is an eigenfunction of the Laplacian and is killed by the lowering operator. The second is arithmetic: $f$ is invariant under a discrete group. The third is a growth condition at the cusps. The adelic definition keeps the three kinds of condition and moves the arithmetic group into the finite adeles.

**Definition (Petersson product).** For $f, g \in S_k(\Gamma_0(N))$ the *Petersson product* is $\langle f, g \rangle = \int_{\Gamma_0(N) \backslash \mathfrak{H}} \overline{f(z)} g(z) y^k \, dx\, dy / y^2$.

Lean: the source's form is `New.Space.petersson` (Lib/Adelic/AutomorphicForms/Basic.lean).

The integral converges because a cusp form decays exponentially at each cusp. The Petersson product makes $S_k(\Gamma_0(N))$ a finite-dimensional Hilbert space. Here we use a convention: the product is conjugate linear in the first variable, as in the source, and not in the second, as in Diamond and Shurman.

### Adelic automorphic forms

Let $\mathbf{G}$ be a connected reductive group over a number field $F$, with adele ring $\mathbb{A}$, and let $K_\infty$ be a maximal compact subgroup of $\mathbf{G}(F \otimes \mathbb{R})$. Let $\mathfrak{z}$ be the center of the universal enveloping algebra of the complexified Lie algebra of $\mathbf{G}(F \otimes \mathbb{R})$.

**Definition (Automorphic form, Borel and Jacquet).** An *automorphic form* on $\mathbf{G}$ is a function $\varphi$ on $\mathbf{G}(\mathbb{A})$ such that:

1. $\varphi(\gamma g) = \varphi(g)$ for all $\gamma \in \mathbf{G}(F)$;
2. $\varphi$ is smooth: it is right invariant under an open compact subgroup $K_f$ of $\mathbf{G}(\mathbb{A}_f)$, and it is smooth in the archimedean variable;
3. $\varphi$ is right $K_\infty$-finite and $\mathfrak{z}$-finite;
4. $\varphi$ has moderate growth.

Lean: the source's form is `New.Space.IsAutomorphic` together with `New.Space.IsForm` (Lib/Adelic/AutomorphicForms/Basic.lean).

This is the definition of Borel and Jacquet, *Automorphic forms and automorphic representations*, in Proc. Sympos. Pure Math. 33, Part 1 (1979), §4. Condition 2 is the adelic form of the arithmetic group. Indeed, for $\mathbf{G} = \mathrm{SL}_2$ over $\mathbb{Q}$ and $K_f$ the group of $k \in \mathrm{SL}_2(\hat{\mathbb{Z}})$ with $k_{21} \equiv 0 \pmod N$, strong approximation gives $\mathbf{G}(\mathbb{A}) = \mathbf{G}(\mathbb{Q})\mathbf{G}(\mathbb{R})K_f$ and $\mathbf{G}(\mathbb{Q}) \cap \mathbf{G}(\mathbb{R})K_f = \Gamma_0(N)$. So a left $\mathbf{G}(\mathbb{Q})$-invariant and right $K_f$-invariant function on $\mathbf{G}(\mathbb{A})$ is a function on $\Gamma_0(N) \backslash \mathrm{SL}_2(\mathbb{R})$. A modular form $f$ of weight $k$ gives such a function by $\varphi_f(g) = (f|_k g_\infty)(i)$ at $g = \gamma g_\infty k_f$. Condition 3 holds since $\varphi_f(g\, r_\theta) = e^{-ik\theta}\varphi_f(g)$ for the rotations $r_\theta \in \mathrm{SO}_2(\mathbb{R})$, and since $\varphi_f$ is an eigenfunction of the Casimir operator.

The source replaces condition 3 by a stronger condition. It fixes a function $e$ on the archimedean group and asks that the right convolution by $e$ fixes $\varphi$. For the kernels that the source uses, $e$ is a matrix coefficient of a discrete series representation, multiplied by the formal degree. By the orthogonality relations for discrete series, convolution by $e$ is then a projection that is $0$ on every irreducible unitary representation except that one discrete series. So the source's forms of type $e$ are the automorphic forms that generate a given discrete series at the archimedean places, in a given $K_\infty$-type. Section 4 states this definition.

### Cusp forms and finite dimension

Let $\mathbf{P} = \mathbf{M}\mathbf{N}$ be a parabolic subgroup of $\mathbf{G}$ defined over $F$, with unipotent radical $\mathbf{N}$. The quotient $\mathbf{N}(F)\backslash\mathbf{N}(\mathbb{A})$ is compact.

**Definition (Cusp form).** An automorphic form $\varphi$ is a *cusp form* if, for every proper parabolic subgroup $\mathbf{P} = \mathbf{M}\mathbf{N}$ defined over $F$, the constant term $\varphi_{\mathbf{P}}(g) = \int_{\mathbf{N}(F)\backslash\mathbf{N}(\mathbb{A})} \varphi(ng)\, dn$ is $0$ for all $g$.

Lean: the source's form is `New.Space.IsCuspidal` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

For a unitary group the proper parabolic subgroups defined over $F$ are the stabilizers of the flags of nonzero isotropic subspaces. It is enough to take the maximal ones, the stabilizers of single nonzero isotropic subspaces $A$. Section 5 gives the source's form, which takes all nonzero isotropic $A$ at once.

**Theorem (Finite dimension, Harish-Chandra).** Fix an open compact subgroup $K_f$ of $\mathbf{G}(\mathbb{A}_f)$, a finite set of irreducible representations of $K_\infty$, and an ideal of finite codimension in $\mathfrak{z}$. Then the automorphic forms that are right $K_f$-invariant, whose right $K_\infty$-translates span a sum of the given representations, and that the ideal kills, form a finite-dimensional space.

Lean: the source proves a special case, `New.Space.finite_levelSpace` (Lib/Adelic/AutomorphicForms/Cuspidality.lean).

This is Harish-Chandra, *Automorphic Forms on Semisimple Lie Groups*, Lecture Notes in Math. 62 (1968), Theorem 1 There it is stated for a semisimple group and an arithmetic subgroup. The proof has two parts. The first part shows that a cusp form of the given type decays rapidly at the cusps. The second part uses the decay and the compactness of the set of points of bounded height (Mahler's criterion) to show that the unit ball of the space is compact. The source follows this pattern for its forms of type $e$. Section 5 gives the details. In the source, a form of type $e$ is cuspidal at once, since the discrete series coefficients have vanishing constant terms. This removes the need to separate cusp forms from Eisenstein series.

### Groups compact at infinity

Suppose that $\mathbf{G}(F \otimes \mathbb{R})$ is compact. This is the case of a unitary group $U(V)$ of a totally definite hermitian space $V$ over a CM field $E$. Then $\mathbf{G}(F)$ is a discrete and cocompact subgroup of $\mathbf{G}(\mathbb{A}_f)$, and for every open compact subgroup $K_f$ the set $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A}_f) / K_f$ is finite. Its number of elements is the *class number* of $K_f$.

**Definition (Algebraic modular form, Gross).** Let $(\rho, W)$ be an irreducible finite-dimensional algebraic representation of $\mathbf{G}$, restricted to $\mathbf{G}(F)$. An *algebraic modular form of weight $W$ and level $K_f$* is a function $\varphi : \mathbf{G}(\mathbb{A}_f) \to W$ with $\varphi(\gamma g k) = \rho(\gamma)\varphi(g)$ for $\gamma \in \mathbf{G}(F)$, $g \in \mathbf{G}(\mathbb{A}_f)$ and $k \in K_f$.

Lean: the source's form is `New.AlgForm` together with `New.Space.forms` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

This is the definition of Gross, *Algebraic modular forms*, Israel J. Math. 113 (1999), 61 to 93. Let $g_1, \dots, g_h$ be representatives of the double cosets, and let $\Gamma_i = \mathbf{G}(F) \cap g_i K_f g_i^{-1}$. Each $\Gamma_i$ is finite, since it is discrete in the compact group $g_i K_f g_i^{-1}$. A form is fixed by its values $\varphi(g_i)$, and $\varphi(g_i)$ can be any vector of $W$ that $\rho(\Gamma_i)$ fixes. So the space of forms is $\bigoplus_{i=1}^{h} W^{\Gamma_i}$, and its dimension is $\sum_i \dim W^{\Gamma_i}$. If all $\Gamma_i$ are trivial, the dimension is $h \cdot \dim W$. The source proves this formula in Section 6. It is the reason that the source can compute dimensions and inner products by finite sums.

For such a group the integral over the quotient is a finite sum. For a function $f$ on $\mathbf{G}(F) \backslash \mathbf{G}(\mathbb{A}_f)$ that is right $K_f$-invariant, and the Haar measure with $\operatorname{vol}(K_f) = 1$, we have $\int f = \sum_{i=1}^{h} f(g_i) / \#\Gamma_i$. The source takes this sum as the definition of its class sum. Section 3 gives the definition, and Section 7 proves the match with the integral.

### Hecke operators

Let $\Gamma \subset G$ be a subgroup, and let $\alpha \in G$ be such that $\Gamma \alpha \Gamma$ is a finite union of cosets $\alpha_i \Gamma$. The classical Hecke operator of $\Gamma\alpha\Gamma$ acts on $\Gamma$-invariant vectors $v$ of a representation $\pi$ of $G$ by $[\Gamma\alpha\Gamma] v = \sum_i \pi(\alpha_i) v$.

**Definition (Hecke operator).** Let $K_f$ be an open compact subgroup of $\mathbf{G}(\mathbb{A}_f)$ and $f$ a $K_f$-bi-invariant function with compact support on $\mathbf{G}(\mathbb{A}_f)$. For a smooth representation $\pi$ of $\mathbf{G}(\mathbb{A}_f)$ and a $K_f$-fixed vector $v$, put $\pi(f)v = \int f(g)\pi(g)v\, dg$, for the Haar measure with $\operatorname{vol}(K_f) = 1$. If $KgK = \bigsqcup_i g_i K$, then $\pi(\mathbf{1}_{KgK})v = \sum_i \pi(g_i)v$.

Lean: the source's form is `New.heckeFun` (Lib/Adelic/Hecke/Basic.lean).

This is the operator of Shimura (1971), Chapter 3, in adelic form. For $\mathbf{G} = \mathrm{GL}_2$, $K_f = \mathrm{GL}_2(\hat{\mathbb{Z}})$ and $g$ the element $\operatorname{diag}(p, 1)$ at $p$, it is the operator $T_p$ of Diamond and Shurman (2005), Chapter 5, up to a power of $p$ that depends on the normalization. The operators of $K_f$-bi-invariant functions with compact support form an algebra under convolution, the Hecke algebra of $K_f$. At a place where $K_f$ is hyperspecial the local Hecke algebra is commutative, by the Satake isomorphism. Its eigenvalues on a form are the Satake parameters, which the source packs into Hecke polynomials. Section 7 states the source's definition of a Hecke polynomial at a split place and its spanning theorem.

### What the source keeps and what it drops

The source keeps three things: invariance under the rational points, a level in $G_f$, and a condition at the archimedean places that fixes one discrete series type. It drops the general $\mathfrak{z}$-finite forms and the Eisenstein series, which the argument does not need. It replaces moderate growth by boundedness, which is enough for forms that generate a discrete series, since such forms are cuspidal. On a definite group it uses Gross's algebraic forms. The Hecke operators enter only through finite sums over cosets, and the integrals over a definite quotient enter only through finite sums over classes. The next section gives these finite sums.
