---
title: Eigenforms, Hecke polynomials and weights
lean:
  - Lib/GaloisRep/Main/Defs.lean
decls:
  - New.coeff_heckePoly
  - New.HasHeckePolyAt.isMonicOfDegree
  - New.jumps
  - New.Weight.nodup_jumps
  - New.HasLabel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Eigenforms, Hecke polynomials and weights

An attached representation is attached to a family of polynomials, one at each finite place. This section recalls where the polynomials come from, proves the two facts about them that the later sections use, and gives the integers that a weight fixes as Hodge-Tate jumps.

### The setting

Let $E$ be a CM field with complex conjugation $w \mapsto \bar w$ on places, and let $n$ be a finite set. The source writes $G_f$ for the finite adelic points of the definite unitary group of rank $|n|$ (Lean `New.Gf E n`), and lets $G_f$ act on functions $f : G_f \to M$ by right translation. A finite place $w$ is *split* when $\bar w \neq w$. At a split place, $\mathrm{GL}_n(E_w)$ embeds in $G_f$, and $T_{w,j}$ is the $j$-th Hecke operator at $w$. Let $q_w$ be the order of the residue field at $w$. The chapter [Iwahori and Satake](/chapter/iwahori-satake/) defines $T_{w,j}$ (Lean `New.heckeSplit`) and the subgroup $K_w$ (Lean `New.maxCompactAt`) of elements that are integral at $w$ and $\bar w$ and $1$ elsewhere.

The chapter [Automorphic forms](/chapter/automorphic-forms/) states the following three definitions in full. We recall them.

The *Hecke polynomial* of degree $N$ of numbers $t_0, t_1, \ldots$ is
$$P_{q,N}(t) = \sum_{j=0}^{N} (-1)^j q^{j(j-1)/2}\, t_j\, X^{N-j}$$
([Definition](/decl/New.heckePoly/)). A function $f$ *has Hecke polynomial $P$ at the split place $w$* ([Definition](/decl/New.HasHeckePolyAt/)) if $K_w$ fixes $f$ and there are numbers $t_j$ with $T_{w,j} f = t_j f$ for all $j$ and $P = P_{q_w, |n|}(t)$. A function $f$ is an *eigenform* for a family $P = (P_w)$ of complex polynomials ([Definition](/decl/New.IsEigenform/)) if $f \neq 0$ and, for all but finitely many $w$, if $q_w$ is prime then $w$ is split and $f$ has Hecke polynomial $P_w$ at $w$.

For $|n| = 1$ the Hecke polynomial is $t_0 X - t_1$. For $|n| = 2$ it is $t_0 X^2 - t_1 X + q_w t_2$. Compare the classical $X^2 - a_p X + \chi(p)p^{k-1}$: the eigenvalue $t_1$ of the first Hecke operator plays the part of $a_p$.

**Remark (Formalization).** The family $P$ of an eigenform is a function on all finite places. Its values at the finitely many exceptional places and at places whose norm is not prime are not constrained. They are junk values. Section 4 shows that the notion "attached" does not read them.

### The coefficients

**Lemma.** For $q, N, j \in \mathbb{N}$ and a sequence $t$ in a commutative ring, the coefficient of $X^j$ in $P_{q,N}(t)$ is $(-1)^{N-j} q^{\binom{N-j}{2}} t_{N-j}$ if $j \leq N$, and $0$ if $j > N$.

Lean: `New.coeff_heckePoly` (Lib/GaloisRep/Main/Defs.lean).

*Proof.* The polynomial is the sum over $i \leq N$ of $(-1)^i q^{\binom{i}{2}} t_i X^{N-i}$. The term of index $i$ has degree $N - i$. So only $i = N - j$ can contribute to $X^j$, and it exists exactly when $j \leq N$. $\square$

**Remark (Formalization).** Lean writes the index as the natural number $N - j$. For $j > N$ this is $0$, so the right side is $0 \cdot t_0$, which is $0$. The statement is correct for all $j$, with no case on $j$ in the type.

**Lemma.** Let $f \neq 0$ be a function on $G_f$, and let $f$ have Hecke polynomial $P$ at the split place $w$. Then $P$ is monic of degree $|n|$.

Lean: `New.HasHeckePolyAt.isMonicOfDegree` (Lib/GaloisRep/Main/Defs.lean).

*Proof.* Let $t$ be the eigenvalues. The operator $T_{w,0}$ is the identity on vectors fixed by $K_w$ (Lean `New.heckeGL_zero`, `Lib/Weil/Unramified/HeckeGL.lean`), and $K_w$ fixes $f$. So $f = T_{w,0} f = t_0 f$. Since $f \neq 0$, $t_0 = 1$. By the lemma above, the coefficient of $X^{|n|}$ is $t_0 = 1$, and the coefficients of $X^j$ for $j > |n|$ are $0$. $\square$

**Remark (Formalization).** The hypothesis $f \neq 0$ is needed. The zero function has Hecke polynomial $P_{q_w, |n|}(t)$ at $w$ for every sequence $t$, since $T_{w,j} 0 = t_j \cdot 0$. So $0$ has many Hecke polynomials, and some of them are $0$. An eigenform is nonzero by definition, so for an eigenform the lemma applies at almost all places of prime norm.

The roots of the Hecke polynomial are the Satake parameters. Volume 5 proves the following (Section 4 of [Iwahori and Satake](/chapter/iwahori-satake/)): if a spherical vector $x$ has an exponent for unramified characters $\theta_0, \ldots, \theta_{N-1}$ of $E_w^\times$, then its Hecke polynomial is $\prod_{i} (X - \theta_i(\varpi))$ for a uniformizer $\varpi$. The eigenvalues there are $t_j = q^{-j(j-1)/2} e_j(\theta_0(\varpi), \ldots, \theta_{N-1}(\varpi))$, so the factor $q^{j(j-1)/2}$ in $P_{q,N}$ cancels the power of $q$.

### Weights and jumps

A *weight* $\kappa$ for $E$ is a pair. For an infinite place $v$ and $h \in \mathbb{N}$, $\kappa_1(v, h)$ is the number of columns of height $h$ of a Young diagram, and $\kappa_2(v) \in \mathbb{Z}$ is a power of the determinant ([Definition](/decl/New.Weight/), in [Automorphic forms](/chapter/automorphic-forms/)). Forms of weight $\kappa$ take values in the space $\mathbb{C}^{I}$ of the weight-$\kappa$ representation, where $I$ is an index set of tableaux (Lean `New.WeylIndex n κ.1`).

**Definition (Jumps of a weight).** Let $E$ have a CM type $\Phi$, which picks an embedding $\Phi(v) : E \to \mathbb{C}$ at each infinite place $v$. Let $\kappa$ be a weight, $N \in \mathbb{N}$, and $\sigma : E \to \mathbb{C}$ an embedding with infinite place $v$. For $1 \leq j \leq N$ put
$$\lambda_j = \kappa_2(v) + \sum_{j \leq h < N} \kappa_1(v, h).$$
The *jumps* of $\kappa$ in rank $N$ at $\sigma$ form the multiset
$$J_{\kappa,N}(\sigma) = \begin{cases} \{\, j - 1 - \lambda_j : 1 \leq j \leq N \,\} & \text{if } \sigma = \Phi(v), \\ \{\, \lambda_j + N - j : 1 \leq j \leq N \,\} & \text{otherwise.} \end{cases}$$

Lean: `New.jumps` (Lib/GaloisRep/Main/Defs.lean).

The sequence $\lambda_1 \geq \lambda_2 \geq \cdots \geq \lambda_N$ is the highest weight of the representation of $\mathrm{GL}_N$ with this Young diagram, twisted by $\det^{\kappa_2(v)}$. The jumps at $\sigma$ and at $\bar\sigma$ are related by $u \mapsto N - 1 - u$, since $\sigma$ and $\bar\sigma$ have the same infinite place and exactly one of them is in $\Phi$. Section 4 meets the twist by the cyclotomic character to the power $1 - N$ that goes with this symmetry.

**Remark (Formalization).** The values $\kappa_1(v, 0)$ and $\kappa_1(v, h)$ for $h \geq N$ do not enter the jumps in rank $N$: the sum runs over $1 \leq j \leq h \leq N - 1$. Columns of height $N$ would change $\lambda$ by a constant, and the source puts that constant in $\kappa_2$. Lean indexes $j$ from $0$, and the code sets $u = \lambda_j + N - j$ and returns $N - 1 - u$ for $\sigma$ in the CM type.

**Lemma.** For every weight $\kappa$, rank $N$ and embedding $\sigma$, the multiset $J_{\kappa,N}(\sigma)$ has no repeated element.

Lean: `New.Weight.nodup_jumps` (Lib/GaloisRep/Main/Defs.lean).

*Proof.* Each $\kappa_1(v, h)$ is a natural number, so $\lambda_i \geq \lambda_j$ for $i < j$, since the sum for $\lambda_i$ has more terms. Then $\lambda_i + N - i > \lambda_j + N - j$. So $j \mapsto \lambda_j + N - j$ is strictly decreasing, hence injective, and so is $j \mapsto N - 1 - (\lambda_j + N - j)$. A multiset that is the image of $\{1, \ldots, N\}$ under an injective map has no repetitions. $\square$

The jumps are *regular*: $N$ distinct integers, as in the classical theory, where a cohomological weight gives distinct Hodge-Tate weights. Section 5 compares them with the jumps of a Galois representation.

### Labels

At a split place where $f$ is not spherical, the source uses a weaker invariant. It reduces integral matrices at $w$ to the residue field $k_w$, and asks how the finite group $\mathrm{GL}_n(k_w)$ acts.

**Definition (Label).** Let $w$ be split and $\Xi$ a function on $\mathrm{GL}_n(k_w)$. A function $f$ on $G_f$ *has the label $\Xi$* at $w$ if

1. every integral matrix at $w$ whose reduction modulo $w$ is $1$ fixes $f$; and
2. the sum $\sum_{x \in \mathrm{GL}_n(k_w)} \overline{\Xi(x)}\, \rho(\tilde x) f$ is not $0$, where $\tilde x$ is a lift of $x$ to an integral matrix at $w$, embedded in $G_f$.

Lean: `New.HasLabel` (Lib/GaloisRep/Main/Defs.lean).

**Remark (Formalization).** The lift $\tilde x$ is chosen with `surjInv` of the surjectivity of the reduction. By part 1 the translate $\rho(\tilde x) f$ does not depend on the choice. The sum is a `finsum`. It is a sum over a finite group, so the convention that `finsum` is $0$ for an infinite support does not occur. When $\Xi$ is the character of an irreducible representation of $\mathrm{GL}_n(k_w)$, part 2 says that $f$ has a nonzero component of that type. The local-global results for labels (Lean `New.GaloisRep.Attached.isLabelledAt`) are in [Building the representations](/chapter/building-representations/).
