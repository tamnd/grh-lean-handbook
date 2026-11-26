---
title: Block determinants
lean:
  - Lib/General/Algebra/BlockFittingBound.lean
decls:
  - New.Selmer.exists_rows_addVal_det_le
  - New.Selmer.DivisibleQuot
  - New.Selmer.divQuot
  - New.Selmer.divQuot_injective
  - New.Selmer.exists_divQuot_eq
  - New.Selmer.exists_smul_eq_zero_divisibleQuot
  - New.Selmer.addVal_le_length_torsionBy
  - New.Selmer.exists_rows_addVal_det_le_of_divisible
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Block determinants

Section 5 bounds a Fitting ideal over a ring $R$ of polynomials. Ribet's lemma needs a second kind of bound. There the ring is a Hecke algebra $A$ with a representation $\psi \colon A \to M_d(O)$, and the question is how small the valuation of $\det \psi(B)$ can be for a square matrix $B$ with rows in a module of relations $N \subseteq A^\iota$. Here $\psi(B)$ is the $(\iota \times d) \times (\iota \times d)$ block matrix whose block $(k, j)$ is $\psi(B_{kj})$. The file `Lib/General/Algebra/BlockFittingBound.lean` gives the bound in 181 lines. The use is in [the Ribet elements](/chapter/ribet-elements/) of Volume 12.

### The textbook form

Let $O$ be a discrete valuation ring with fraction field $K$. For a finitely generated torsion $O$-module $M$ with a square relation matrix $D$, the length of $M$ is $v(\det D)$. The Pontryagin type dual $\operatorname{Hom}_O(M, K/O)$ has the same length as $M$. So "the solutions in $K/O$ of the relations have length at most $b$" says "some square relation matrix has determinant of valuation at most $b$". This is the theorem on elementary divisors (Lang, *Algebra*, Chapter III, Section 7) together with Matlis duality for a discrete valuation ring, in the simple form that $\operatorname{Hom}_O(O/\varpi^a, K/O) \cong O/\varpi^a$.

Ribet's application has two changes. The relations live over $A$, not over $O$, and the determinant is taken after $\psi$. The hypothesis that $\psi$ is onto makes the passage possible: every family of $d$ linear forms in the span of the rows of the matrices $\psi(t)$, $t \in N$, is the family of rows of a single $\psi(t)$.

### The bound modulo $p$

Write $O/p$ for `QuotSpan p`. The matrices $M_d(O)$ act on $(O/p)^d$ by multiplication.

**Theorem.** Let $O$ be a discrete valuation ring with normalized valuation $v$, $A$ an $O$-algebra, and $\psi \colon A \to M_d(O)$ an $O$-algebra map that is onto. Let $N$ be an $A$-submodule of $A^\iota$ with $\iota$ finite. Let $p \neq 0$ and $b \in \mathbb{N} \cup \{\infty\}$ with $b < v(p)$. Let $Z$ be an $O$-submodule of $((O/p)^d)^\iota$ of length at most $b$ that contains every $w$ with
$$\sum_{j \in \iota} \psi(t_j)\, w_j = 0 \quad \text{for all } t \in N.$$
Then there is a square matrix $B$ over $A$ with rows in $N$ such that $v(\det \psi(B)) \leq b$, where $\psi(B)$ is the block matrix.

Lean: `New.Selmer.exists_rows_addVal_det_le` (Lib/General/Algebra/BlockFittingBound.lean). The block matrix is `Matrix.comp ι ι d d O (B.map ψ)`.

*Proof.* Let $\sigma \colon A^\iota \to O^{\iota \times d}$ send $t$ to the sum of the rows of the $d \times (\iota \times d)$ matrix $(\psi(t_j))_j$: $\sigma(t)_{(j,l)} = \sum_c \psi(t_j)_{c l}$. Let $L = p O^{\iota \times d} + \sigma(N)$. By the duality lemma of Section 4 (`New.exists_matrix_addVal_det_le_length`), there are a square matrix $M$ with rows in $L$ and a module $S$ of vectors modulo $p$, whose annihilator in $O^{\iota \times d}$ is $L$, with $v(\det M) \leq \operatorname{len}(S)$.

First, $S$ embeds in $Z$. Let $w \in S$ and $t \in N$. Fix $i \in d$ and choose $e \in A$ with $\psi(e)$ equal to the matrix unit $E_{ii}$. Then $\sigma(e t)$ is row $i$ of the matrices $\psi(t_j)$. It lies in $L$, so it is orthogonal to $w$. So row $i$ of $\sum_j \psi(t_j) w_j$ is $0$. This holds for all $i$, so $w \in Z$, and $v(\det M) \leq b$.

Second, write each row $(k, c)$ of $M$ as $p u_{kc} + \sigma(t_{kc})$ with $t_{kc} \in N$. Choose $e_c \in A$ with $\psi(e_c)$ equal to the matrix whose row $c$ has all entries $1$ and whose other rows are $0$. Put $B_k = \sum_c e_c t_{kc}$, which lies in $N$. Row $(k, c)$ of $\psi(B)$ is then $\sigma(t_{kc})$. So $\det \psi(B) \equiv \det M \pmod p$. Since $v(\det M) \leq b < v(p)$, the two determinants have the same valuation. $\square$

The preimages $e$ and $e_c$ come from a right inverse of $\psi$, which exists since $\psi$ is onto. The proof uses choice for it and for the decomposition of the rows of $M$. The conclusion is existential, so the choices do not matter.

### Coefficients in $K/O$

Ribet's lemma counts cocycles with values in $K/O$, not in $O/p$, since the Selmer bound of Volume 12 is for a divisible module. The file passes from one to the other.

**Definition.** Let $O$ be a discrete valuation ring with fraction field $K$. The module `DivisibleQuot O` is $K/O$, the quotient of $K$ by the submodule $1 = O$. For $a \in O$, the map $\operatorname{divQuot}_a \colon O/a \to K/O$ sends the class of $t$ to the class of $t/a$.

Lean: `New.Selmer.DivisibleQuot`, `New.Selmer.divQuot` (Lib/General/Algebra/BlockFittingBound.lean).

**Lemma.** Let $a \neq 0$.

1. The map $\operatorname{divQuot}_a$ is injective.
2. Every $y \in K/O$ with $a y = 0$ is $\operatorname{divQuot}_a(x)$ for some $x \in O/a$.
3. Every $y \in K/O$ is killed by some $d \neq 0$.

Lean: `New.Selmer.divQuot_injective`, `New.Selmer.exists_divQuot_eq`, `New.Selmer.exists_smul_eq_zero_divisibleQuot` (Lib/General/Algebra/BlockFittingBound.lean). Part 3 holds for every $y$ and does not need $a$.

So $\operatorname{divQuot}_a$ identifies $O/a$ with the $a$-torsion of $K/O$.

**Remark (Formalization).** The map $\operatorname{divQuot}_a$ is defined for all $a$, with the inverse $a^{-1}$ taken in the field $K$. For $a = 0$ the source uses Lean's convention $0^{-1} = 0$, so $\operatorname{divQuot}_0$ is the zero map from $O/0 = O$ to $K/O$. This is a junk value. Each lemma that needs the map to be injective has the hypothesis $a \neq 0$.

**Lemma.** Let $X$ be an $O$-module in which every element is killed by some nonzero element of $O$. If the $a$-torsion $X[a]$ is not all of $X$, then $v(a) \leq \operatorname{len}_O X[a]$.

Lean: `New.Selmer.addVal_le_length_torsionBy` (Lib/General/Algebra/BlockFittingBound.lean).

*Proof.* Take $z$ with $a z \neq 0$. Its annihilator is $(b)$ for some $b$. Since $O$ is a valuation ring, $a \mid b$ or $b \mid a$, and $b \mid a$ would give $a z = 0$. So $b = a c$ with $c \neq 0$, since $z$ is torsion. The element $c z$ has annihilator exactly $(a)$, so $O/a$ embeds in $X[a]$. By the length lemma of Section 2, $\operatorname{len}(O/a) = v(a)$. $\square$

For $X = K/O$ with $a = 0$ the lemma is empty, since $X[0] = X$. The source uses it in `New/Congruences/Selmer/Line.lean` and `New/Congruences/FirstOrder/RibetLemma.lean`: if a Selmer module is not killed by $a$, then its $a$-torsion is already large.

**Theorem (Divisible form).** Let $O$, $A$, $\psi$, $N$ be as in the theorem above, and let $b \in \mathbb{N}$. Let $Z$ be an $O$-submodule of $((K/O)^d)^\iota$ of length at most $b$ that contains every $w$ with $\sum_j \psi(t_j)\, w_j = 0$ for all $t \in N$. Then there is a square matrix $B$ over $A$ with rows in $N$ such that $v(\det \psi(B)) \leq b$.

Lean: `New.Selmer.exists_rows_addVal_det_le_of_divisible` (Lib/General/Algebra/BlockFittingBound.lean).

*Proof.* Choose a uniformizer $\varpi$ and put $p = \varpi^{b+1}$. Then $p \neq 0$ and $b < v(p)$. The map $\operatorname{divQuot}_p$, applied in each entry, is an injective $O$-linear map $E \colon ((O/p)^d)^\iota \to ((K/O)^d)^\iota$ that commutes with the action of the matrices. So $E^{-1}(Z)$ has length at most $b$, and it contains every $w$ modulo $p$ that $\psi(N)$ kills. Apply the theorem modulo $p$ to $E^{-1}(Z)$. $\square$

Here $b$ is a natural number, not an element of $\mathbb{N} \cup \{\infty\}$. For $b = \infty$ there is no $p$ with $b < v(p)$. In that case the statement would say nothing, since every valuation is at most $\infty$.

### How Volume 12 uses the bound

The lemma `New.Selmer.exists_block_rows` in `New/Congruences/FirstOrder/FittingBlock.lean` applies the divisible form. In it, $\rho \colon G \to M_r(O)$ is a monoid map whose values span $M_r(O)$ over $O$, $\psi_0 \colon A \to M_r(O)$ agrees with $\rho$ on the images of the group elements, and $N$ is a module of rows that holds the cocycle rule for the vectors $z(g)$, the normalization $z(\mathrm{gen}_i) = e_i$, some linear relations, and the vanishing at the elements $\tau_k$ and $\gamma$. The module $Z$ is the module `New.Selmer.ribetCocyclesVanishingOn` of cocycles with values in $(K/O)^r$ that obey the same relations and vanish at the same elements. The hypothesis that $\rho$ spans $M_r(O)$ makes $\psi_0$ onto. A vector $w$ killed by $\psi_0(N)$ defines a form $\Psi$ on $O^\iota$, and $\Psi \circ z$ is such a cocycle. The conclusion is a square matrix $B_0$ with rows in $N$ and
$$v\bigl(\det \psi_0(B_0)\bigr) \leq b_0,$$
where $b_0$ bounds the length of those cocycles. [The Ribet elements](/chapter/ribet-elements/) states the lemma in full and turns $\det \psi_0(B_0)$ into a Ribet element.

**Remark (Formalization).** The theorem modulo $p$ is not used by name outside its file. Only the divisible form is used, in `New.Selmer.exists_block_rows`. The theorem modulo $p$ is not dead code, since the divisible form is proved from it. The docstring of the file lists its relation to the literature as "general linear algebra over a discrete valuation ring (elementary divisors)", with no specific reference. The references given in this section are the ones this handbook uses for the same facts.

### A small example

Take $O = \mathbb{Z}_p$, $A = O$, $d = 1$, $\psi$ the identity and $\iota = \{1, 2\}$. Let $N$ be the span of the rows $(p^2, 0)$ and $(0, p)$, and of $(p^3, p)$. The solutions $w \in (K/O)^2$ of $p^2 w_1 = 0$ and $p w_2 = 0$ form $p^{-2}\mathbb{Z}_p/\mathbb{Z}_p \times p^{-1}\mathbb{Z}_p/\mathbb{Z}_p$, of length $3$. The third row adds no condition. With $b = 3$ the theorem gives a matrix $B$ with rows in $N$ and $v(\det B) \leq 3$. The diagonal matrix $\operatorname{diag}(p^2, p)$ is such a $B$, and every square matrix with rows in $N$ has determinant divisible by $p^3$. So the bound is sharp here.
