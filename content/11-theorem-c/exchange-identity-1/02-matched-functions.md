---
title: Matched functions
lean:
  - Lib/General/LinearAlgebra/PartnerAlgebra.lean
  - Lib/Adelic/Adeles/LocalFactors.lean
  - Lib/SiegelWeil/Tower/LineGaussSums.lean
  - New/Determinant/Exchange/MatchingPartners.lean
decls:
  - New.SemilocalField
  - New.invLastRows
  - New.firstCols
  - New.AreMatched
  - New.invLastRows_mul_firstCols
  - New.det_fromRows_invLastRows
  - New.Rows.blockRowDatum
  - New.Rows.blockColDatum
  - New.Rows.areMatched_block
  - New.stdColDatum
  - New.stdRowDatum
  - New.areMatched_stdRowDatum_stdColDatum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Matched functions

This section defines the local objects of the exchange identity. They live at the ramified places of a split tame character. There the large side of the identity has a function $\Phi$ of $a \times n$ matrices, and the small side has a function $\Psi$ of $n \times b$ matrices. The two functions are *matched* if they are supported on complementary blocks of the same invertible integral matrices, with values that differ by a character of the determinant. The section gives two families of matched pairs: the block determinant functions, and the standard pair of an integral matrix. Both come from Jacobi's identity for complementary minors.

### The ring

At the ramified places the scalars are a finite product of non-archimedean local fields. The source uses a weaker structure.

**Definition.** A *semilocal field* is a commutative topological ring $F$, Polish and locally compact, with an additive Haar measure, together with a subring $O$ and a unit $\varpi$ of $F$, such that: $O$ is compact and open and has volume $1$; $\varpi \in O$ and the powers $\varpi^k$ tend to $0$; and for all $x, y \in F$ there is an idempotent $\epsilon$ of $O$ such that $x$ and $y$ are $O$-multiples of $(1 - \epsilon)x + \epsilon y$.

Lean: `New.SemilocalField` (Lib/Adelic/Adeles/LocalFactors.lean).

In a product of local fields, $O$ is the product of the rings of integers and $\varpi$ is a product of uniformizers. The last condition is the valuation pair condition: in each factor, one of $x$ and $y$ divides the other, and $\epsilon$ selects the factors where $y$ divides $x$. The source uses the condition to complete primitive matrices to invertible integral ones. A matrix is *primitive* if it has entries in $O$ and a left inverse with entries in $O$; see [Witt's theorem in Volume 4](/chapter/adeles-hermitian-spaces/).

### Complementary blocks

Fix finite index sets $a$, $b$, $n$ and a bijection $e \colon b \sqcup a \to n$. So $b$ indexes the first coordinates of $n$ and $a$ the last ones. For an invertible $n \times n$ matrix $k$ over a commutative ring $R$:

**Definition.** The matrix $x_k$ is the $a \times n$ matrix of the rows of $k^{-1}$ indexed by $a$. The matrix $y_k$ is the $n \times b$ matrix of the columns of $k$ indexed by $b$.

Lean: `New.invLastRows`, `New.firstCols` (Lib/General/LinearAlgebra/PartnerAlgebra.lean).

**Lemma (Jacobi's identity).** For every invertible $k$:

1. $x_k\, y_k = 0$.
2. For every $b \times n$ matrix $s$, let $(s; x_k)$ be the square matrix with the rows of $s$ at $b$ and the rows of $x_k$ at $a$. Then $\det(s; x_k) \cdot \det k = \det(s\, y_k)$.

Lean: `New.invLastRows_mul_firstCols`, `New.det_fromRows_invLastRows` (Lib/General/LinearAlgebra/PartnerAlgebra.lean).

*Proof.* The entries of $x_k y_k$ are entries of $k^{-1} k = 1$ in the rows $a$ and the columns $b$. These are off the diagonal, so they are $0$. For the second statement, $(s; x_k)\, k$ has the rows $s k$ at $b$ and the rows $x_k k$ at $a$. The rows $x_k k$ are the rows $a$ of the identity. So in the order $b \sqcup a$,
$$(s; x_k)\, k = \begin{pmatrix} s\, y_k & s\, k_a \\ 0 & 1 \end{pmatrix},$$
where $k_a$ is the matrix of the columns $a$ of $k$. The determinant of a block triangular matrix is the product of the determinants of the diagonal blocks, so it is $\det(s\, y_k)$. $\square$

If $s$ is the matrix $(1\ 0)$ of the rows $b$ of the identity, then $(s; x_k)$ is block triangular too, and the identity reads $\det x_{k,2} \cdot \det k = \det y_{k,1}$. Here $x_{k,2}$ is the square block of $x_k$ in the columns $a$, and $y_{k,1}$ is the square block of $y_k$ in the rows $b$. This is the classical statement: a minor of $k^{-1}$ is $(\det k)^{-1}$ times the complementary minor of $k$.

### Matched functions

Let $O$ be a subring of $R$, and let $GL_n(O)$ be the invertible matrices $k$ such that $k$ and $k^{-1}$ have entries in $O$. Let $\chi$ be a multiplicative character of $R$, with values in $\mathbb{C}$. As usual for a multiplicative character, $\chi(r) = 0$ if $r$ is not a unit.

**Definition.** Functions $\Phi$ on $a \times n$ matrices and $\Psi$ on $n \times b$ matrices are *matched* for $\chi$ over $O$ if:

1. $\Phi(x) \neq 0$ only if $x = x_k$ for some $k \in GL_n(O)$;
2. $\Psi(y) \neq 0$ only if $y = y_k$ for some $k \in GL_n(O)$;
3. $\Phi(x_k) = \chi(\det k)\, \Psi(y_k)$ for every $k \in GL_n(O)$.

Lean: `New.AreMatched` (Lib/General/LinearAlgebra/PartnerAlgebra.lean).

A given $x$ is $x_k$ for many $k$. The third condition is therefore a compatibility condition: if $x_k = x_{k'}$, then $\chi(\det k)\Psi(y_k) = \chi(\det k')\Psi(y_{k'})$. Section 3 shows that this compatibility follows from the structure of the cosets of $GL_b(O)$.

### Block determinant functions

Write an $a \times n$ matrix as $x = (x_1\ x_2)$, with $x_1$ the $a \times b$ block of the columns $b$ and $x_2$ the square $a \times a$ block. Write an $n \times b$ matrix as $y = (y_1; y_2)$, with $y_1$ the square $b \times b$ block of the rows $b$ and $y_2$ the $a \times b$ block.

**Definition.** For a function $f$ on $a \times b$ matrices put
$$\Phi_f(x_1\ x_2) = \chi^{-1}(\det x_2)\, f(x_2^{-1} x_1), \qquad \Psi_f(y_1; y_2) = \chi^{-1}(\det y_1)\, f(-y_2\, y_1^{-1}).$$

Lean: `New.Rows.blockRowDatum`, `New.Rows.blockColDatum` (New/Determinant/Exchange/MatchingPartners.lean).

Both functions vanish unless the square block is invertible, because $\chi^{-1}$ vanishes on the non-units.

**Proposition.** For every $f$, the functions $\Phi_f$ and $\Psi_f$ are matched for $\chi$ over the whole ring $R$.

Lean: `New.Rows.areMatched_block` (New/Determinant/Exchange/MatchingPartners.lean).

*Proof.* Over $O = R$, the group $GL_n(O)$ is the group of all invertible matrices.

Support of $\Phi_f$. If $\Phi_f(x) \neq 0$, then $\det x_2$ is a unit. The block matrix $m = \begin{pmatrix} 1 & 0 \\ x_1 & x_2 \end{pmatrix}$, in the order $b \sqcup a$, has determinant $\det x_2$, so it is invertible. Put $k = m^{-1}$. The rows $a$ of $k^{-1} = m$ are $x$, so $x = x_k$.

Support of $\Psi_f$. If $\Psi_f(y) \neq 0$, then $\det y_1$ is a unit. Put $k = \begin{pmatrix} y_1 & 0 \\ y_2 & 1 \end{pmatrix}$. It has determinant $\det y_1$, so it is invertible, and its columns $b$ are $y$.

Values. Let $k$ be invertible, and write $x_k = (x_1\ x_2)$ and $y_k = (y_1; y_2)$. Jacobi's identity with $s = (1\ 0)$ gives $\det y_1 = \det x_2 \cdot \det k$. The relation $x_k y_k = 0$ reads $x_1 y_1 + x_2 y_2 = 0$ in blocks. Suppose first that $\det x_2$ is a unit. Then $\det y_1$ is a unit, and $y_2 = -x_2^{-1} x_1 y_1$. So $-y_2 y_1^{-1} = x_2^{-1} x_1$, and the arguments of $f$ agree. For the factors,
$$\chi(\det k)\, \chi^{-1}(\det y_1) = \chi(\det k)\, \chi^{-1}(\det x_2)\, \chi^{-1}(\det k) = \chi^{-1}(\det x_2).$$
So $\Phi_f(x_k) = \chi(\det k)\Psi_f(y_k)$. Suppose next that $\det x_2$ is not a unit. Then $\det y_1 = \det x_2 \det k$ is not a unit either, so both sides are $0$. $\square$

**Remark (Formalization).** In the formulas, $x_2^{-1}$ and $y_1^{-1}$ are the matrix inverses of Mathlib, which are $0$ for a singular matrix. These values never matter, because the factor $\chi^{-1}(\det x_2)$ or $\chi^{-1}(\det y_1)$ is then $0$. The source uses the block pair in the chapter on seesaw squares and in the explicit matching of [the second part](/chapter/exchange-identity-2/).

**Example.** Let $b = a = \{1\}$ and $n = 2$, with $b$ first. Then $x = (x_1\ x_2)$ is a row and $y = (y_1; y_2)$ is a column, and
$$\Phi_f(x_1\ x_2) = \chi^{-1}(x_2)\, f(x_1/x_2), \qquad \Psi_f(y_1; y_2) = \chi^{-1}(y_1)\, f(-y_2/y_1).$$
Let $k = \begin{pmatrix} p & q \\ r & t \end{pmatrix}$ with $D = pt - qr$ a unit. Then $k^{-1} = D^{-1}\begin{pmatrix} t & -q \\ -r & p \end{pmatrix}$, so $x_k = (-r/D\ \ p/D)$ and $y_k = (p; r)$. If $p$ is a unit,
$$\Phi_f(x_k) = \chi^{-1}(p/D)\, f(-r/p) = \chi(D)\, \chi^{-1}(p)\, f(-r/p) = \chi(D)\, \Psi_f(y_k).$$
Jacobi's identity here is the statement that the entry $p/D$ of $k^{-1}$ is $D^{-1}$ times the entry $p$ of $k$.

### The standard pair

The standard data of [the tower](/chapter/rallis-inner-product/#the-tower) are matched too. Now let $F$ be a semilocal field with ring $O$, and write $\chi^{-1}_O(t)$ for $\chi(t)^{-1}$ if $t$ is a unit of $O$ and $0$ otherwise.

**Definition.** For a $b \times n$ matrix $s$, the *standard column datum* is $\Psi_s(y) = \chi^{-1}_O(\det(s y))$ if $y$ has entries in $O$, and $0$ otherwise. The *standard row datum* is $\Phi_s(x) = \chi^{-1}_O(\det(s; x))$ if $(s; x)$ has entries in $O$, and $0$ otherwise.

Lean: `New.stdColDatum`, `New.stdRowDatum` (Lib/SiegelWeil/Tower/LineGaussSums.lean).

So $\Phi_s(x) \neq 0$ exactly when $(s; x) \in GL_n(O)$, and $\Psi_s(y) \neq 0$ exactly when $y$ is integral and $\det(s y)$ is a unit of $O$.

**Proposition.** If $s$ has entries in $O$, then $\Phi_s$ and $\Psi_s$ are matched for $\chi$ over $O$.

Lean: `New.areMatched_stdRowDatum_stdColDatum` (Lib/SiegelWeil/Tower/LineGaussSums.lean).

*Proof.* Support of $\Phi_s$. If $\Phi_s(x) \neq 0$, then $m = (s; x)$ lies in $GL_n(O)$. Put $k = m^{-1} \in GL_n(O)$. The rows $a$ of $k^{-1} = m$ are $x$, so $x = x_k$.

Support of $\Psi_s$. If $\Psi_s(y) \neq 0$, then $y$ is integral and $s y$ is an integral square matrix with a unit determinant, so $(s y)^{-1}$ is integral. Then $(s y)^{-1} s$ is an integral left inverse of $y$, and $y$ is primitive. By the valuation pair condition a primitive matrix is the block $y_k$ of some $k \in GL_n(O)$.

Values. Let $k \in GL_n(O)$. Jacobi's identity gives $\det(s; x_k) \det k = \det(s y_k)$, and $\det k$ is a unit of $O$. The matrix $(s; x_k)$ is integral. If $\det(s; x_k)$ is a unit of $O$, then so is $\det(s y_k)$, and
$$\Phi_s(x_k) = \chi^{-1}(\det(s; x_k)) = \chi^{-1}\bigl(\det(s y_k)\bigr)\, \chi(\det k) = \chi(\det k)\, \Psi_s(y_k).$$
Otherwise neither determinant is a unit, and both sides are $0$. $\square$

In Section 5 the matrix $s$ is the dual basis of a self-dual lattice, and $\Psi_s$ is the datum at which an equivariant lift is tested.
