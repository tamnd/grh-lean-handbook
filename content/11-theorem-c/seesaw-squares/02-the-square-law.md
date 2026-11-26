---
title: The square law
lean:
  - New/Determinant/Chain/SquareLaw.lean
decls:
  - New.Exchange.SquareLaw
  - New.Exchange.pointDatum
  - New.Exchange.nextDatum
  - New.Exchange.swapFirstTwo
  - New.Exchange.sum_nextDatum_mul
  - New.Exchange.sum_inv_det_mul_eq_card_mul
  - New.Exchange.SquareLaw.card_mul_apply_fromRows_eq
  - New.Exchange.SquareLaw.sum_eq_nextDatum
  - New.Exchange.blockInlGL
  - New.Exchange.matchOf
  - New.Exchange.exists_firstCols_eq_mul_of_invLastRows_eq
  - New.Exchange.areMatched_matchOf
  - New.AreMatched.unique
  - New.AreMatched.translate
  - New.Exchange.hasLeftInv_submatrix_invLastRows
  - New.Exchange.hasLeftInv_toCols_of_hasLeftInv_toRows
  - New.Exchange.exists_eq_firstCols
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The square law

This section is finite linear algebra. It defines the square law, which is the form in which the one square identity is stated and used. It then proves two consequences of the law: the law at one point, and the law for a datum $p$ against a datum $\operatorname{nextDatum}(p)$. The chain of later chapters uses the second one. The section ends with lemmas that build matched partners and recognize blocks of invertible matrices.

Let $R$ be a finite commutative ring and $\chi$ a multiplicative character of $R$ with values in $\mathbb{C}$. Then $\chi(r) = 0$ for $r$ not a unit, and $\chi^{-1}$ is the inverse character, which is also $0$ off the units. We use the blocks $x_k$ and $y_k$ of [complementary blocks](/chapter/exchange-identity-1/#matched-functions): for $e \colon b \sqcup a \simeq n$ and invertible $k$, $x_k$ is the matrix of the rows $a$ of $k^{-1}$ and $y_k$ the matrix of the columns $b$ of $k$. "Matched" means matched over the whole ring $R$, so $GL_n(O)$ is all of $GL_n(R)$.

### The law

**Definition (Square law).** Let $\sigma \colon b \sqcup a \simeq n$, $c \in \mathbb{C}$, $L$ a function on $a \times n$ matrices and $L'$ a function on $n \times b$ matrices over $R$. The pair $(L, L')$ satisfies the *square law* for $\chi$ and $\sigma$ with constant $c$ if:

1. $L(k x) = \chi(\det k)\, L(x)$ for all $k \in GL_a(R)$;
2. $L'(y k) = \chi(\det k)\, L'(y)$ for all $k \in GL_b(R)$;
3. $\sum_y \Psi(y) L'(y) = c \sum_x \Phi(x) L(x)$ for all functions $\Phi$, $\Psi$ that are matched for $\chi$ and $\sigma$.

Lean: `New.Exchange.SquareLaw` (New/Determinant/Chain/SquareLaw.lean).

In the application, $L(x) = l(\Theta_i(x) f)$ and $L'(y) = l(\Theta'_i(y) f)$ are values of the two paths around a square, as in [the statement](/chapter/seesaw-squares/#what-the-chapter-proves).

**Definition (Point datum, next datum).** The *point datum* is the indicator function of the matrix $(1; 0)$ among the $(a \sqcup b) \times a$ matrices. For a function $p$ on $n \times a$ matrices, $\operatorname{nextDatum}(p)$ is the function on $(n \sqcup b) \times (a \sqcup b)$ matrices with
$$\operatorname{nextDatum}(p)\begin{pmatrix} A & B \\ C & D \end{pmatrix} = \begin{cases} p(-A)/|R^{n \times b}| & \text{if } C = 0 \text{ and } D = 1, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.Exchange.pointDatum`, `New.Exchange.nextDatum` (New/Determinant/Chain/SquareLaw.lean).

Here $|R^{n \times b}|$ is the number of all $n \times b$ matrices over $R$. So $\operatorname{nextDatum}(p)$ lives on the matrices $\begin{pmatrix} \eta & s \\ 0 & 1 \end{pmatrix}$, has the value $p(-\eta)$ there, and is averaged over the block $s$.

**Definition.** The bijection $\operatorname{swapFirstTwo} \colon a \sqcup (n \sqcup b) \simeq n \sqcup (a \sqcup b)$ moves the block $a$ to the second place.

Lean: `New.Exchange.swapFirstTwo` (New/Determinant/Chain/SquareLaw.lean).

We use three facts without comment. A sum over matrices with rows $N \sqcup n$ is a double sum over the two row blocks; the same holds for columns, and a sum over block matrices is a fourfold sum over the blocks. The inclusion matrix of $a$ in $a \sqcup b$ is $(1; 0)$ (`New.Exchange.inclMatrix_inl`). Complex conjugation commutes with $\operatorname{nextDatum}$ (`New.Exchange.star_nextDatum`), as it is applied value by value.

**Lemma.** For every function $F$ on $(n \sqcup b) \times (a \sqcup b)$ matrices,
$$\sum_x \operatorname{nextDatum}(p)(x)\, F(x) = \sum_{s} \sum_{\eta} \frac{p(-\eta)}{|R^{n \times b}|}\, F\begin{pmatrix} \eta & s \\ 0 & 1 \end{pmatrix},$$
with $s$ over the $n \times b$ matrices and $\eta$ over the $n \times a$ matrices.

Lean: `New.Exchange.sum_nextDatum_mul` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Write the sum as a fourfold sum over the blocks $A, B, C, D$. The factor $\operatorname{nextDatum}(p)$ is $0$ unless $C = 0$ and $D = 1$, so only these terms remain, with $A = \eta$ and $B = s$. $\square$

**Lemma.** Let $f$ be a function on $a \times a$ matrices and $v \in \mathbb{C}$ with $f(g) = \chi(\det g)\, v$ for all $g \in GL_a(R)$. Then $\sum_u \chi^{-1}(\det u)\, f(u) = |GL_a(R)|\, v$, the sum being over all $a \times a$ matrices $u$.

Lean: `New.Exchange.sum_inv_det_mul_eq_card_mul` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* If $u$ is not invertible, $\det u$ is not a unit and $\chi^{-1}(\det u) = 0$. So the sum is over $GL_a(R)$. For $g$ invertible, $\chi(\det g) \neq 0$, and $\chi^{-1}(\det g)\, \chi(\det g)\, v = v$. The sum of $|GL_a(R)|$ terms $v$ is $|GL_a(R)|\, v$. $\square$

### The law at a point

**Proposition.** Let $(L, L')$ satisfy the square law for $\chi$ and $\sigma$ with constant $c$, and let $w$ be an $a \times b$ matrix. Read $(1; -w)$, with the rows $b$ first, as an $n \times b$ matrix through $\sigma$, and read $(w\ 1)$, with the columns $b$ first, as an $a \times n$ matrix through $\sigma$. Then
$$|GL_b(R)|\, L'(1; -w) = c\, |GL_a(R)|\, L(w\ 1).$$

Lean: `New.Exchange.SquareLaw.card_mul_apply_fromRows_eq` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Let $\delta$ be the indicator function of $w$. By [the block pair](/chapter/exchange-identity-1/#matched-functions) (`New.Rows.areMatched_block`), the functions
$$\Phi_\delta(x_1\ x_2) = \chi^{-1}(\det x_2)\, \delta(x_2^{-1} x_1), \qquad \Psi_\delta(y_1; y_2) = \chi^{-1}(\det y_1)\, \delta(-y_2\, y_1^{-1})$$
are matched. The third clause of the law gives
$$\sum_{y_1} \chi^{-1}(\det y_1) \sum_{y_2} \delta(-y_2 y_1^{-1})\, L'(y_1; y_2) = c \sum_{x_2} \chi^{-1}(\det x_2) \sum_{x_1} \delta(x_2^{-1} x_1)\, L(x_1\ x_2).$$
Compute the inner sums at an invertible block. For $y_1 = g \in GL_b(R)$, the term $\delta(-y_2 g^{-1})$ is $1$ exactly for $y_2 = -w g$. So the inner sum is $L'((1; -w)\, g) = \chi(\det g)\, L'(1; -w)$ by the second clause. For $x_2 = g \in GL_a(R)$, the term $\delta(g^{-1} x_1)$ is $1$ exactly for $x_1 = g w$. So the inner sum is $L(g\,(w\ 1)) = \chi(\det g)\, L(w\ 1)$ by the first clause. Apply the previous lemma to both outer sums. The left side is $|GL_b(R)|\, L'(1; -w)$ and the right side is $c\, |GL_a(R)|\, L(w\ 1)$. $\square$

### The law for the next datum

**Theorem (Square law for the next datum).** Let $L$ be a function on $(n \sqcup b) \times (n \sqcup a \sqcup b)$ matrices and $L'$ a function on $(n \sqcup a \sqcup b) \times a$ matrices. Suppose that $(L, L')$ satisfies the square law for $\chi$ and $\operatorname{swapFirstTwo}$ with constant $c$. Let $\iota$ denote the inclusion matrices $(1; 0)$ of $a$ in $a \sqcup b$ and of $n$ in $n \sqcup b$. Then for every function $p$ on $n \times a$ matrices,
$$|GL_a(R)| \sum_{y} p(y)\, L'(y; \iota) = c\, |GL_{n \sqcup b}(R)| \sum_{x} \operatorname{nextDatum}(p)(x)\, L(\iota\ x).$$
Here $y$ runs over the $n \times a$ matrices, and $x$ over the $(n \sqcup b) \times (a \sqcup b)$ matrices.

Lean: `New.Exchange.SquareLaw.sum_eq_nextDatum` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Step 1, a shear. Fix an $n \times a$ matrix $\eta$ and an $n \times b$ matrix $s$. We show
$$|GL_a(R)|\, L'(-\eta; \iota) = c\, |GL_{n \sqcup b}(R)|\, L\Bigl(\iota\ \ \begin{pmatrix} \eta & s \\ 0 & 1 \end{pmatrix}\Bigr).$$
Here the roles of $b$ and $a$ in the law are played by $a$ and $n \sqcup b$. Put $w = (\eta; 0)$, an $(n \sqcup b) \times a$ matrix. Reorder $(1; -w)$ by $\operatorname{swapFirstTwo}$: the rows $n$ are $-\eta$, the rows $a$ are $1$ and the rows $b$ are $0$. This is $(-\eta; \iota)$. Reorder $(w\ 1)$: the columns $n$ are $\iota$, the columns $a$ are $(\eta; 0)$ and the columns $b$ are $(0; 1)$. Let $u = \begin{pmatrix} 1 & s \\ 0 & 1 \end{pmatrix} \in GL_{n \sqcup b}(R)$. It has determinant $1$, it fixes $\iota$, and it sends the columns $a \sqcup b$ to $\begin{pmatrix} \eta & s \\ 0 & 1 \end{pmatrix}$. So $u\,(w\ 1) = (\iota\ \ (\eta\ s; 0\ 1))$. The first clause gives $L(u\,(w\ 1)) = \chi(1)\, L(w\ 1) = L(w\ 1)$. The law at the point $w$ gives the claim.

Step 2, the sum. By the lemma on $\operatorname{nextDatum}$, the right side is
$$c\, |GL_{n \sqcup b}(R)| \sum_\eta \sum_s \frac{p(-\eta)}{|R^{n \times b}|}\, L\Bigl(\iota\ \ \begin{pmatrix} \eta & s \\ 0 & 1 \end{pmatrix}\Bigr) = \sum_\eta \sum_s \frac{p(-\eta)}{|R^{n \times b}|}\, |GL_a(R)|\, L'(-\eta; \iota)$$
by Step 1. The terms do not depend on $s$, and there are $|R^{n \times b}|$ values of $s$. So the right side is $|GL_a(R)| \sum_\eta p(-\eta) L'(-\eta; \iota)$. Substitute $y = -\eta$. $\square$

### Matched partners

**Definition.** For $e \colon b \sqcup a \simeq n$, the embedding $GL_b(R) \to GL_n(R)$, $g \mapsto g \oplus 1$, in the order of $e$, is $\operatorname{blockInlGL}(e)$.

Lean: `New.Exchange.blockInlGL` (New/Determinant/Chain/SquareLaw.lean).

**Definition (The matched function of $\Psi$).** For a function $\Psi$ on $n \times b$ matrices, $\operatorname{matchOf}(\chi, e, \Psi)$ is the function on $a \times n$ matrices that is $0$ off the matrices $x_\gamma$ and has the value $\chi(\det \gamma)\, \Psi(y_\gamma)$ at $x_\gamma$, for a chosen $\gamma$.

Lean: `New.Exchange.matchOf` (New/Determinant/Chain/SquareLaw.lean).

**Remark (Formalization).** The source defines $\operatorname{matchOf}$ with `Function.extend` along $\gamma \mapsto x_\gamma$. The value at $x_\gamma$ uses a preimage chosen by `Classical.choice`, and the value off the image is $0$. The next two lemmas show that the choice does not matter when $\Psi$ transforms well on the right.

**Lemma.** Let $\gamma, \gamma' \in GL_n(R)$ with $x_\gamma = x_{\gamma'}$. Then there is $h \in GL_b(R)$ with $y_{\gamma'} = y_\gamma h$ and $\det \gamma' = \det \gamma \cdot \det h$.

Lean: `New.Exchange.exists_firstCols_eq_mul_of_invLastRows_eq` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Let $z_\gamma$ be the rows $b$ of $\gamma^{-1}$. Then $z_\gamma y_\gamma = 1$, and $\gamma\gamma^{-1} = 1$ reads $y_\gamma z_\gamma + \gamma_a x_\gamma = 1$, with $\gamma_a$ the columns $a$ of $\gamma$. If $x_\gamma y = 0$, multiply by $y$ and get $y = y_\gamma (z_\gamma y)$. Jacobi's identity gives $x_\gamma y_{\gamma'} = x_{\gamma'} y_{\gamma'} = 0$, so $y_{\gamma'} = y_\gamma h$ with $h = z_\gamma y_{\gamma'}$. In the same way $y_\gamma = y_{\gamma'} h'$ with $h' = z_{\gamma'} y_\gamma$. Then $h h' = z_\gamma y_{\gamma'} z_{\gamma'} y_\gamma = z_\gamma y_\gamma = 1$, and $h' h = 1$ in the same way. So $h$ is invertible. For the determinants, let $d = \det(z_\gamma; x_\gamma)$. Jacobi's identity with $s = z_\gamma$ gives $d \det \gamma = \det(z_\gamma y_\gamma) = 1$. Since $x_\gamma = x_{\gamma'}$, it also gives $d \det \gamma' = \det(z_\gamma y_{\gamma'}) = \det h$. Then $\det \gamma' = \det\gamma' \cdot d \det \gamma = \det \gamma \det h$. $\square$

**Lemma.** Suppose that $\Psi(y) \neq 0$ only if $y = y_\gamma$ for some $\gamma$, and that $\chi(\det h)\, \Psi(y h) = \Psi(y)$ for all $y$ and $h \in GL_b(R)$. Then $\operatorname{matchOf}(\chi, e, \Psi)$ and $\Psi$ are matched.

Lean: `New.Exchange.areMatched_matchOf` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* The first two conditions of matching hold by the definition and by the hypothesis. For the third, we show that $\gamma \mapsto \chi(\det\gamma)\Psi(y_\gamma)$ is constant on the fibers of $\gamma \mapsto x_\gamma$. Then the extension takes the value $\chi(\det \gamma)\Psi(y_\gamma)$ at every $x_\gamma$. Let $x_\gamma = x_{\gamma'}$, and take $h$ from the previous lemma. Then
$$\chi(\det \gamma)\Psi(y_\gamma) = \chi(\det\gamma)\chi(\det h)\Psi(y_\gamma h) = \chi(\det \gamma')\Psi(y_{\gamma'}). \qquad \square$$

**Lemma.** If $\Phi$ and $\Phi'$ are both matched with $\Psi$, then $\Phi = \Phi'$.

Lean: `New.AreMatched.unique` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* At $x = x_\gamma$ both take the value $\chi(\det\gamma)\Psi(y_\gamma)$. At other $x$ both vanish by the first condition. $\square$

**Lemma (Translates).** If $\Phi$ and $\Psi$ are matched, $c \in \mathbb{C}$ and $g \in GL_n(R)$, then $x \mapsto c\,\chi(\det g)\,\Phi(x g)$ and $y \mapsto c\,\Psi(g^{-1} y)$ are matched.

Lean: `New.AreMatched.translate` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* The blocks move with $\gamma$: $x_\gamma\, k = x_{k^{-1}\gamma}$ and $k\, y_\gamma = y_{k\gamma}$. If $\Phi(x g) \neq 0$, then $x g = x_\gamma$ and $x = x_{g\gamma}$. If $\Psi(g^{-1} y) \neq 0$, then $g^{-1} y = y_\gamma$ and $y = y_{g\gamma}$. For the values, $x_\gamma g = x_{g^{-1}\gamma}$ and $g^{-1} y_\gamma = y_{g^{-1}\gamma}$, so
$$c\,\chi(\det g)\,\Phi(x_{g^{-1}\gamma}) = c\,\chi(\det g)\,\chi(\det g^{-1}\gamma)\,\Psi(y_{g^{-1}\gamma}) = \chi(\det\gamma)\cdot c\,\Psi(g^{-1}y_\gamma). \qquad \square$$

### Left inverses of blocks

**Lemma.** Let $k \in GL_n(R)$ and let $s$ be a $b \times n$ matrix with $s\, y_k = 1$. Let $f \colon N \to n$ be injective, and suppose that the columns $f$ of $s$ vanish. Then the columns $f$ of $x_k$ form a matrix with a left inverse.

Lean: `New.Exchange.hasLeftInv_submatrix_invLastRows` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Let $P = (s; x_k)$, the square matrix with the rows $s$ at $b$ and $x_k$ at $a$. Jacobi's identity gives $\det P \det k = \det(s y_k) = 1$, so $P$ is invertible. Read $P^{-1} P = 1$ at the rows and columns $f$. The rows $b$ of $P$ contribute $s_{t, f(j)} = 0$. So the columns $a$ of $P^{-1}$, in the rows $f$, form a left inverse of the columns $f$ of $x_k$. $\square$

**Lemma.** Let $e \colon b \sqcup a \simeq N \sqcup n$ and $k \in GL_{N \sqcup n}(R)$. If the rows $N$ of $y_k$ have a left inverse, then the columns $n$ of $x_k$ have a left inverse. If the rows $n$ of $y_k$ have a left inverse, then the columns $N$ of $x_k$ have a left inverse.

Lean: `New.Exchange.hasLeftInv_toCols_of_hasLeftInv_toRows` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Let $M$ be a left inverse of the rows $N$ of $y_k$. Then $s = (M\ 0)$ is a left inverse of $y_k$ whose columns $n$ vanish. Apply the previous lemma with $f$ the inclusion of $n$. The second case is the same with $s = (0\ M)$. $\square$

The ring $R$ is a *valuation pair* if any two elements $u$, $v$ are multiples of $(1 - \epsilon)u + \epsilon v$ for an idempotent $\epsilon$ ([congruence subgroups](/chapter/congruence-subgroups/), `New.IsValuationPair`). For such $R$, an $n \times b$ matrix is $y_k$ for some invertible $k$ exactly when it has a left inverse ([PartnerAlgebra.lean line 227](lean:Lib/General/LinearAlgebra/PartnerAlgebra.lean#L227), `New.IsValuationPair.exists_firstCols_iff` with $O = R$).

**Lemma.** Let $R$ be a valuation pair and $e \colon b \sqcup a \simeq N \sqcup n$. If the rows $N$ or the rows $n$ of an $(N \sqcup n) \times b$ matrix $y$ have a left inverse, then $y = y_\gamma$ for some $\gamma \in GL_{N \sqcup n}(R)$.

Lean: `New.Exchange.exists_eq_firstCols` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Extend the left inverse $M$ of a row block by $0$ to $(M\ 0)$ or $(0\ M)$. This is a left inverse of $y$. Over $O = R$ every matrix has integral entries, so $y$ is primitive. The cited equivalence gives $\gamma$. $\square$
