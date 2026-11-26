---
title: The square law after Fourier transform
lean:
  - Lib/General/Analysis/FiniteFourier.lean
  - New/Determinant/Chain/SquareLaw.lean
decls:
  - New.Exchange.IsPrimitiveMulChar
  - New.sum_addChar_trace_mul
  - New.Exchange.matrixFourier_matrixFourier
  - New.Exchange.matrixFourier_eq_inv_det_mul
  - New.Exchange.star_matrixFourier_det_mul
  - New.Exchange.exists_matrixFourier_eq_mul_inv_det
  - New.Exchange.matrixFourier_nextDatum_fromBlocks
  - New.Exchange.exists_sum_matrixFourier_nextDatum_eq
  - New.Exchange.SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The square law after Fourier transform

The law for the next datum compares a sum weighted by $p$ with a sum weighted by $\operatorname{nextDatum}(p)$. The chain of [the chain determinant](/chapter/chain-determinant/) also needs the same comparison for Fourier transforms of the weights. This section applies the law to a transform and computes the constant that appears. The constant is a Gauss sum of $\chi \circ \det$, and its modulus is known.

We keep the finite ring $R$ and the character $\chi$ of [Section 2](/chapter/seesaw-squares/#the-square-law). Let $\psi$ be an additive character of $R$. It is *primitive* if no multiple $t \mapsto \psi(r t)$ with $r \neq 0$ is trivial. The Fourier transform of a function $f$ on $N \times a$ matrices is the function
$$\hat f(\rho) = \sum_v f(v)\, \psi(\operatorname{tr}(\rho v))$$
on $a \times N$ matrices, with no normalizing factor ([the notation](/chapter/notation/#spaces-forms-lattices-and-normalizations), `New.Exchange.matrixFourier`). We write $\mathcal{F}f$ for $\hat f$ when $f$ is a long expression.

### Gauss sums of matrices

**Definition.** The multiplicative character $\chi$ is *primitive* if for every $a \neq 0$ there is $c \in R$ with $\chi(1 + ca) \neq 0$ and $\chi(1 + ca) \neq 1$.

Lean: `New.Exchange.IsPrimitiveMulChar` (Lib/General/Analysis/FiniteFourier.lean).

So for no $a \neq 0$ is $\chi$ trivial on the units congruent to $1$ modulo $a$.

**Lemma (Orthogonality).** If $\psi$ is primitive and $\rho$ is an $a \times N$ matrix, then $\sum_v \psi(\operatorname{tr}(\rho v))$ over all $N \times a$ matrices $v$ is the number of such matrices if $\rho = 0$, and $0$ otherwise.

Lean: `New.sum_addChar_trace_mul` (Lib/General/Analysis/FiniteFourier.lean).

*Proof.* $\operatorname{tr}(\rho v) = \sum_{i,j} \rho_{ji} v_{ij}$, so the sum is a product over the entries of $\sum_t \psi(\rho_{ji} t)$. If $\rho_{ji} = 0$ the factor is $|R|$. If $\rho_{ji} \neq 0$, then $t \mapsto \psi(\rho_{ji} t)$ is a nontrivial character of the additive group, and the factor is $0$. $\square$

**Lemma (Inversion).** If $\psi$ is primitive, then $\hat{\hat f}(y) = f(-y)\, |R^{a \times N}|$.

Lean: `New.Exchange.matrixFourier_matrixFourier` (Lib/General/Analysis/FiniteFourier.lean).

*Proof.* $\hat{\hat f}(y) = \sum_u \sum_v f(v)\, \psi(\operatorname{tr}(u v))\, \psi(\operatorname{tr}(y u)) = \sum_v f(v) \sum_u \psi(\operatorname{tr}((v + y) u))$. By orthogonality the inner sum is $0$ unless $v = -y$. $\square$

**Lemma.** Let $\chi$ be primitive, and let $S$ be a function on $a \times a$ matrices with $S(g d) = \chi(\det g)\, S(d)$ for all $g \in GL_a(R)$. Then $\hat S(y) = \chi^{-1}(\det y)\, \hat S(1)$ for every $y$. The character $\psi$ may be any.

Lean: `New.Exchange.matrixFourier_eq_inv_det_mul` (Lib/General/Analysis/FiniteFourier.lean).

*Proof.* Step 1. Substitute $d \mapsto g d$ in the sum: $\chi(\det g)\, \hat S(z g) = \hat S(z)$ for $g$ invertible.

Step 2. Let $z$ be not invertible. Over a finite ring, $z$ is then a zero divisor: there is $D \neq 0$ with $z D = 0$. Choose $i, j$ with $D_{ij} \neq 0$, and choose $c$ with $\chi(1 + c D_{ij}) \notin \{0, 1\}$. Let $v$ be the column $j$ of $D$, and put $g = 1 + c\, v\, e_i^{\mathsf{T}}$. Then $z g = z$, as $z v = 0$, and $\det g = 1 + c\, v_i = 1 + c D_{ij}$, which is a unit. Step 1 gives $\chi(1 + c D_{ij})\, \hat S(z) = \hat S(z)$, so $\hat S(z) = 0$. Since $\chi^{-1}(\det z) = 0$ too, the claim holds at $z$.

Step 3. For $y$ invertible, Step 1 with $z = y$ and $g = y^{-1}$ gives $\hat S(y) = \chi(\det y)^{-1}\, \hat S(1)$. $\square$

**Lemma.** Let $\psi$ and $\chi$ be primitive, and let $S$ be as in the previous lemma. Let $G = \mathcal{F}(\chi \circ \det)(1)$. Then $\bar G\, \hat S(1) = S(1)\, |R^{a \times a}|$.

Lean: `New.Exchange.star_matrixFourier_det_mul` (Lib/General/Analysis/FiniteFourier.lean).

*Proof.* Conjugation turns $\chi$ into $\chi^{-1}$ and $\psi(t)$ into $\psi(-t)$. So $\bar G\, \hat S(1)$ is the transform of $y \mapsto \chi^{-1}(\det y)\, \hat S(1)$ at $-1$. By the previous lemma this function is $\hat S$. By inversion, $\hat{\hat S}(-1) = S(1)\, |R^{a \times a}|$. $\square$

**Theorem (Gauss sums of matrices).** Let $\psi$ and $\chi$ be primitive. There is $G \in \mathbb{C}$ with $|G|^2 = |R|^{|a|^2}$ such that every $S$ with $S(g u) = \chi(\det g)\, S(u)$ for all $g \in GL_a(R)$ satisfies $\hat S(y) = G\, \chi^{-1}(\det y)\, S(1)$ for all $y$.

Lean: `New.Exchange.exists_matrixFourier_eq_mul_inv_det` (Lib/General/Analysis/FiniteFourier.lean).

*Proof.* Take $G = \mathcal{F}(\chi \circ \det)(1)$. The previous lemma with $S = \chi \circ \det$ gives $\bar G G = |R^{a \times a}| = |R|^{|a|^2}$, so $G \neq 0$. For general $S$ the previous lemma gives $\bar G\, \hat S(1) = S(1)\, \bar G G$, so $\hat S(1) = G\, S(1)$. Insert this in $\hat S(y) = \chi^{-1}(\det y)\, \hat S(1)$. $\square$

### The transform of the next datum

**Lemma.** Let $\psi$ be primitive and let $p$ be a function on $n \times a$ matrices. At an $(a \sqcup b) \times (n \sqcup b)$ block matrix,
$$\mathcal{F}(\operatorname{nextDatum} p)\begin{pmatrix} A & B \\ C & D \end{pmatrix} = \begin{cases} \hat p(-A)\, \psi(\operatorname{tr} D) & \text{if } C = 0, \\ 0 & \text{otherwise.} \end{cases}$$

Lean: `New.Exchange.matrixFourier_nextDatum_fromBlocks` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* By the lemma on $\operatorname{nextDatum}$ of Section 2, the transform is a sum over $\eta$ and $s$ of $p(-\eta)/|R^{n \times b}|$ times $\psi$ of the trace of
$$\begin{pmatrix} A & B \\ C & D \end{pmatrix}\begin{pmatrix} \eta & s \\ 0 & 1 \end{pmatrix} = \begin{pmatrix} A\eta & As + B \\ C\eta & Cs + D \end{pmatrix}.$$
The trace is $\operatorname{tr}(A\eta) + \operatorname{tr}(Cs) + \operatorname{tr}(D)$, and $\psi$ turns the sum into a product. The sum over $s$ of $\psi(\operatorname{tr}(Cs))$ is $|R^{n \times b}|$ if $C = 0$ and $0$ otherwise, by orthogonality. The sum over $\eta$ of $p(-\eta)\, \psi(\operatorname{tr}(A\eta))$ is $\hat p(-A)$, by the substitution $\eta \mapsto -\eta$. $\square$

**Proposition.** Let $\psi$ and $\chi$ be primitive, and let $N$, $M$, $T$ be finite index sets. There is $\gamma$ with $|\gamma|^2 = |R|^{|T|(|T| + 2|N|)}$ with this property. Let $L$ be a function on $(N \sqcup T) \times (N \sqcup M \sqcup T)$ matrices with $L(k x) = \chi(\det k)\, L(x)$ for all $k \in GL_{N \sqcup T}(R)$, and let $p$ be a function on $M \times N$ matrices. Let $\iota = (1; 0)$ be the inclusion matrix of $N$ in $N \sqcup T$. Then, with $x$ over the $(N \sqcup T) \times (M \sqcup T)$ matrices,
$$\sum_x \mathcal{F}(\overline{\operatorname{nextDatum} p})(x)\, L(\iota\ x) = \gamma \sum_x \operatorname{nextDatum}(\hat{\bar p})(x)\, L(\iota\ x).$$

Lean: `New.Exchange.exists_sum_matrixFourier_nextDatum_eq` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Let $G$ be the Gauss sum of the theorem for the index set $T$, and put $\gamma = G\, |R^{N \times T}|$. Then $|\gamma|^2 = |R|^{|T|^2} |R|^{2|N||T|}$. Put $q = \hat{\bar p}$ and $K(\eta, s, d) = L\bigl(\iota\ \ (\eta\ s; 0\ d)\bigr)$.

Step 1, the corner block. For $g \in GL_T(R)$ let $u = \operatorname{diag}(1, g) \in GL_{N \sqcup T}(R)$. Then $u\iota = \iota$, $u\,(\eta\ s; 0\ d) = (\eta\ s; 0\ g d)$ and $\det u = \det g$. So $K(\eta, s, g d) = \chi(\det g)\, K(\eta, s, d)$. The theorem on Gauss sums, at $y = 1$, gives $\sum_d K(\eta, s, d)\, \psi(\operatorname{tr} d) = G\, K(\eta, s, 1)$.

Step 2, the sum. Conjugation commutes with $\operatorname{nextDatum}$. By the previous lemma, $\mathcal{F}(\operatorname{nextDatum} \bar p)$ at $(\eta\ s; C\ d)$ is $q(-\eta)\, \psi(\operatorname{tr} d)$ if $C = 0$, and $0$ otherwise. So the left side is
$$\sum_s \sum_\eta q(-\eta) \sum_d K(\eta, s, d)\, \psi(\operatorname{tr} d) = G\, |R^{N \times T}| \sum_s \sum_\eta \frac{q(-\eta)}{|R^{N \times T}|}\, K(\eta, s, 1)$$
by Step 1. By the lemma on $\operatorname{nextDatum}$ of Section 2, the last double sum is $\sum_x \operatorname{nextDatum}(q)(x)\, L(\iota\ x)$. $\square$

### The law for transforms

**Theorem (Square law for transforms).** Let $\psi$ and $\chi$ be primitive, and let $N$, $T$ be finite index sets. There is $\gamma$ with $|\gamma|^2\, |R|^{|T|(|T| + 2|N|)} = 1$ with this property. Let $c \in \mathbb{C}$, let $L$ be a function on $(N \sqcup T) \times (N \sqcup (N \sqcup T) \sqcup T)$ matrices and $L'$ a function on $(N \sqcup (N \sqcup T) \sqcup T) \times (N \sqcup T)$ matrices. Suppose that $(L, L')$ satisfies the square law for $\chi$ and $\operatorname{swapFirstTwo}$, with $a = N \sqcup T$, $b = T$ and $n = N$, and with constant $c$. Then for every function $p$ on $(N \sqcup T) \times N$ matrices,
$$\sum_y \hat{\bar p}(y)\, L'(y; \iota) = \gamma\, c \sum_x \mathcal{F}(\overline{\operatorname{nextDatum} p})(x)\, L(\iota\ x),$$
with $y$ over the $N \times (N \sqcup T)$ matrices and $x$ over the $(N \sqcup T) \times ((N \sqcup T) \sqcup T)$ matrices.

Lean: `New.Exchange.SquareLaw.exists_sum_matrixFourier_eq_sum_nextDatum` (New/Determinant/Chain/SquareLaw.lean).

*Proof.* Let $\gamma_0$ be the constant of the proposition for $M = N \sqcup T$, and put $\gamma = \gamma_0^{-1}$. Since $|\gamma_0|^2 > 0$, $\gamma_0 \neq 0$, and $|\gamma|^2\, |R|^{|T|(|T| + 2|N|)} = 1$. Let $q = \hat{\bar p}$. The law for the next datum, applied to $q$, gives
$$|GL_{N \sqcup T}(R)| \sum_y q(y)\, L'(y; \iota) = c\, |GL_{N \sqcup T}(R)| \sum_x \operatorname{nextDatum}(q)(x)\, L(\iota\ x).$$
Both group orders are those of $GL_{N \sqcup T}(R)$, since $a = N \sqcup T$ and $n \sqcup b = N \sqcup T$. Cancel them. The proposition, applied with the first clause of the law, gives $\sum_x \operatorname{nextDatum}(q)(x)\, L(\iota\ x) = \gamma_0^{-1} \sum_x \mathcal{F}(\overline{\operatorname{nextDatum} p})(x)\, L(\iota\ x)$. $\square$

**Remark (Formalization).** The constant of the theorem is the inverse of the constant of the proposition. So the Lean statement gives its modulus in the form $|\gamma|^2 \cdot |R|^{|T|(|T| + 2|N|)} = 1$, and $\gamma \neq 0$ follows. The theorem says nothing about $c$. If $c = 0$, the right side is $0$ for every $p$. The nonvanishing of the constant of a square comes from elsewhere; see [Section 5](/chapter/seesaw-squares/#the-one-square-identity).
