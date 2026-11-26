---
title: Ribet's method for tied rows
lean:
  - New/Congruences/FirstOrder/RibetMethod.lean
decls:
  - New.Selmer.mul_aeval_eq_zero_of_adjugate
  - New.Selmer.exists_ribet_polynomial
  - New.Selmer.traceIdeal
  - New.Selmer.mem_traceIdeal
  - New.Selmer.trace_mul_mem_of_mem_span
  - New.Selmer.trace_mul_aeval_apply
  - New.Selmer.map_mem_span_range
  - New.Selmer.map_mul_eq_zero_of_blocks
  - New.Selmer.det_comp_map_eq_mul_prod
  - New.Selmer.exists_ribet_element_of_tied_rows
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Ribet's method for tied rows

This section proves Ribet's method in the form that the chapter uses. The input is a square matrix $B$ over an algebra $\Lambda$ whose rows give relations modulo an ideal $\mathfrak{a}$. The output is a polynomial $P$ with $P(0) = \det B$ such that $P(\rho_0)$ multiplies a left ideal into $\mathfrak{a}$. When $\mathfrak{a}$ is an ideal of traces, the trace of $\rho_1 P(\rho_0)$ is the Ribet element.

The notation is that of [Amitsur and Cayley-Hamilton](/chapter/ribet-elements/#amitsur-and-cayley-hamilton). For a vector $y \in \Lambda^N$, write $I = \sum_i \Lambda y_i$ for the left ideal spanned by its entries.

### The polynomial kills the vector

The first lemma is the heart of the method. Let $\Lambda[X]$ act on a ring $Q$ through a ring map $\pi : \Lambda \to Q$, with $\Lambda$ acting by left multiplication and $X$ acting by right multiplication with $\pi(\rho_0)$. The two actions commute, since left and right multiplications commute. So the action is well defined.

**Lemma (The adjugate kills the vector).** Let $\pi : \Lambda \to Q$ be a ring map, $y \in \Lambda^N$, $\rho_0 \in \Lambda$, and $B$, $B_1$ square matrices over $\Lambda$. Suppose that $\pi((By)_i) = \pi((B_1 y)_i\, \rho_0)$ for all $i$. Let $P \in R[X]$ and $B'$ over $\Lambda[X]$ satisfy: $\pi$ of each coefficient of each entry of $B'(B - X B_1)$ is $\pi$ of the same coefficient of $P \cdot 1$. Then $\pi(y_i\, P(\rho_0)) = 0$ for all $i$.

Lean: `New.Selmer.mul_aeval_eq_zero_of_adjugate` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* The action of $c \in \Lambda[X]$ on $Q$ depends only on the images $\pi(c_m)$ of its coefficients, since $c \cdot q = \sum_m \pi(c_m)\, q\, \pi(\rho_0)^m$. By induction on $P$, the polynomial $P$ with coefficients mapped to $\Lambda$ acts on $\pi(r)$ as $\pi(r P(\rho_0))$. For a constant this is the commutation of $R$ with $\Lambda$, and a factor $X$ multiplies by $\pi(\rho_0)$ on the right.

Write $B_X = B - X B_1$. For each row $l$,
$$\sum_j (B_X)_{lj} \cdot \pi(y_j) = \pi((By)_l) - \pi((B_1 y)_l\, \rho_0) = 0 .$$
Now compute
$$\pi(y_i P(\rho_0)) = \sum_j (P \cdot 1)_{ij} \cdot \pi(y_j) = \sum_j (B' B_X)_{ij} \cdot \pi(y_j) = \sum_k B'_{ik} \cdot \Big(\sum_j (B_X)_{kj} \cdot \pi(y_j)\Big) = 0 .$$
The second equality uses that the action sees only $\pi$ of the coefficients. $\square$

### Ribet's polynomial

**Theorem (Ribet's method).** Let $\sigma$ be nonempty, and let $\rho : \Lambda \to M_\sigma(L)$ be a map of $R$-algebras such that $\Lambda$ is spanned over $R$ by elements whose characteristic polynomials under $\rho$ have coefficients in the image of $R$. Let $\mathfrak{a}$ be a two-sided ideal of $\Lambda$ that contains the kernel of $\rho$. Let $y \in \Lambda^N$, $\rho_0 \in \Lambda$, and let $B$ be a square matrix over $\Lambda$ such that each entry of $By$ has the form $a + z\rho_0$ with $a \in \mathfrak{a}$ and $z \in I$. Then there is $P \in R[X]$ with:

1. $P(0)$ maps to the determinant of the block matrix with blocks $\rho(B_{ij})$;
2. $z\,P(\rho_0) \in \mathfrak{a}$ for every $z \in I$;
3. for every $\rho_1 \in \Lambda$, the trace of $\rho(\rho_1 P(\rho_0))$ lies in the image of $R$;
4. for $\rho_1 \in \Lambda$ and $\delta \in R$, if some $z \in I$ has $\rho(z) = \delta \cdot 1$, then $\delta \operatorname{tr}\rho(\rho_1 P(\rho_0)) = \operatorname{tr} \rho(a)$ for some $a \in \mathfrak{a}$.

Lean: `New.Selmer.exists_ribet_polynomial` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* By Amitsur's theorem, every $\rho(w)$ has its characteristic polynomial over $R$. Each $z_i \in I$ is $\sum_j (B_1)_{ij}\, y_j$ for some row of coefficients. So $(By)_i = a_i + (B_1 y)_i\, \rho_0$ with $a_i \in \mathfrak{a}$. Put $B_X = B - X B_1$, a matrix over $\Lambda[X]$. The adjugate lemma over $\Lambda[X]$ gives $P$ and $B'$, with $P(0)$ equal to the determinant of the blocks of $B_X(0) = B$. This is claim 1.

Let $\pi : \Lambda \to \Lambda/\mathfrak{a}$ be the quotient map. If $\rho(w) = \rho(w')$, then $w - w'$ lies in the kernel of $\rho$, hence in $\mathfrak{a}$, and $\pi(w) = \pi(w')$. So the identity $B'B_X = P$ after $\rho$ gives the same identity after $\pi$. Also $\pi((By)_i) = \pi((B_1 y)_i \rho_0)$, since $a_i \in \mathfrak{a}$. The lemma on the adjugate gives $y_i P(\rho_0) \in \mathfrak{a}$ for each $i$. Every $z \in I$ is a sum $\sum c_i y_i$, and $\mathfrak{a}$ is a left ideal, so $z P(\rho_0) \in \mathfrak{a}$. This is claim 2.

For claim 3, the trace of a $\sigma \times \sigma$ matrix is minus the coefficient of $X^{|\sigma| - 1}$ in its characteristic polynomial. By Amitsur's theorem this coefficient lies in the image of $R$.

For claim 4, let $z_0 \in I$ with $\rho(z_0) = \delta \cdot 1$. By claim 2, $z_0 P(\rho_0) \in \mathfrak{a}$, and since $\mathfrak{a}$ is two-sided, $a = \rho_1 z_0 P(\rho_0) \in \mathfrak{a}$. Then $\rho(a) = \rho(\rho_1)\,\delta\,\rho(P(\rho_0)) = \delta\, \rho(\rho_1 P(\rho_0))$, and the traces agree. $\square$

**Remark (Formalization).** The proof chooses the elements $a_i$ and the rows of $B_1$ with `choose`. The polynomial $P$ depends on this choice. The four claims hold for every choice, and later results use only the claims.

### The trace ideal

**Definition (Trace ideal).** For an $R$-submodule $\mathcal{J}$ of $L$, the trace ideal of $\rho$ is the set of $w \in \Lambda$ with $\operatorname{tr}\rho(ws) \in \mathcal{J}$ for every $s \in \Lambda$.

Lean: `New.Selmer.traceIdeal` (New/Congruences/FirstOrder/RibetMethod.lean).

It is a two-sided ideal. It is closed under sums and negatives, since the trace is additive. If $w$ is in it, then $w w'$ is in it, since $\operatorname{tr}\rho(w w' s) = \operatorname{tr}\rho(w (w' s))$. And $w' w$ is in it, since the trace is cyclic: $\operatorname{tr}\rho(w' w s) = \operatorname{tr}\rho(w s w')$.

**Lemma.** An element $w$ lies in the trace ideal if and only if $\operatorname{tr}\rho(ws) \in \mathcal{J}$ for all $s \in \Lambda$.

Lean: `New.Selmer.mem_traceIdeal` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* This is the definition. $\square$

For a family $u_x$, $x \in Y$, of representations of $O[G]$ and $\rho : S[G] \to M_\sigma(Y \to L)$ as in [the lemma on one representation for the family](/chapter/ribet-elements/#amitsur-and-cayley-hamilton), the hypotheses of Ribet's method are stated over $O[G]$, with group elements only. The next lemma moves them to $S[G]$.

**Lemma (Traces from group elements).** Let $\mathcal{J}$ be an $S$-submodule of $Y \to L$. Let $r$ lie in the left ideal of $O[G]$ spanned by the $w$ such that, for every $g \in G$, the function $x \mapsto \operatorname{tr}(u_x(w)\, u_x(g))$ lies in $\mathcal{J}$. Then $\operatorname{tr}\rho(b\, \kappa(r)) \in \mathcal{J}$ for every $b \in S[G]$.

Lean: `New.Selmer.trace_mul_mem_of_mem_span` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Use induction on $r$ in the span, for all $b$ at once. For a generator $w$ and $b = g$, the trace of $\rho(g\,\kappa(w))$ at $x$ is $\operatorname{tr}(u_x(g) u_x(w)) = \operatorname{tr}(u_x(w) u_x(g))$, which is in $\mathcal{J}$. Sums in $b$ and multiples by $S$ stay in $\mathcal{J}$, since $\mathcal{J}$ is an $S$-module. For $r = s r'$ with $s \in O[G]$, apply the induction hypothesis to $b\, \kappa(s)$. Sums in $r$ are clear. $\square$

**Lemma.** A ring map $f : A \to A'$ sends the left ideal spanned by the $y_i$ into the left ideal spanned by the $f(y_i)$.

Lean: `New.Selmer.map_mem_span_range` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Write $w = \sum c_i y_i$. Then $f(w) = \sum f(c_i) f(y_i)$. $\square$

### The value on the reducible points

At the points $x$ of a set $\mathcal{X}$, the representation $u_x$ is a sum of a block and characters. Fix a bijection $r \sqcup \{0, \dots, t-1\} \cong \sigma$. For $x \in \mathcal{X}$ suppose that $u_x(w)$ is, after this reindexing, the block diagonal matrix with blocks $\psi_x(w)$ and $\eta_0(w), \dots, \eta_{t-1}(w)$. Here $\psi_x$ is a representation by $r \times r$ matrices and the $\eta_e$ are characters $O[G] \to O$.

**Lemma (Determinants of block sums).** Let $\chi(c)$ be the reindexed block sum of $\psi(c)$ and the scalars $\eta_e(c)$, for $c$ in a ring $A$. For a square matrix $M$ over $A$,
$$\det\big(\text{blocks } \chi(M_{ij})\big) = \det\big(\text{blocks } \psi(M_{ij})\big) \cdot \prod_e \det\big(\eta_e(M_{ij})\big) .$$

Lean: `New.Selmer.det_comp_map_eq_mul_prod` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Reorder the index set $N \times \sigma$ as $(N \times r) \sqcup (N \times \{0, \dots, t-1\})$. The block matrix becomes block diagonal, with the blocks of $\psi(M)$ in one corner and, for each $e$, the matrix $\eta_e(M)$. Reordering rows and columns by the same bijection does not change the determinant. $\square$

**Lemma (A product that vanishes).** Suppose $\psi(\rho_1) = 0$, $\eta_e(\rho_1) = 0$ for $e \neq 0$, $\eta_0(\rho_1) = \mu_0$, and $\eta_0(\rho_0) = 0$. Then $\chi(\rho_1 \rho_0) = 0$.

Lean: `New.Selmer.map_mul_eq_zero_of_blocks` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* On the block, $\psi(\rho_1\rho_0) = 0 \cdot \psi(\rho_0) = 0$. On $\eta_e$ with $e \neq 0$, $\eta_e(\rho_1) = 0$. On $\eta_0$, $\eta_0(\rho_0) = 0$. $\square$

**Lemma.** Let $\rho_0, \rho_1 \in S[G]$, $P \in S[X]$ and $x \in Y$, and suppose that every entry of $\rho(\rho_1\rho_0)$ vanishes at $x$. Then $\operatorname{tr}\rho(\rho_1 P(\rho_0))(x) = P(0)(x) \cdot \operatorname{tr}\rho(\rho_1)(x)$.

Lean: `New.Selmer.trace_mul_aeval_apply` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Write $P = X \operatorname{div}_X P + P(0)$. Then $\rho_1 P(\rho_0) = \rho_1\rho_0\, (\operatorname{div}_X P)(\rho_0) + P(0)\rho_1$. The trace of the first term at $x$ is a sum of products with a factor $\rho(\rho_1\rho_0)(x) = 0$. $\square$

### Ribet's element for a matrix of tied rows

**Theorem (Ribet's element for tied rows).** Let $u_x : O[G] \to M_\sigma(O)$, $x \in Y$, be maps of $O$-algebras, and let $S$ be an algebra of functions $Y \to L$ that contains the constants from $O$ and the coefficients of the characteristic polynomials of the $u_x(g)$, as functions of $x$. Let $\mathcal{J}$ be an $S$-module of functions $Y \to L$. Let $\mathfrak{a}_0$ be the left ideal of $O[G]$ spanned by the $w$ with $x \mapsto \operatorname{tr}(u_x(w) u_x(g))$ in $\mathcal{J}$ for all $g$. Let $y \in O[G]^N$, let $I$ be the left ideal spanned by $y$, and let $B$ be a square matrix over $O[G]$ of *tied rows*: each entry of $By$ lies in $\mathfrak{a}_0 + I \rho_0$. Suppose that for $x \in \mathcal{X}$, $u_x$ is the block sum of $\psi_x$ and the characters $\eta_e$, that $\psi_x(\rho_1) = 0$, that $\eta_e(\rho_1)$ is $\mu_0$ for $e = 0$ and $0$ otherwise, and that $\eta_0(\rho_0) = 0$. Then there is $f \in S$ with:

1. $f \cdot (x \mapsto \det u_x(w)) \in \mathcal{J}$ for every $w \in I$;
2. for $x \in \mathcal{X}$, $f(x) = \mu_0 \det\big(\text{blocks } \psi_x(B_{ij})\big) \prod_e \det\big(\eta_e(B_{ij})\big)$.

Lean: `New.Selmer.exists_ribet_element_of_tied_rows` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Let $\iota : O[G] \to S[G]$ be the map along $\kappa$, and let $\rho$ be the representation of the family. Let $\mathfrak{a}$ be the trace ideal of $\rho$ for $\mathcal{J}$. For $a \in \mathfrak{a}_0$ and $s \in S[G]$, $\operatorname{tr}\rho(\iota(a) s) = \operatorname{tr}\rho(s\,\iota(a)) \in \mathcal{J}$ by the lemma on traces from group elements. So $\iota(\mathfrak{a}_0) \subseteq \mathfrak{a}$, and the matrix $\iota(B)$ has tied rows for $\iota(y)$, $\mathfrak{a}$ and $\iota(\rho_0)$. The kernel of $\rho$ lies in $\mathfrak{a}$, since the trace of $0$ is $0$. By the lemma on one representation, all characteristic polynomials of $\rho$ are over $S$, so they span. Ribet's method over $R = S$ gives $P$. Let $f \in S$ be the trace of $\rho(\iota(\rho_1) P(\iota\rho_0))$, by claim 3.

For claim 1, let $w \in I$. Cayley and Hamilton for the family give $D \in S$, the function $x \mapsto \det u_x(w)$, and $v$ with $\rho(v\,\iota(w)) = D \cdot 1$. The element $v\,\iota(w)$ lies in the left ideal spanned by $\iota(y)$. Claim 4 of Ribet's method gives $b \in \mathfrak{a}$ with $D f = \operatorname{tr}\rho(b) = \operatorname{tr}\rho(b \cdot 1) \in \mathcal{J}$.

For claim 2, let $x \in \mathcal{X}$. The lemma on a product that vanishes gives $u_x(\rho_1\rho_0) = 0$, so every entry of $\rho(\iota\rho_1\, \iota\rho_0)$ vanishes at $x$. The last lemma gives $f(x) = P(0)(x) \operatorname{tr} u_x(\rho_1)$. By claim 1 of Ribet's method, $P(0)(x)$ is the determinant of the blocks $u_x(B_{ij})$. The lemma on block sums splits it into the determinant for $\psi_x$ and the product over the $\eta_e$. Finally $\operatorname{tr} u_x(\rho_1) = \operatorname{tr}\psi_x(\rho_1) + \sum_e \eta_e(\rho_1) = \mu_0$. $\square$

**Example (The smallest case).** Take $N$ one point and $y = (1)$, so that $I = O[G]$ and every row is tied as soon as its entry lies in $\mathfrak{a}_0 + O[G]\rho_0$. Suppose $\mathcal{J}$ contains the functions $x \mapsto p \operatorname{tr} u_x(g)$ for an element $p \in O$, as it does in the application. Then $p \in \mathfrak{a}_0$, and $B = (p)$ is a matrix of tied rows. If $r$ is empty, so that $u_x$ is a sum of $t$ characters on $\mathcal{X}$, the theorem gives $f$ with $f \det u_x(w) \in \mathcal{J}$ for all $w$ and $f(x) = \mu_0\, p^t$ on $\mathcal{X}$. This is the trivial Ribet element. Its value has valuation $t\,v(p) + v(\mu_0)$ and carries no information. The rest of the chapter finds matrices of tied rows whose determinants have a much smaller valuation.
