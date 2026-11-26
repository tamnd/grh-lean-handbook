---
title: Sparse theta kernels
lean:
  - New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean
decls:
  - New.Fock.norm_sq_le_norm_sq_add_norm_mulVec_add_sq
  - New.Fock.norm_fockInner_realHeisenbergOp_le
  - New.Rows.firstMinimum_mul_le_hom
  - New.Rows.norm_pairHomInf_le_mul
  - New.Rows.le_norm_realCoord
  - New.Rows.tsum_inv_norm_realCoord_pow_le
  - New.Rows.dataInner_traceChar
  - New.Rows.modKernel_expect_traceChar
  - New.Rows.exists_norm_modKernel_sub_fockInner_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Sparse theta kernels

A theta kernel is a sum over the rational points of a lattice. If the lattice has no short vectors, the term of $0$ dominates, and the kernel is close to one Fock matrix coefficient. This section proves this with explicit constants. The Fock model, the Heisenberg action $\varrho$ and the Weil action $\omega$ are in [the Weil representation](/chapter/weil-representation/). The spaces with a point and their first minima are in [reduction theory](/chapter/reduction-theory/).

### Decay of Heisenberg coefficients

Let $\iota$ be a nonempty finite set, $\varepsilon$ signs on $\iota$ and $\sigma \in U(\varepsilon)$. Write $|y|$ for the Euclidean norm on $\mathbb{C}^\iota$ and $\|\sigma\|$ for the operator norm. Note $\|\sigma\| \geq 1$.

**Lemma (A triangle bound).** For $x, y \in \mathbb{C}^\iota$, $|y|^2 \leq 2\|\sigma\|^2\bigl(|x|^2 + |\sigma x + y|^2\bigr)$.

Lean: `New.Fock.norm_sq_le_norm_sq_add_norm_mulVec_add_sq` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* $|y| \leq |\sigma x + y| + |\sigma x| \leq \|\sigma\|(|\sigma x + y| + |x|)$, as $\|\sigma\| \geq 1$. Square and use $(p+q)^2 \leq 2(p^2 + q^2)$. $\square$

**Theorem (Decay of Fock coefficients).** Let $P$ be a polynomial on $\mathbb{C}^\iota$ with $P(cx) = c^dP(x)$ for real $c$, let $v = v_P$ be its Fock vector, and let $A, n \in \mathbb{N}$ with $d + |\iota| \leq A$. For $y \neq 0$,
$$|\langle v, \varrho(y)\omega(\sigma)v\rangle| \leq \|\sigma\|^{|\iota| + 2n}\,\mathrm{Re}\langle v, v\rangle\,(4(A+n))^n\,|y|^{-2n}.$$

Lean: `New.Fock.norm_fockInner_realHeisenbergOp_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Write $\omega(\sigma)v$ as an integral of translated vacua and move $\varrho(y)$ to the left. By the reproducing property of the vacuum, the coefficient is at most $\|\sigma\|^{|\iota|}\int|v(x)|\,|v(\sigma x + y)|\,dx$; the factor $\|\sigma\|^{|\iota|}$ bounds the multiplier. Put $c = \sqrt{n/A + 1}$. The Fock vector is $v(x) = P(x)e^{-|x|^2/2}$ up to the normalisation. Let $G(x) = |v_c(c^{-1}x)|^2$, where $v_c$ is the Fock vector of $P$ dilated by $c$. By homogeneity, $|v(x)|^2 = G(x)\,e^{-(1 - c^{-2})|x|^2}$, and $1 - c^{-2} = n/(n+A)$. Undoing the dilation costs $c^{2d}$ from $P$ and the Jacobian $c^{2|\iota|}$, so $\int G \leq c^{2(d + |\iota|)}\int|v|^2 \leq e^n\int|v|^2$, as $(1 + n/A)^A \leq e^n$. By the triangle bound, $|x|$ and $|\sigma x + y|$ are not both small against $|y|/\|\sigma\|$. So the two Gaussian factors multiply to at most $K = \bigl(4(A+n)\|\sigma\|^2/(e|y|^2)\bigr)^n$, using $t^ne^{-t\,n/(n+A)} \leq (n+A)^n e^{-n}$. Then $2ab \leq a^2 + b^2$ gives
$$|v(x)|\,|v(\sigma x+y)| \leq \tfrac{K}{2}\bigl(G(x) + G(\sigma x + y)\bigr).$$
The map $x \mapsto \sigma x + y$ preserves the measure, so both terms have integral $\int G$. Collect: $K e^n\int|v|^2 = \|\sigma\|^{2n}(4(A+n))^n|y|^{-2n}\mathrm{Re}\langle v, v\rangle$. $\square$

### Short vectors

For a space $S$ with a point, $\lambda(S)$ is the minimum of $1$ and the length of a shortest nonzero vector of its lattice. Let $f$ be the number of infinite places of $E$.

**Theorem (First minimum of $\mathrm{Hom}$).** Let $N \neq 0$ be a natural number in the different of $E$. Then
$$\frac{\lambda(S)\lambda(T)}{C\,\#n'\,\#n} \leq \lambda(\mathrm{Hom}(S, T)),\qquad C = 6N(f\#n)^2.$$

Lean: `New.Rows.firstMinimum_mul_le_hom` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Both minima are at most $1$ and the denominator is at least $1$, so the left side is at most $1$. Let $z$ be a nonzero lattice vector of $\mathrm{Hom}(S, T)$, read as a matrix. Since $N$ lies in the different, the lattice of $S$ contains a basis $Y$ of $E^n$ whose vectors have length at most $C/\lambda(S)$ (`New.Space.exists_short_basis`, in [reduction theory](/chapter/reduction-theory/)). As $z \neq 0$, some $zY_k$ is a nonzero lattice vector of $T$, so $\lambda(T) \leq |zY_k| \leq \#n'\,\#n\,|z|\,C/\lambda(S)$. This is the claim. $\square$

**Lemma (Norm of the pair).** For real points $u$ of $U(S)$ and $u'$ of $U(T)$, the point of $U(\mathrm{Hom}(S, T))$ they define has operator norm at most $\|u\|\,\|u'\|$, where $\|u\|$ is the largest operator norm of $u$ at a place.

Lean: `New.Rows.norm_pairHomInf_le_mul` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* The block diagonal map is a star homomorphism of $C^*$-algebras, so it does not increase norms. Each block is a Kronecker product, with norm the product of the norms. $\square$

Let $\Phi_w$ be the chosen embedding at $w$, and $j \in E$ the imaginary element fixed by the Weil data. The *Fock coordinates* of an adelic vector are its components at the infinite places, times $\sqrt{2\pi\,\mathrm{Im}\,\Phi_w(j)}$.

**Lemma (No short vectors).** Let $c \neq 0$ and $m > 0$ with $m|\Phi_w c| \leq \sqrt{2\pi\,\mathrm{Im}\,\Phi_w j}\,\lambda(V)$ for all $w$. If $cy$ is in the lattice and $y \neq 0$, then the Fock coordinates of $y$ have norm at least $m$.

Lean: `New.Rows.le_norm_realCoord` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* The vector $cy$ is a nonzero lattice vector, so its length is at least $\lambda(V)$. Divide by $c$ at each place and use the hypothesis. $\square$

**Lemma (A lattice sum).** Under the same hypotheses, let $q > \#(\text{places} \times \iota)$. Then, over the nonzero $y$ with $cy$ in the lattice, $|y| \geq m$, the sum $\sum_y |y|^{-2q}$ converges, and $\sum_y|y|^{-2q} \leq (5/m)^{2q}$. Here $|y|$ is the norm of the Fock coordinates.

Lean: `New.Rows.tsum_inv_norm_realCoord_pow_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* The first claim is the last lemma. The same lemma applied to $y - z$ shows that the points are $m$-separated. The real dimension is $2\#(\text{places}\times\iota) \leq 2q - 2$. A packing bound for $m$-separated sets at distance $\geq m$ from $0$ in such a dimension gives convergence and the bound $(5/m)^{2q}$. $\square$

### The sparse kernel

For a matrix $t$ modulo $\mathfrak{m}$ let $\Psi_t$ be the additive character $x \mapsto \psi(\mathrm{tr}(tx))$ of the matrices modulo $\mathfrak{m}$ (`traceChar`).

**Lemma (Pairing of character data).** The pairing of the datum $v \otimes \Psi_t \otimes \mathrm{vac}$ with the Heisenberg translate by $z$ of $w \otimes \Psi_t \otimes \mathrm{vac}$ is the lift of $\Psi_t$ at the finite coordinates of $z$, times $\langle v, \varrho(z_\infty)w\rangle$, times the vacuum at the finite part.

Lean: `New.Rows.dataInner_traceChar` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* The finite part of the datum of $\Psi_t$ is the vacuum translated by a finite vector. Moving the finite translate of $z$ past it costs the phase of the Heisenberg bicharacter, which is the lift of $\Psi_t$. The archimedean and finite parts pair separately. $\square$

**Lemma (A mean over characters).** Let $\Psi = \mathbb{E}_t\,\overline{\mathrm{modKernel}(\Psi_t)(g, h)}\,\Psi_t$. Then the kernel of $\Psi$ at $(gu, hu')$ is the mean over $t$ of $\theta(\omega(p)(w\otimes\Psi_t\otimes\mathrm{vac}))\,\overline{\theta(\omega(p)(v\otimes\Psi_t\otimes\mathrm{vac}))}$, with $p$ the point of $\mathrm{Hom}(S, T)$ given by $(g, h)$ and $w = \Omega(u, u')v$.

Lean: `New.Rows.modKernel_expect_traceChar` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* The kernel is linear in the datum. The real points act only on the Fock vector, through the real Weil representation $\Omega$ twisted by the weights of $a$ and $b$. $\square$

**Theorem (Sparse theta kernels).** Let $a$, $b$ have weights $\gamma$, $\gamma'$ and tame parts $\psi$, $\psi'$. Let $c \neq 0$ with $c\alpha z$ integral for every integral $z \equiv 0$ modulo $\mathfrak{m}$. Let $m > 0$ with $m|\Phi_wc| \leq \sqrt{2\pi\,\mathrm{Im}\,\Phi_wj}\,\lambda\bigl(\mathrm{Hom}(S g, T h)\bigr)$ for all $w$, and $q > \#(\text{places}\times n'\times n)$. Let $Q$ be homogeneous of real degree $d$, with Fock vector $v$. Then some $\Psi$ satisfies, for all real points $u$, $u'$,
$$\bigl|\mathrm{modKernel}(S, T, a, b, \mathfrak{m}, \Psi, Q)(gu, hu') - \langle v, \Omega(u, u')v\rangle\bigr| \leq \|u'\|^{3q}\Bigl(\frac{100(d+2q)}{m^2}\Bigr)^q|\langle v, v\rangle|\,\|u\|^{3q}.$$

Lean: `New.Rows.exists_norm_modKernel_sub_fockInner_le` (New/OneLift/ComparisonOperator/ThetaKernelEstimates.lean).

*Proof.* Take $\Psi$ as in the lemma on a mean over characters. Each product $\theta(\cdot)\overline{\theta(\cdot)}$ is a sum over rational vectors $y$ of pairings with Heisenberg translates. By the lemma on pairing and orthogonality of the characters $\Psi_t$, the mean of the terms of $y$ is $0$ unless the finite coordinates of $y$ are integral and $\equiv 0$ modulo $\mathfrak{m}$. Then it is $\langle v, \varrho(y_\infty)w\rangle$ times a phase of modulus $1$. By the hypothesis on $c$, a contributing $y$ has $cy$ in the lattice. The term $y = 0$ is $\langle v, w\rangle = \langle v, \Omega(u, u')v\rangle$. For the other terms apply the decay theorem with $\sigma$ the point of $(u, u')$, $A = d + \dim$ and $n = q$, where $\dim = \#(\text{places}\times n'\times n) < q$. Each term is at most $\|\sigma\|^{\dim + 2q}\,|\langle v, v\rangle|\,(4(d + \dim + q))^q\,|y|^{-2q}$. The lemma on the norm of the pair gives $\|\sigma\|^{\dim + 2q} \leq (\|u\|\|u'\|)^{3q}$, as both norms are at least $1$ (`New.Rows.one_le_maxOpNorm`). The lattice sum gives $\sum|y|^{-2q} \leq (5/m)^{2q}$. Finally $4(d + \dim + q)\cdot 25 \leq 100(d + 2q)$. $\square$

**Remark (Formalization).** The datum $\Psi$ is given by an existence statement, but it is explicit: the weighted mean of the characters $\Psi_t$. The theorem is used in the second part with $q$ and $m$ fixed by the sizes of [the data](/chapter/data-and-sizes/).
