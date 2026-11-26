---
title: Tight frames
lean:
  - Lib/General/LinearAlgebra/PolarDecomposition.lean
  - New/Derivatives/Vacuum/TightFrames.lean
  - New/Derivatives/Vacuum/ShortVectors.lean
decls:
  - New.Parameters.finiteImage_mem_iff
  - New.finiteImage_add_mem
  - New.finiteImage_mul_mem
  - New.Parameters.finiteImage_coe_mem
  - New.Parameters.finiteImage_galOfPlace_mem
  - New.Parameters.coe_trace_eq_sum
  - New.Parameters.exists_coe_eq_trace_of_isIntegral
  - New.Parameters.sum_mul_conj_mem_quadInt
  - New.Parameters.exists_natCast_eq_sum_norm_sq
  - New.Parameters.eq_of_phi_eq_of_isPrimitiveRoot
  - New.Parameters.isTightFrame_pow
  - New.Parameters.isTightFrame_zeta_pow
  - New.IsTightFrame.mul_left
  - New.IsTightFrame.repeat_vectors
  - New.IsTightFrame.sumElim
  - New.IsTightFrame.join_family
  - New.IsTightFrame.replace_pairs
  - New.Parameters.orbit
  - New.Parameters.isTightFrame_orbit
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Tight frames

A tight frame of length $M$ is a family of vectors of $\mathfrak{a}_0$ whose linear forms add up $M$ times the standard hermitian form (Section 1). This section first studies the lattice $\mathfrak{a}_0$ and the pairing $\langle x, y\rangle$ on it. The pairing takes values in $\mathcal{O}_K$, and this is what makes the theta functions of Section 4 integral. It then gives the first frame, the powers of $\zeta$, and the operations that make new frames from old ones. Section 7 uses all of them.

### The lattice of the idele

Recall that $\alpha$ is $1/P'(\zeta)$ at the primes of $E$ that divide $\beta = (1+\sqrt{-d})/2$, and $1$ at the other primes. So $y \in \mathfrak{a}_0$ means that $\alpha^{-1} y$ is integral at every finite place.

**Lemma.** An element $y \in E$ lies in $\mathfrak{a}_0$ if and only if, for every finite place $w$ of $E$, $|P'(\zeta)\, y|_w \le 1$ when $\beta \in w$ and $|y|_w \le 1$ when $\beta \notin w$.

Lean: `New.Parameters.finiteImage_mem_iff` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The component of $\alpha^{-1}$ at $w$ is $P'(\zeta)$ if $\beta \in w$ and $1$ otherwise. $\square$

**Lemma.** The set $\mathfrak{a}_0$ is closed under addition and under multiplication by $\mathcal{O}_E$. It contains $\mathcal{O}_E$. It is stable under $\mathrm{Gal}(E/K)$.

Lean: `New.finiteImage_add_mem`, `New.finiteImage_mul_mem` (New/Derivatives/Vacuum/ShortVectors.lean); `New.Parameters.finiteImage_coe_mem` (New/Derivatives/Vacuum/TightFrames.lean); `New.Parameters.finiteImage_galOfPlace_mem` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The integral adeles $\hat{\mathcal{O}}$ form a ring that contains $\mathcal{O}_E$. This gives the first two claims. For the third, $\alpha^{-1}$ is integral, since $P'(\zeta)$ is an algebraic integer. For the last, let $g \in \mathrm{Gal}(E/K)$. The valuation of $g(y)$ at $w$ is the valuation of $y$ at $g^{-1}w$. The element $\beta$ lies in $K$, so $g$ fixes it, and $\beta \in w$ if and only if $\beta \in g^{-1} w$. The different is stable under $g$, so $P'(\zeta)$ has the same valuation at $w$ and at $g^{-1}w$. The criterion of the previous lemma at $g^{-1}w$ for $y$ is the criterion at $w$ for $g(y)$. $\square$

### The pairing is integral

**Lemma.** For $z \in E$, the trace of $z$ from $E$ to $K$, seen in $\mathbb{C}$, is $\sum_\tau \tau(z)$.

Lean: `New.Parameters.coe_trace_eq_sum` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The trace is the sum of $g(z)$ over $g \in \mathrm{Gal}(E/K)$. Apply the embedding of the trivial place, which is the identity on $K$, and use the bijection of the places with $\mathrm{Gal}(E/K)$. $\square$

**Lemma.** If $z P'(\zeta)$ is an algebraic integer, then $\mathrm{tr}_{E/K}(z) \in \mathcal{O}_K$.

Lean: `New.Parameters.exists_coe_eq_trace_of_isIntegral` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* The element $P'(\zeta)$ generates the different $\mathfrak{D}_{E/K}$ ([the field E at the primes](/chapter/field-at-primes/)). So $z \in (P'(\zeta))^{-1} = \mathfrak{D}_{E/K}^{-1}$. The trace maps the inverse different into $\mathcal{O}_K$, by the definition of the different. $\square$

**Proposition (Integral pairing).** For $x, y \in \mathfrak{a}_0$,
$$\langle x, y \rangle = \sum_\tau \tau(x)\, \overline{\tau(y)} \in \mathcal{O}_K .$$

Lean: `New.Parameters.sum_mul_conj_mem_quadInt` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* As finite adeles,
$$x\, \bar y\, P'(\zeta) = \bigl(\alpha \bar\alpha P'(\zeta)\bigr) \cdot (\alpha^{-1} x) \cdot \overline{(\alpha^{-1} y)} .$$
The first factor is a unit at every finite place ([the field E at the primes](/chapter/field-at-primes/)). The other two are integral by hypothesis, since complex conjugation preserves $\hat{\mathcal{O}}$. So $x \bar y P'(\zeta)$ is an algebraic integer. By the last lemma, $\mathrm{tr}_{E/K}(x \bar y) \in \mathcal{O}_K$. Each $\tau$ is a CM embedding, so $\tau(\bar y) = \overline{\tau(y)}$, and $\mathrm{tr}_{E/K}(x \bar y) = \langle x, y \rangle$ by the trace lemma. $\square$

The proposition says that $\mathfrak{a}_0$ is a hermitian $\mathcal{O}_K$-lattice for the form $\langle\ ,\ \rangle$, and that it is contained in its own dual. In fact $\mathfrak{a}_0 \bar{\mathfrak{a}}_0 = \mathfrak{D}_{E/K}^{-1}$, so $\mathfrak{a}_0$ is unimodular, but only the inclusion is used.

**Corollary.** For $y \in \mathfrak{a}_0$ there is $\nu \in \mathbb{N}$ with $\nu = \sum_\tau |\tau(y)|^2$.

Lean: `New.Parameters.exists_natCast_eq_sum_norm_sq` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The number $\langle y, y \rangle$ lies in $\mathcal{O}_K$ and is real. A real element of $\mathcal{O}_K$ lies in $\mathbb{Z}$, since $d \equiv 7 \pmod 8$ makes $\mathcal{O}_K = \mathbb{Z}[\beta]$ and $\beta$ has imaginary part $\sqrt d/2 \ne 0$. A sum of squares is not negative. $\square$

### The powers of a root of unity

**Lemma.** If $z$ is a primitive $q_1$-th root of unity in $E$ and $\sigma(z) = \tau(z)$ for two places $\sigma$, $\tau$, then $\sigma = \tau$.

Lean: `New.Parameters.eq_of_phi_eq_of_isPrimitiveRoot` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* Both embeddings are $K$-linear, and $z$ generates $E$ over $K$, so they agree on $E$. Distinct places have distinct embeddings in the CM type. $\square$

**Theorem (Powers of a root of unity).** Let $z \in E$ be a primitive $q_1$-th root of unity. The powers $z^i$, $0 \le i < q_1$, each with multiplicity $1$, form a tight frame of length $q_1$.

Lean: `New.Parameters.isTightFrame_pow` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* Each $z^i$ lies in $\mathcal{O}_E \subseteq \mathfrak{a}_0$. Put $u = \sigma(z)\overline{\tau(z)}$. As $|\tau(z)| = 1$, $\overline{\tau(z)} = \tau(z)^{-1}$, and
$$\sum_{i < q_1} \sigma(z^i)\, \overline{\tau(z^i)} = \sum_{i < q_1} u^i .$$
If $\sigma = \tau$ then $u = 1$ and the sum is $q_1$. Otherwise $u \ne 1$ by the last lemma, and $u^{q_1} = 1$, so the geometric sum $(u^{q_1} - 1)/(u - 1)$ is $0$. $\square$

**Corollary.** For $k \in \mathbb{N}$, the powers $\zeta^i$, $0 \le i < q_1$, each with multiplicity $k$, form a tight frame of length $k q_1$.

Lean: `New.Parameters.isTightFrame_zeta_pow` (New/Derivatives/Vacuum/TightFrames.lean).

*Proof.* Apply the next lemma with the factor $k$ to the theorem with $z = \zeta$. $\square$

### Operations on frames

**Lemma (Operations).** Let $(w_i)$ with multiplicities $(m_i)$ be a tight frame of length $M$, and $(w'_j)$ with multiplicities $(m'_j)$ one of length $M'$.

1. For $k \in \mathbb{N}$, $(w_i)$ with multiplicities $(k m_i)$ is a tight frame of length $kM$.
2. The family in which each $w_i$ is repeated $m_i$ times, with all multiplicities $1$, is a tight frame of length $M$.
3. The disjoint union of the two families, with multiplicities $m_i$ and $m'_j$, is a tight frame of length $M + M'$.
4. If $v_i$ is a tight frame of length $L_i$ with multiplicities $1$ for each $i$ in a finite set, the disjoint union of all $v_i$ is a tight frame of length $\sum_i L_i$.

Lean: `New.IsTightFrame.mul_left` (New/Derivatives/Vacuum/TightFrames.lean); `New.IsTightFrame.repeat_vectors` (Lib/General/LinearAlgebra/PolarDecomposition.lean); `New.IsTightFrame.sumElim`, `New.IsTightFrame.join_family` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The defining sum is linear in the multiplicities, and it is additive in the family. Membership in $\mathfrak{a}_0$ is a condition on each vector. $\square$

The next operation is the one that changes the length by a number that is not a multiple of $q_1$.

**Lemma (Replacing pairs).** Let $(w_i)_{i \in I}$, with multiplicities $1$, be a tight frame of length $M$. Let $(a_j, b_j)_{j \in J}$ be disjoint pairs of members of $I$, and suppose that there is $t \in \mathbb{Z}$ with
$$\sum_{j \in J} \Bigl( \sigma(w_{a_j})\, \overline{\tau(w_{b_j})} + \sigma(w_{b_j})\, \overline{\tau(w_{a_j})} \Bigr) = t\, \delta_{\sigma\tau} \qquad \text{for all } \sigma, \tau .$$
Then there is $L \in \mathbb{N}$ with $L = M + t$, and the members of $I$ in no pair, together with the sums $w_{a_j} + w_{b_j}$, form a tight frame of length $L$ with multiplicities $1$.

Lean: `New.IsTightFrame.replace_pairs` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* For the new family $v$,
$$\sigma(x + y)\overline{\tau(x+y)} = \sigma(x)\overline{\tau(x)} + \sigma(y)\overline{\tau(y)} + \sigma(x)\overline{\tau(y)} + \sigma(y)\overline{\tau(x)} .$$
Summing over the unpaired members and the pairs gives the old sum, which is $M\delta_{\sigma\tau}$, plus the cross terms, which give $t\,\delta_{\sigma\tau}$. So $\sum_v \sigma(v)\overline{\tau(v)} = (M + t)\delta_{\sigma\tau}$. For $\sigma = \tau$ the left side is $\sum_v |\sigma(v)|^2 \ge 0$, so $M + t \ge 0$ and $L = M + t$ is a natural number. The sums lie in $\mathfrak{a}_0$, since $\mathfrak{a}_0$ is closed under addition. $\square$

**Example.** Here is a frame in $\mathbb{C}^2$ that shows the shape of the conditions, without the lattice. Let $\omega = e^{2\pi i/3}$, and take the vectors $(1, 1)$, $(\omega, \bar\omega)$ and $(\omega^2, \bar\omega^2)$, read as $(\sigma(w), \tau(w))$. The diagonal sums are $3$. The off-diagonal sum is $1 + \omega^2 + \omega^4 = 0$. So the three vectors are a tight frame of length $3$. Replace the pair $(1,1)$, $(\omega, \bar\omega)$ by its sum $(1 + \omega, 1 + \bar\omega) = (-\bar\omega, -\omega)$. The cross terms are $\bar\omega + \omega = -1$ at both diagonal entries and $\omega + \omega = 2\omega$ off the diagonal. They are not a multiple of the identity, and the new family $(-\bar\omega, -\omega)$, $(\omega^2, \bar\omega^2)$ is not a tight frame: its diagonal sums are $2$, but its off-diagonal sum is $\bar\omega^2 + \omega^4 = 2\omega$. In Section 7 the pairs are chosen so that the cross terms are $t$ times the identity.

### Orbits

**Definition (Orbit).** For $y \in E$, the orbit of $y$ is the family $\zeta^i g(y)$, indexed by $0 \le i < q_1$ and $g \in \mathrm{Gal}(E/K)$.

Lean: `New.Parameters.orbit` (New/Derivatives/Vacuum/ShortVectors.lean).

**Proposition (Orbits are frames).** Let $y \in \mathfrak{a}_0$ and $\nu = \sum_\tau |\tau(y)|^2 \in \mathbb{N}$. The orbit of $y$, with multiplicities $1$, is a tight frame of length $q_1 \nu$.

Lean: `New.Parameters.isTightFrame_orbit` (New/Derivatives/Vacuum/ShortVectors.lean).

*Proof.* The vectors $\zeta^i g(y)$ lie in $\mathfrak{a}_0$, by the stability lemmas. Identify the places with $\mathrm{Gal}(E/K)$, so that $\sigma(g(y))$ is the embedding of the place $\sigma g$ applied to $y$. The sum over $(i, g)$ splits as
$$\Bigl(\sum_{i < q_1} \sigma(\zeta^i)\, \overline{\tau(\zeta^i)}\Bigr) \cdot \sum_g (\sigma g)(y)\, \overline{(\tau g)(y)} .$$
The first factor is $q_1 \delta_{\sigma\tau}$ by the theorem on powers. For $\sigma = \tau$ the second factor is $\sum_g |(\tau g)(y)|^2 = \nu$, since $g \mapsto \tau g$ is a bijection. $\square$

The length of an orbit is a multiple of $q_1$, and so is the length of the frame of powers. Sums of such frames have lengths in $q_1\mathbb{N}$. Section 7 needs a length prime to $q_1$, and gets it from the replacement of pairs.
