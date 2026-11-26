---
title: Jet sizes, the direction amount and the main amount
lean:
  - New/Reduction/PrimeSums.lean
  - New/Reduction/Data/AdmissibleData.lean
decls:
  - New.Data.jetSize
  - New.Data.jetSize_mem_Icc
  - New.Data.directionAmount
  - New.Data.jetSize_sub_primeSum_mem_Icc
  - New.Data.directionAmount_mem_Icc
  - New.Data.mainAmount
  - New.Data.le_mainAmount
  - New.Data.mainAmount_nonneg
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Jet sizes, the direction amount and the main amount

This section defines the main amount, the leading term that the two bounds of the lattice argument share. It proves two bounds for it: $x^4 f a \leq \text{main amount}$, and so the main amount is nonnegative. The main inequality uses the second bound ([the main inequality and the end of the proof](/chapter/main-inequality/)). The section first defines the jet size and the direction amount, from which the main amount is made.

### The jet size

The data contain two distinct primes $p_0$ and $p_1$, and the *principal level* is $M = p_0 p_1$. The table of sizes gives $b^{20} \leq M \leq b^{22}$ (Lean: `New.Data.M_mem_Icc`). The field $E$ has the *period*

$$\Omega = e^{C_d} \cdot \frac{2\pi}{\mathrm{rd}_E},$$

where $\mathrm{rd}_E = |\operatorname{disc} E|^{1/[E : \mathbb{Q}]}$ is the root discriminant of $E$ and $C_d = \gamma - \operatorname{Re}(L'/L)(1, \chi_K)$ ([fields, places and twists](/chapter/fields-places-twists/)). The table of sizes gives $\Omega \leq 1$ (Lean: `New.Data.bigOmega_le_one`) and

$$20 \log b \leq \log(M/\Omega) \leq 23 \log b$$

([the data and its sizes](/chapter/data-and-sizes/); Lean: `New.Data.log_M_div_bigOmega_mem_Icc`).

**Definition (Jet size).** For an integer $j \geq 0$, the *jet size* is

$$s_\infty(j) = \log j! + j \log(M/\Omega).$$

Lean: `New.Data.jetSize` (New/Reduction/Data/AdmissibleData.lean).

The docstring of the source calls $s_\infty(j)$ "the size of a derivative of order $j$". [The archimedean size](/chapter/archimedean-size/) explains it. This chapter uses only the definition.

**Lemma (Size of the jet size).** For an integer $0 \leq y \leq a$,

$$20\, y \log b \leq s_\infty(y) \leq 25\, y \log b .$$

Lean: `New.Data.jetSize_mem_Icc` (New/Reduction/PrimeSums.lean).

*Proof.* For the lower bound, $\log y! \geq 0$ and $y \log(M/\Omega) \geq 20 y \log b$. For the upper bound, $y! \leq y^y \leq a^y$, and $a = xb \leq b^2$ by the scale inequalities. So $\log y! \leq 2y \log b$, and $y \log(M/\Omega) \leq 23 y \log b$. $\square$

### The direction amount

**Definition (Direction amount).** The *direction amount* is the sum over all $f$ places

$$\sum_{\sigma \in \Phi} \Bigl(s_\infty\bigl(\kappa(\sigma)\bigr) - s_{\mathrm{fin}}\bigl(\kappa(\sigma), \sigma\bigr)\Bigr).$$

Lean: `New.Data.directionAmount` (New/Reduction/Data/AdmissibleData.lean).

At the place $\sigma$ the term $s_\infty(\kappa(\sigma))$ is the size of a derivative of order $\kappa(\sigma)$, and $s_{\mathrm{fin}}(\kappa(\sigma), \sigma)$ is the divisibility that is guaranteed for it.

**Lemma (One direction).** For every place $\tau$,

$$\kappa(\tau) \log b \leq s_\infty\bigl(\kappa(\tau)\bigr) - s_{\mathrm{fin}}\bigl(\kappa(\tau), \tau\bigr) \leq 25\, \kappa(\tau) \log b .$$

Lean: `New.Data.jetSize_sub_primeSum_mem_Icc` (New/Reduction/PrimeSums.lean).

*Proof.* The weight satisfies $0 \leq \kappa(\tau) \leq b \leq a$. The lemma on the jet size gives $20 \kappa(\tau) \log b \leq s_\infty(\kappa(\tau)) \leq 25 \kappa(\tau) \log b$. The corollary of Section 2, with $y = \kappa(\tau)$, gives $0 \leq s_{\mathrm{fin}}(\kappa(\tau), \tau) \leq \kappa(\tau) \log b$. Subtract. $\square$

The lower bound has much room: it is $\kappa \log b$, and the proof gives $19 \kappa \log b$. The source keeps only what the next proposition needs.

**Proposition (Size of the direction amount).** The direction amount lies in the interval

$$\bigl[\, b \cdot \#\Phi_a,\ 25 f b \log b \,\bigr].$$

Lean: `New.Data.directionAmount_mem_Icc` (New/Reduction/PrimeSums.lean).

*Proof.* Upper bound: by the lemma, each term is at most $25 \kappa(\tau) \log b \leq 25 b \log b$, and there are $f$ terms. Lower bound: by the lemma, the direction amount is at least $\sum_{\tau \in \Phi} \kappa(\tau) \log b$. All terms are nonnegative, so this is at least the sum over $\Phi_b$, which is $\#\Phi_b \cdot b \log b$, since $\kappa = b$ on $\Phi_b$. The data give $\#\Phi_a = 3 l_0 2^s \leq \#\Phi_b \log b$ (Section 5 proves $\#\Phi_a = 3 l_0 2^s$). So the sum is at least $b \cdot \#\Phi_a$. $\square$

The lower bound uses the $b$-places only, through the condition $3 l_0 2^s \leq \#\Phi_b \log b$. Section 6 uses the same condition again.

### The main amount

**Definition (Main amount).** The *main amount* is

$$\text{main amount} = m\, k \cdot \text{direction amount} = m k \sum_{\sigma \in \Phi}\Bigl(s_\infty\bigl(\kappa(\sigma)\bigr) - s_{\mathrm{fin}}\bigl(\kappa(\sigma), \sigma\bigr)\Bigr),$$

where $m \in [\sqrt{x}, 2\sqrt{x}]$ is the number of theta lifts in a chain and $k = r + 1 - m$ is the rank of the source, with $r \in [x^5, 3x^5]$ the rank of the target.

Lean: `New.Data.mainAmount` (New/Reduction/PrimeSums.lean).

A chain has $m$ lifts, and each lift contributes $k$ copies of the direction amount. The main amount occurs in the lower bound of Theorem C for the volume of the lattice (Volume 11). It occurs in Theorem A as $\text{main amount} - m \cdot \mathrm{rem}$ ([Theorems A, B and C](/chapter/theorems-a-b-c/)). The main inequality compares the two bounds, and the main amount cancels.

**Proposition (Lower bound for the main amount).** $x^4 f a \leq \text{main amount}$.

Lean: `New.Data.le_mainAmount` (New/Reduction/PrimeSums.lean).

*Proof.* By the proposition on the direction amount and $\#\Phi_a = 3 l_0 2^s$,

$$\text{main amount} \geq m k \cdot b \cdot 3 l_0 2^s .$$

So it suffices to prove $x^4 f a \leq mk \cdot b \cdot 3 l_0 2^s$. Put $f = 3 l_0 2^s \cdot \varphi(q_0)$ and $a = xb$. The inequality becomes $x^5 \varphi(q_0) \leq mk$. The data give $m \geq \sqrt{x}$ and $r \geq x^5$. The table of sizes gives $100 m \leq k$ (Lean: `New.Data.hundred_mul_m_le_k`), so $r + 1 = k + m \leq 2k$ and $k \geq x^5/2$. So $mk \geq x^{11/2}/2$, and it suffices that $2\varphi(q_0) \leq \sqrt{x}$. This holds. The bound $\varphi(q_0) \leq q_0 \leq c$ holds for the constant $c$ of the parameters (Lean: `New.Data.le_constantBound`), and the scale inequalities give $10^{12} c \leq \log\log b$ and $(\log b)^{100} \leq x$. So $\varphi(q_0) \leq 10^{-14} \log x$, which is far below $\sqrt{x}/2$. $\square$

**Remark (Formalization).** The source proves the first step, $x^4 f a \leq mk \cdot b \cdot 3 l_0 2^s$, by its automation for sizes (`New.Data.le_of_hasLogBound`), which compares the logarithms of the two sides through the scale inequalities. The proof above is the same comparison by hand. The automation is the subject of a remark in [the data and its sizes](/chapter/data-and-sizes/).

**Corollary.** The main amount is nonnegative.

Lean: `New.Data.mainAmount_nonneg` (New/Reduction/PrimeSums.lean).

*Proof.* $x^4 f a \geq 0$, and the proposition applies. $\square$

The main amount is at least $x^4 f a$. The right side $f a (\log b)^5$ of the main inequality is smaller by a factor of about $x^4$. So an error of relative size $x^{-4}$ in the main amount would already be too large. This is one reason why the source proves an exact identity for $\mathrm{rem}$.
