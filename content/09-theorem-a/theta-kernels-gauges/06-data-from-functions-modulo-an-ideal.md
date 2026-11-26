---
title: Data from functions modulo an ideal
lean:
  - New/UpperBound/Kernels/ThetaLiftGauge.lean
decls:
  - New.Parameters.absNorm_span_natCast_eq_pow_numInfPlaces
  - New.Modulus.card_residueRing_le
  - New.Parameters.smul_schrodingerOp_mem_standardData
  - New.Parameters.vacuumScale_pow_smul_vacuumDatum
  - New.Parameters.smul_vacuumDatum_mem_standardData
  - New.Parameters.isAdmissibleCombination_vacuumDatum_of_sum_le
  - New.Parameters.isAdmissibleCombination_vacuumDatum
  - New.Parameters.isVacuumCombination_vacuumDatum
  - New.Parameters.isAdmissibleCombination_vacuumDatum_indicator
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Data from functions modulo an ideal

The kernels of the argument do not use arbitrary data. Their data come from functions $\Psi$ on matrices modulo a modulus $\mathfrak{m}$ of $E$. At the places that divide $\mathfrak{m}$ the datum is $\Psi$, and at the other finite places it is the vacuum. This section proves two facts about such a datum. First, an explicit integer multiple of it is standard at every prime $l$ prime to a given $q$, so Section 5 applies at $l$. Second, it is a vacuum combination with an explicit size, so Section 4 applies at every conjugate.

### Setting

A modulus $\mathfrak{m}$ is an ideal of $\mathcal{O}_E$ prime to its conjugate; $\mathcal{O}_E/\mathfrak{m}$ is its residue ring. For a function $\Psi$ on $(\mathcal{O}_E/\mathfrak{m})^n$, the operator $\Psi\otimes$ of [the seesaw identity, part 1](/chapter/seesaw-identity-1/) puts $\Psi$ at the places of $\mathfrak{m}$. Its lift to finite adelic vectors reduces the components at the places of $\mathfrak{m}$ modulo $\mathfrak{m}$ and is $0$ where they are not integral. Three facts from that chapter are used:

- the ring $\mathcal{O}_{(q)}$ of complex numbers $z$ with $|\iota z|_l \le 1$ for every prime $l$ coprime to $q$ and every ring map $\iota : \mathbb{C} \to \mathbb{C}_l$;
- the group $\mathrm{Tr}(q, a)$ of finite adelic vectors $y$ with $a y$ integral at every finite place not above $q$;
- the theorem on values of $\Psi\otimes$: if $gq \in \mathfrak{m}$, $\Psi$ has values in $\mathcal{O}_{(q)}$, and $\mathrm{proj}_{\mathfrak{m}}(u) = v$, then $(\Psi\otimes)(u)$ is an admissible combination of the $\varrho^\pm(y)v$, $y \in \mathrm{Tr}(q, \bar g)$, with denominator $N(g)^{n}$ away from $q$; under a proposition $p$ that gives $\sum_x |\sigma(\Psi(x))| \le B$ for all $\sigma$, it has size $B$ under $p$.

An admissible combination with denominator $D$ away from $q$ gives a membership: if all the $v(y)$ lie in a module $M$ over $\{z : |\iota_l z|_l \le 1\}$, for a prime $l$ coprime to $q$, then $D$ times the combination lies in $M$. This is also in [the seesaw identity, part 1](/chapter/seesaw-identity-1/).

The integral vacuum is fixed by the integral translations, so $\mathrm{proj}_{\mathfrak{m}}(\theta^\circ) = \theta^\circ$.

### Norms and residue rings

**Lemma (Norm of an integer).** For a natural number $k$, the ideal $k\mathcal{O}_E$ has absolute norm $k^{2f}$, where $f$ is the number of infinite places of $E$.

Lean: `New.Parameters.absNorm_span_natCast_eq_pow_numInfPlaces` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The norm of $k\mathcal{O}_E$ is $k^{[E:\mathbb{Q}]}$, since $\mathcal{O}_E/k\mathcal{O}_E \cong (\mathbb{Z}/k)^{[E:\mathbb{Q}]}$. The field $E$ is a CM field, so all its infinite places are complex and $[E:\mathbb{Q}] = 2f$. $\square$

**Lemma (Size of the residue ring).** If $k > 0$ is a natural number in $\mathfrak{m}$, then $|\mathcal{O}_E/\mathfrak{m}| \le k^{2f}$.

Lean: `New.Modulus.card_residueRing_le` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The size of $\mathcal{O}_E/\mathfrak{m}$ is the norm of $\mathfrak{m}$. Since $k \in \mathfrak{m}$, the ideal $\mathfrak{m}$ divides $k\mathcal{O}_E$, so its norm divides $k^{2f}$ by the lemma. A divisor of a positive integer is at most that integer. $\square$

### Integrality

**Theorem (A multiple of $\Psi\otimes\theta^\circ$ is standard).** Let $V$ be a hermitian space over $E$ of rank $n$, and let $N, q$ be natural numbers with $Nq \in \mathfrak{m}$. Let $\Psi$ be a function on $(\mathcal{O}_E/\mathfrak{m})^n$ with values in $\mathcal{O}_{(q)}$, and let $l$ be a prime that does not divide $q$. Then
$$N^{2f|n|}\,(\Psi\otimes)(\theta^\circ) \in \mathrm{SD}_l(V, N).$$

Lean: `New.Parameters.smul_schrodingerOp_mem_standardData` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The prime $l$ does not divide $q$, so $l$ is coprime to $q$. Apply the theorem on values of $\Psi\otimes$ with $g = N$, $u = v = \theta^\circ$, and the proposition "false", so no size is needed. Then $(\Psi\otimes)(\theta^\circ)$ is an admissible combination of the $\varrho^\pm(y)\theta^\circ$, $y \in \mathrm{Tr}(q, \bar N)$, with denominator $N(N\mathcal{O}_E)^{|n|}$ away from $q$. By the lemma on norms, this denominator is $(N^{2f})^{|n|} = N^{2f|n|}$.

Each translate $\varrho^\pm(y)\theta^\circ$ with $y \in \mathrm{Tr}(q, \bar N)$ is a generator of $\mathrm{SD}_l(V, N)$. Indeed, a place $w$ above $l$ does not contain $q$, because $l$ and $q$ are coprime. So $N y$ is integral at $w$; here $\bar N = N$, since $N$ is rational. The module $\mathrm{SD}_l(V, N)$ is a module over $\{z : |\iota_l z|_l \le 1\}$. By the membership for admissible combinations, $N^{2f|n|}(\Psi\otimes)(\theta^\circ)$ lies in it. $\square$

Now let $V = H = \mathrm{Hom}(V_n, V_{n'})$. For a function $\Psi$ on the $n' \times n$ matrices modulo $\mathfrak{m}$, the *vacuum datum* $\mathrm{vd}_{\mathfrak{m}}(\Psi)$ is $(\Psi\otimes)(\mathrm{vac})$, with $\Psi$ read as a function on vectors indexed by $n' \times n$. It lies in the finite part $H^{\mathrm{fin}}$. This is `New.vacuumDatum` (Lib/Weil/DualPair/KernelLaws.lean), the datum also used in [the Rallis inner product formula](/chapter/rallis-inner-product/).

**Lemma (The scaled vacuum datum).** $c_s^{\,|n'||n|}\,\mathrm{vd}_{\mathfrak{m}}(\Psi) = (\Psi\otimes)(\theta^\circ)$, where $\theta^\circ = c_s^{\,|n'||n|}\,\mathrm{vac}$ is the integral vacuum of $H$.

Lean: `New.Parameters.vacuumScale_pow_smul_vacuumDatum` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The operator $\Psi\otimes$ is linear. $\square$

**Corollary (Vacuum data are standard up to a multiple).** Let $qN \in \mathfrak{m}$, let $\Psi$ have values in $\mathcal{O}_{(q)}$, and let $l$ be a prime coprime to $q$. Then
$$N^{2f|n'||n|}\,c_s^{\,|n'||n|}\,\mathrm{vd}_{\mathfrak{m}}(\Psi) \in \mathrm{SD}_l(H, N).$$

Lean: `New.Parameters.smul_vacuumDatum_mem_standardData` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* By the lemma the datum is $N^{2f|n'||n|}(\Psi\otimes)(\theta^\circ)$ on $H$, which has rank $|n'||n|$. Apply the theorem. $\square$

With Section 5 this gives the integrality of a kernel at $l$. Let $N \ne 0$, $d_0 = N^{2f|n'||n|}$, $F = c_s^{\,|n'||n|}\mathrm{vd}_{\mathfrak{m}}(\Psi)$, and $|\iota_l c|_l \le 1$. If $d_0 (N d)^{\mathrm{boxes}(\kappa, |n'|)}$ divides $M$, then $MF \in \mathrm{raises}(1, 1, 1)$ at $l$ for the theta kernel of scale $c\,t_0$, by the corollary on integer multiples of Section 5.

**Remark (Formalization).** The prime $l$ carries a chosen ring map $\iota_l : \mathbb{C} \to \mathbb{C}_l$ (the instance `New.PadicPlace`), and $\mathrm{SD}_l$ is defined with it. The hypothesis $\Psi(x) \in \mathcal{O}_{(q)}$ is for all ring maps, so it holds for the chosen one. The number $c_s$ is the chosen nonzero scale `New.Parameters.vacuumScale` of [the integral vacuum and tight frames](/chapter/integral-vacuum/), named through `choose`. The statements hold for it because only its stated properties are used, and here only its definition enters.

### Size

**Proposition (Vacuum data as combinations).** Let $\Psi$ be a function on the $n' \times n$ matrices modulo $\mathfrak{m}$, and let $B$ be real with
$$\sum_{x} |\sigma(\Psi(x))| \le B \qquad\text{for every ring automorphism } \sigma \text{ of } \mathbb{C}.$$
Then $c_s^{\,|n'||n|}\,\mathrm{vd}_{\mathfrak{m}}(\Psi)$ is an admissible combination of the vectors $\varrho^\pm(y)\theta^\circ$, over all finite adelic vectors $y$, with denominator $0$ away from $0$ and size $B$ under "true".

Lean: `New.Parameters.isAdmissibleCombination_vacuumDatum_of_sum_le` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* Take $q = 0$ and $g = 0$. Then $gq = 0 \in \mathfrak{m}$. Every value of $\Psi$ lies in $\mathcal{O}_{(0)}$, because no prime is coprime to $0$: $\gcd(l, 0) = l \ne 1$. So the condition is empty. The integral vacuum has $\mathrm{proj}_{\mathfrak{m}}(\theta^\circ) = \theta^\circ$. By the lemma on the scaled vacuum datum and the theorem on values of $\Psi\otimes$, the datum is an admissible combination of the $\varrho^\pm(y)\theta^\circ$, $y \in \mathrm{Tr}(0, 0)$, with denominator $N(0)^{|n'||n|}$ away from $0$ and size $B$ under "true". Each $\varrho^\pm(y)\theta^\circ$ is an admissible combination of itself, over all $y$, of size $1$ and any denominator, in particular $1$. By substitution the datum is an admissible combination over all $y$, with any denominator divisible by $N(0)^{|n'||n|}\cdot 1$, for example $0$, and size $B\cdot|1| = B$. $\square$

**Remark (Formalization).** The choice $q = 0$ is a device. The ring $\mathcal{O}_{(0)}$ is all of $\mathbb{C}$, and "denominator $0$ away from $0$" says nothing: the condition on denominators is a condition at the primes coprime to $0$, and there are none. So the proposition states only the decomposition into translates and the size. This is all that Section 4 needs. Integrality is the separate corollary above.

**Corollary (Bounded values).** If $|\sigma(\Psi(x))| \le M$ for every ring automorphism $\sigma$ of $\mathbb{C}$ and every matrix $x$ modulo $\mathfrak{m}$, then the conclusion of the proposition holds with size $|\mathcal{O}_E/\mathfrak{m}|^{|n'||n|}\,M$. In the terms of Section 4, $c_s^{\,|n'||n|}\,\mathrm{vd}_{\mathfrak{m}}(\Psi)$ is a vacuum combination of size $|\mathcal{O}_E/\mathfrak{m}|^{|n'||n|}\,M$.

Lean: `New.Parameters.isAdmissibleCombination_vacuumDatum`, `New.Parameters.isVacuumCombination_vacuumDatum` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* The sum over $x$ has $|\mathcal{O}_E/\mathfrak{m}|^{|n'||n|}$ terms, each at most $M$. Apply the proposition. An admissible combination of the $\varrho^\pm(y)\theta^\circ$ of size $B$ under "true" is a vacuum combination of size $B$, by Section 4. $\square$

**Corollary (Indicators).** Let $y_0$ be a matrix modulo $\mathfrak{m}$ and $\delta_{y_0}$ its indicator. Then $c_s^{\,|n'||n|}\,\mathrm{vd}_{\mathfrak{m}}(\delta_{y_0})$ is an admissible combination as in the proposition, of size $1$.

Lean: `New.Parameters.isAdmissibleCombination_vacuumDatum_indicator` (New/UpperBound/Kernels/ThetaLiftGauge.lean).

*Proof.* In the sum $\sum_x |\sigma(\delta_{y_0}(x))|$ only $x = y_0$ contributes, with $|\sigma(1)| = 1$. So the sum is $1$. Apply the proposition with $B = 1$. $\square$

**Example.** For $\Psi = 1$, the constant function, the bounded-values corollary gives size $|\mathcal{O}_E/\mathfrak{m}|^{|n'||n|}$. The indicator corollary gives size $1$ for each of the $|\mathcal{O}_E/\mathfrak{m}|^{|n'||n|}$ indicators, and $1 = \sum_{y_0}\delta_{y_0}$. So the two bounds agree here. If $k > 0$ is an integer in $\mathfrak{m}$, the lemma on residue rings bounds the size by $k^{2f|n'||n|}M$.

### Where this is used

In Volume 11 the size statements enter [the comparison operator](/chapter/comparison-operator-1/) through the bound of Section 4, and the integrality statement enters [the Hecke values](/chapter/hecke-values/) and [the deep-level Poincaré series](/chapter/deep-level-poincare/) at each prime $l$ prime to $q$.
