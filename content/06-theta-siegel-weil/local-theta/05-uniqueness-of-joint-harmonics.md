---
title: Uniqueness of joint harmonics
lean:
  - Lib/DiscreteSeries/Theta/FockJointHarmonics.lean
  - Lib/DiscreteSeries/Theta/FockDualPair.lean
decls:
  - New.Fischer.inner_X_mul
  - New.FockDualPair.fockLaplacian
  - New.FockDualPair.IsLaplaceHarmonic
  - New.FockDualPair.IsPreJointHarmonic
  - New.FockDualPair.IsTermwiseHarmonic.isLaplaceHarmonic
  - New.FockDualPair.IsJointHighest.isPreJointHarmonic
  - New.FockDualPair.IsPreJointHarmonic.sub_smul
  - New.DiscreteSeries.polarisation_one_eq_of_lt
  - New.DiscreteSeries.inner_polarisation_eq_zero
  - New.DiscreteSeries.polarisation_eq_zero_of_isCompactPrimitive
  - New.DiscreteSeries.polarisation_self_eq_smul_of_isCompactPrimitive
  - New.FockDualPair.matchingPoint
  - New.DiscreteSeries.IsEigenDirection
  - New.DiscreteSeries.exists_not_isEigenDirection
  - New.IsMatch.lt_or_exists_isMatchedPair
  - New.IsMatch.isEigenDirection_of_polarisation
  - New.IsMatch.isEigenDirection_of_swap_polarisation
  - New.IsMatch.eval_matchingPoint_ne_zero
  - New.IsMatch.unique
  - New.IsJointHarmonic.exists_eq_smul_of_row_weight
  - New.IsJointHarmonic.exists_eq_smul_of_column_weight
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Uniqueness of joint harmonics

This section proves that two joint harmonics for one pair of matching parameters are proportional. The source proves this in a class that is wider than joint harmonics, the *pre-joint harmonics*, because Howe's argument in Section 7 needs it there. The proof has two steps. First, the conditions on a pre-joint harmonic make it an eigenvector of many polarisations. Second, a pre-joint harmonic does not vanish at one point, the 0-1 matrix of the matching.

In the textbook, uniqueness is a part of the multiplicity one statement of Howe duality for $(GL_n, GL_{n'})$ on polynomials (Howe, *Transcending classical invariant theory*, J. Amer. Math. Soc. 2 (1989)). The source gives a direct argument. The docstring of the main theorem says that it "proves the case of the multiplicity one part of Howe's (GL, GL)-duality that is used".

### The Fischer inner product

The *Fischer inner product* on complex polynomials is $\langle P, Q\rangle = [\bar P, Q]$, where $[P, Q] = P(\partial)Q(0)$ is the Fock pairing (`New.fockPairing`, in Lib/GLn/SchurModule/Basic.lean) and $\bar P$ has the conjugate coefficients. The monomials are orthogonal, and $\langle X^\alpha, X^\alpha\rangle = \alpha!$.

**Lemma.** For the Fischer inner product, multiplication by a variable $X_b$ is adjoint to the partial derivative $\partial_b$:
$$\langle X_b P, Q\rangle = \langle P, \partial_b Q\rangle, \qquad \langle P, X_b Q\rangle = \langle \partial_b P, Q\rangle.$$

Lean: `New.Fischer.inner_X_mul` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

*Proof.* Both sides are sesquilinear, so it suffices to take monomials. For monomials it is the identity $\langle X^{\alpha + e_b}, X^{\beta}\rangle = \langle X^\alpha, \partial_b X^\beta\rangle$, which follows from $\langle X^\alpha, X^\alpha\rangle = \alpha!$. $\square$

### Laplacians and pre-joint harmonics

**Definition (Laplacian).** For rows $a$, $b$ the *Laplacian* is the sum of the operators $\omega(E_{(a,c)(b,c)})$ of the Fock model over the columns $c$ where the variable $(a, c)$ has sign $-1$. For $\varepsilon_a \neq \varepsilon_b$ it is $-\sum_c \partial_{ac}\partial_{bc}$ over those columns. A polynomial is *Laplace harmonic* if all Laplacians with $\varepsilon_a \neq \varepsilon_b$ kill it.

Lean: `New.FockDualPair.fockLaplacian` (Lib/DiscreteSeries/Theta/FockDualPair.lean). The second notion is `New.FockDualPair.IsLaplaceHarmonic`.

**Lemma.** A termwise harmonic polynomial is Laplace harmonic.

Lean: `New.FockDualPair.IsTermwiseHarmonic.isLaplaceHarmonic` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Each term $\partial_{ac}\partial_{bc}\Phi$ of the Laplacian is $0$. $\square$

**Definition (Pre-joint harmonic).** A polynomial $\Phi$ is a *pre-joint harmonic* for $l$, $l'$ if the following hold.
1. $\Phi \neq 0$.
2. The compact raising operators of the column action, in the order of $l'$, kill $\Phi$.
3. The Laplacians of the rows kill $\Phi$.
4. $\Phi$ is $K$-highest of weight $\Lambda$ for the row action, where $\Lambda$ is the lowest $K$-type of $l$.
5. The Laplacians of the columns kill $\Phi$.

Lean: `New.FockDualPair.IsPreJointHarmonic` (Lib/DiscreteSeries/Theta/FockDualPair.lean).

The weight of $\Phi$ for the column action is not fixed.

**Lemma.** Let $\Phi$ be jointly highest of weights $\Lambda$, $\nu'$, where $\Lambda$ is the lowest $K$-type of $l$ and $\nu'$ is any weight. Then $\Phi$ is a pre-joint harmonic.

Lean: `New.FockDualPair.IsJointHighest.isPreJointHarmonic` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* The termwise conditions give the Laplace conditions by the last lemma. The other conditions are parts of the definition. $\square$

**Lemma.** Let $P$, $Q$ be pre-joint harmonics and $c$ a scalar. If $P - cQ \neq 0$, then $P - cQ$ is a pre-joint harmonic.

Lean: `New.FockDualPair.IsPreJointHarmonic.sub_smul` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Conditions 2 to 5 are linear. $\square$

### Polarisations of a pre-joint harmonic

Recall the polarisation $D^s_{ab}$ of Section 4 and the formula $\rho(E_{ab}) = D^{+}_{ab} - D^{-}_{ba} + \delta_{ab}v(\varepsilon_a)$ for rows of equal sign.

**Lemma.** Let $P$ be compact primitive for the row action and $l$, let $\varepsilon_a = \varepsilon_b$ and $l_b < l_a$. Then $D^{+}_{ab}P = D^{-}_{ba}P$.

Lean: `New.DiscreteSeries.polarisation_one_eq_of_lt` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Here $a \neq b$, and $0 = \rho(E_{ab})P = D^{+}_{ab}P - D^{-}_{ba}P$. $\square$

**Theorem.** Let the entries of $l$ be distinct. Let $P$ be compact primitive for the row action and $l$, and let the Laplacians of the columns kill $P$. Then for every sign $s$ and rows $a$, $b$ of equal sign,
$$\langle D^{-s}_{ba}P,\; D^{s}_{ab}P\rangle = 0.$$

Lean: `New.DiscreteSeries.inner_polarisation_eq_zero` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Write $N_s(a, b)$ for the pairing. Expand both polarisations and move the variables across by the adjointness lemma. A variable of sign $-s$ of row $a$ and one of sign $s$ of row $b$ lie in columns of opposite signs, so they are distinct and no commutator term arises. The result is a sum of pairings of second derivatives $\partial_{ac}\partial_{bd}P$, and it is symmetric in $s$, so $N_{-s} = N_s$. Now take $s = 1$. If $l_b < l_a$, the last lemma makes $N_1(a, b)$ a squared norm. If $a = b$, it is a sum of squared norms. If $l_b > l_a$, use $N_1(a, b) = N_{-1}(a, b)$ and the lemma with $a$ and $b$ exchanged. So all $N_1(a, b) \geq 0$. The sum of $N_1(a, b)$ over the rows $b$ of the sign of $a$ is the pairing of a derivative of $P$ with a Laplacian of the columns applied to $P$, up to sign. That Laplacian kills $P$, so the sum is $0$, and each term is $0$. $\square$

**Corollary.** Under the same hypotheses, let $\varepsilon_a = \varepsilon_b$ and $s\,l_b < s\,l_a$. Then $D^s_{ab}P = 0$.

Lean: `New.DiscreteSeries.polarisation_eq_zero_of_isCompactPrimitive` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* By the lemma, applied to $(a, b)$ if $s = 1$ and to $(b, a)$ if $s = -1$, the two polarisations in the theorem are equal. By the theorem they are orthogonal. So $D^s_{ab}P$ has norm $0$. $\square$

**Theorem.** Under the same hypotheses, let $\rho(E_{aa})P = \Lambda_a P$, and let $s$ be a sign with $s\,w_a \geq 0$, where $w_a = \Lambda_a - v(\varepsilon_a)$. Then
$$D^{s}_{aa}P = (s\,w_a)\,P,$$
and $\partial_{ac}P = 0$ for every column $c$ where the variable $(a, c)$ has sign $-s$.

Lean: `New.DiscreteSeries.polarisation_self_eq_smul_of_isCompactPrimitive` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Put $k = s\,w_a \geq 0$ and $Q = D^{-s}_{aa}P$. The weight equation and the formula for $\rho(E_{aa})$ give $D^{s}_{aa}P = Q + kP$. The theorem on orthogonality, with $a = b$, gives $\langle Q, Q + kP\rangle = 0$, that is, $\|Q\|^2 + k\langle Q, P\rangle = 0$. By adjointness, $\langle Q, P\rangle$ is the sum of $\|\partial_{ac}P\|^2$ over the columns $c$ of sign $-s$, so it is real and $\geq 0$. Both terms are $\geq 0$, so $Q = 0$, and then each $\partial_{ac}P$ is $0$. $\square$

So $P$ is free of the variables of sign $-s$ of row $a$, and it is homogeneous of degree $s\,w_a$ in the variables of sign $s$ of that row.

### The value at the matrix of the matching

**Definition (Matrix of the matching).** The *matrix of the matching* is the point $x$ of $\mathbb{C}^{R \times C}$ with $x_{rc} = 1$ if row $r$ is matched with column $c$, and $x_{rc} = 0$ otherwise.

Lean: `New.FockDualPair.matchingPoint` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

Each row and each column of $x$ has at most one entry $1$.

**Definition (Eigendirection).** A variable $i$ is an *eigendirection* of $F$ at $x$ if there is a linear vector field $V = \sum_{k \in S} X_{a_k}\partial_{b_k}$ and a scalar $\mu$ with $VF = \mu F$, and an index $j \in S$ with $b_j = i$, such that $x_{a_k} \neq 0$ exactly for $k = j$.

Lean: `New.DiscreteSeries.IsEigenDirection` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

**Lemma.** Let $F \neq 0$ and $F(x) = 0$. Then there is a variable $i$ with $\partial_i F \neq 0$ that is not an eigendirection of $F$ at $x$.

Lean: `New.DiscreteSeries.exists_not_isEigenDirection` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Let $H(X) = F(X + x)$, the Taylor series of $F$ at $x$. It is not zero. Its constant term is $F(x) = 0$. Take a monomial $X^n$ of $H$ of least degree. Then $n \neq 0$, so $n = t + e_i$ for some variable $i$ and some $t$. The coefficient of $X^t$ in $\partial_i H$ is not zero, so $\partial_i F \neq 0$. Suppose that $i$ is an eigendirection, with a field $V$ and an index $j$. Translate $VF = \mu F$ by $x$: the field becomes $\sum_k (X_{a_k} + x_{a_k})\partial_{b_k}$. Compare the coefficients of $X^t$. On the right, $\mu$ times a coefficient of $H$ in degree $|t| < |n|$, which is $0$. On the left, the terms $X_{a_k}\partial_{b_k}H$ keep the degree, so they have no part in degree $|t|$. The constant terms leave only $x_{a_j}$ times the coefficient of $X^t$ in $\partial_i H$, which is not zero. This is a contradiction. $\square$

**Lemma.** Let $l$ and $l'$ match, let $s = \eta_{rc}$ be the sign of the variable $(r, c)$. Then one of the following holds.
1. $n' - n < -s\,\xi_r$.
2. $n' - n < s\,\xi_r$, and $(r, c)$ is matched.
3. Row $r$ is matched with a column $d$ with $\varepsilon'_d = \varepsilon'_c$ and $s\,l'_d < s\,l'_c$.
4. Column $c$ is matched with a row $a$ with $\varepsilon_a = \varepsilon_r$ and $s\,l_r < s\,l_a$.

Lean: `New.IsMatch.lt_or_exists_isMatchedPair` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Suppose that case 1 fails. If $|\xi_r| < n - n'$, then $-s\,\xi_r > n' - n$, which is case 1. So row $r$ is not free. So $r$ is matched with a column $d$, and the sign of $(r, d)$ is $s$, so $\varepsilon'_d = \varepsilon'_c$. Compare $s\,l'_d$ with $s\,l'_c$. If it is smaller, case 3 holds. If they are equal, then $d = c$ and case 2 holds. If it is larger, then column $c$ lies beyond $d$, so it is not free. It is matched with a row $a$, and the order of the centred parameters gives $s\,l_r < s\,l_a$ and $\varepsilon_a = \varepsilon_r$. This is case 4. $\square$

**Lemma.** Let $l$, $l'$ match.
1. Let row $a$ be matched with column $c$, and let $F$ be an eigenvector of $D^{s}_{ar}$ with $s = \eta_{rc}$. Then $(r, c)$ is an eigendirection of $F$ at $x$.
2. Let row $r$ be matched with column $d$, and let $F$ be an eigenvector of the polarisation of the swap from column $c$ to column $d$, in the variables of the sign of $(c, r)$ for the swap. Then $(r, c)$ is an eigendirection of $F$ at $x$.

Lean: `New.IsMatch.isEigenDirection_of_polarisation` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean). The second part is `New.IsMatch.isEigenDirection_of_swap_polarisation`.

*Proof.* In part 1 the field is $\sum_d X_{ad}\partial_{rd}$ over the columns $d$ of the sign of $(r, c)$. At $x$, the coefficient $x_{ad}$ is not zero only for $d = c$, since $a$ is matched with $c$ only. Part 2 is the same with $\sum_a X_{ad}\partial_{ac}$ and the row $r$ matched with $d$. $\square$

**Theorem.** Let $l$ and $l'$ match, and let $F$ be a pre-joint harmonic. Then $F(x) \neq 0$ at the matrix of the matching.

Lean: `New.IsMatch.eval_matchingPoint_ne_zero` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Suppose $F(x) = 0$. By the lemma on Taylor series, $F$ depends on a variable $(r, c)$ that is not an eigendirection at $x$. Let $s = \eta_{rc}$ and apply the four cases.

In case 1, the sign lemma of Section 3 gives $-s\,w_r \geq 0$. The theorem on $D^{-s}_{rr}$ shows that $F$ does not depend on the variables of sign $s$ of row $r$. The variable $(r, c)$ has sign $s$, so $\partial_{rc}F = 0$. This is a contradiction.

In case 2, the same theorem with the sign $s$ shows that $F$ is an eigenvector of $D^{s}_{rr}$. Row $r$ is matched with $c$, so part 1 of the last lemma, with $a = r$, makes $(r, c)$ an eigendirection.

In case 3, the variable $(c, r)$ of the swap has sign $-s$, and $-s\,l'_c < -s\,l'_d$. The corollary for the swap, with the compact primitivity of the columns and the Laplacians of the rows, makes the polarisation of the swap from $c$ to $d$ zero on $F$. So $F$ is an eigenvector with eigenvalue $0$, and part 2 of the last lemma gives an eigendirection.

In case 4, the corollary gives $D^{s}_{ar}F = 0$, and part 1 of the last lemma gives an eigendirection.

Each case contradicts the choice of $(r, c)$. $\square$

### Uniqueness

**Theorem (Uniqueness of joint harmonics).** Let $l$ and $l'$ match, and let $P$, $Q$ be pre-joint harmonics. Then $P = cQ$ for a scalar $c$.

Lean: `New.IsMatch.unique` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean).

*Proof.* Let $x$ be the matrix of the matching and $c = P(x)/Q(x)$. This is defined, since $Q(x) \neq 0$. Then $(P - cQ)(x) = 0$. If $P - cQ \neq 0$, it is a pre-joint harmonic, and its value at $x$ is not zero. So $P - cQ = 0$. $\square$

**Corollary.** Let $\Phi$ be a joint harmonic for $l$, $l'$.
1. Let $P$ be termwise harmonic for $T$ and for the swap, $K$-highest of weight $\Lambda$ for the row action, and compact primitive for the column action and $l'$. Then $P = c\Phi$ for a scalar $c$.
2. Let $P$ be termwise harmonic for $T$ and for the swap, compact primitive for the row action and $l$, and $K$-highest of weight $\Lambda'$ for the column action. Then $P = c\Phi$ for a scalar $c$.

Lean: `New.IsJointHarmonic.exists_eq_smul_of_row_weight` (Lib/DiscreteSeries/Theta/FockJointHarmonics.lean). The second part is `New.IsJointHarmonic.exists_eq_smul_of_column_weight`.

*Proof.* If $P = 0$, take $c = 0$. Otherwise $P$ and $\Phi$ are pre-joint harmonics, so the theorem applies. For part 2, apply part 1 to the swap, where $\Phi$ is a joint harmonic for $l'$, $l$ by Section 3. $\square$

**Remark (Formalization).** The constant $c = P(x)/Q(x)$ in the proof is a real division in `ℂ`, and $Q(x) \neq 0$ is proved. There is no junk value here. The polynomial `New.jointHarmonicAt` of the global argument is chosen by `Classical.epsilon` (Lib/Weil/Lift.lean). When a joint harmonic exists, the corollary shows that the chosen one is a nonzero multiple of every other one, so the global results do not depend on the choice.

