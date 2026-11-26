---
title: The spine in both editions
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/Determinant/Twist/LongForms.lean
  - New/Reduction/MainInequality.lean
  - New/Reduction/Zeros/PrimeError.lean
  - New/Reduction/Zeros/Criterion.lean
  - New/Reduction/OneSidedBound.lean
decls:
  - New.Data.span_short_integralRamified_eq_top
  - New.Data.indexLe_normalizedPoincare
  - New.Data.enough_forms
  - New.Data.integral_forms_long
  - New.star_inequality
  - New.primeRemainder
  - New.LFunction_ne_zero_of_primeRemainder_le
  - New.eventually_primeRemainder_le_rpow
  - New.grh
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The spine in both editions

The last part of the proof goes from Theorems A, B and C to the half-plane theorem in four steps. Theorems A, B and C give the main inequality. The main inequality gives a one-sided bound for a weighted sum over primes. The one-sided bound gives the half-plane theorem through a criterion of Landau type. This section states each step in the form of the readable edition and gives the compact form in a remark. The proofs are in Volume 1. Here the aim is the comparison. Data $D$ for parameters $P$ are fixed throughout: a modulus $q_0$, a prime $d$, scales $x, x_1, b$, the number $m$ of lifts, the number $f$ of infinite places of the field $E$, and the long order $a$. [The data and their sizes](/chapter/data-and-sizes/) defines them.

### Theorems A, B and C

**Theorem (Theorem A (a), short forms).** The ramified source forms are spanned by the forms $\varphi$ that are integral at every prime and satisfy $\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 \leq \exp(\mathrm{main} - m\,\mathrm{rem} + f a \log^4 b)$ for every $s$ in the finite group of chosen translates and every automorphism $\sigma$ of $\mathbb{C}$.

Lean: `New.Data.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean).

*Proof.* See [Theorems A, B and C](/chapter/theorems-a-b-c/). $\square$

**Theorem (Theorem A (b), index).** Let $t$ be a finite set of translates. A finite family $y$ of target forms, each of the form $s\mathfrak{p}\,\varphi$ with $s \in t$ and $\varphi$ integral, has logarithmic index at most $\#t \cdot \dim(\mathrm{src}) \cdot 2 f a \log^3 b$ in the target lattice.

Lean: `New.Data.indexLe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

*Proof.* See [Theorems A, B and C](/chapter/theorems-a-b-c/). $\square$

**Theorem (Theorem B, enough forms).** The target dimension $d_T$ is positive, and there is a set $t$ of translates with $\#t \cdot \dim(\mathrm{src}) \leq 5 d_T \log(1 + 2b^2)$ such that the images $s\mathfrak{p}(\mathrm{src})$, $s \in t$, span a space of dimension at least $(1 - 4/b^2) d_T$.

Lean: `New.Data.enough_forms` (New/Reduction/ShortAndEnough.lean).

*Proof.* See [Theorems A, B and C](/chapter/theorems-a-b-c/). $\square$

**Theorem (Theorem C, integral forms are long).** Let $y_1, \dots, y_n$ be linearly independent target forms with $n \geq (1 - 4/b^2) d_T$, with index at most $\delta$ and covolume at most $c$. Then $d_T(\mathrm{main} - 3 f a \log^4 b) \leq c + 2\delta$.

Lean: `New.Data.integral_forms_long` (New/Determinant/Twist/LongForms.lean).

*Proof.* See [Theorems A, B and C](/chapter/theorems-a-b-c/). $\square$

**Remark (Formalization).** The compact edition has the three theorems in `New/Endgame/ShortAndEnough.lean` and `New/Endgame/LongForms.lean`, as `Data.short_forms`, `Data.enough_forms` and `Data.integral_forms_long`. There are four differences of form.

1. Compact `Data.short_forms` is one statement for parts (a) and (b). It starts with "there is a rational $q > 0$" and uses the maps $q \cdot s\mathfrak{p}$ in place of $s\mathfrak{p}$. The readable edition puts the scale into the definition of `New.Data.normalizedPoincare`.
2. The length bound has the error $\log b \cdot \mathcal{B}$, where $\mathcal{B} = f a \log^3 b$ is `Data.budget`. This is $f a \log^4 b$, as in the readable edition. The index bound is $\#t \cdot \dim \cdot \mathcal{B}$, with no factor $2$. The readable bound has $2 f a \log^3 b$.
3. Compact `Data.enough_forms` has $\log(1 + b^2)$ where the readable theorem has $\log(1 + 2b^2)$. It also states that the space of columns has positive dimension.
4. Compact `Data.integral_forms_long` takes the covolume as a bound $\exp V$ on the squared covolume at every conjugate. The readable theorem takes it through `New.TwistedLattice.CovolumeLe`. The compact edition also has `Data.exists_family_covolumeSq_le`, which puts A and B together into one family. The readable edition does this inside the proof of the main inequality.

So the two editions state the three theorems with the same main term and errors of the same order. The constants differ by small factors.

### The main inequality

**Theorem (The main inequality).** For the data $D$, $m \cdot \mathrm{rem} \leq f a \log^5 b$.

Lean: `New.star_inequality` (New/Reduction/MainInequality.lean).

*Proof.* See [the main inequality and the end of the proof](/chapter/main-inequality/). $\square$

The idea is the same in both editions. One covolume is bounded from above by A and B and from below by C. The main amount $\mathrm{main}$ occurs on both sides and cancels. What remains is $m \cdot \mathrm{rem}$ against the sum of the errors.

**Remark (Formalization).** Compact `star_inequality` (in `New/Main.lean`, line 121) states $m \cdot \mathrm{rem} \leq \log^2 b \cdot \mathcal{B}$. Since $\mathcal{B} = f a \log^3 b$, this is the same bound $f a \log^5 b$. The proofs differ. The readable proof divides by the number $n$ of forms, with $n \geq d_T/2$, and uses $\mathrm{main} \geq 0$ (`New.Data.mainAmount_nonneg`). The compact proof divides by $d_T$. It bounds the missing dimensions by the crude estimate $|h_{\mathrm{main}}| + m |\mathrm{rem}| \leq b^2 x^{99}$ (`Data.abs_mainHeight_add_remainder_le`) and the share $4/b^2$ of missing dimensions. The error table at the head of compact `New/Main.lean` lists these terms per dimension, with $L = f a \log^4 b$: length $L$; missing dimensions $4 b^{-2} \cdot b^2 x^{99}$; index $2 \cdot 5 \log(1 + b^2) \cdot \mathcal{B}$; covolume $3L$.

### The remainder and the criterion

**Definition (The remainder).** Let $q \geq 1$ and let $d$ be a prime. For $n \geq 1$ let $\lambda(n) = \Lambda(n)(1 - (n/d))$ if $n \equiv 1 \pmod q$, and $\lambda(n) = 0$ otherwise. For real $x$, the *remainder* is
$$R_q(x) = \sum_{1 \leq n \leq x} \lambda(n)\Big(\frac1n - \frac1x\Big) - \frac{\log x}{\varphi(q)} - c_q,$$
where $c_q$ is the real part of a value at $s = 1$ of a mean of logarithmic derivatives of L-functions, fixed so that $R_q(x) \to 0$.

Lean: `New.primeRemainder` (New/Reduction/Zeros/PrimeError.lean).

The compact edition has the same definition under the name `primeError`, with `lambdaClass` and `lambdaSum` for the readable `New.lambdaKResidueClass` and `New.lambdaKSum`. The readable edition proves $R_q(x) \to 0$ for odd $d$ prime to $q$ (`New.tendsto_primeRemainder`). The compact edition does not state this limit, and it does not need it.

**Theorem (One-sided criterion).** Let $q_0$ be a positive multiple of $8$, let $d_0 \equiv 7 \pmod 8$ be prime to $q_0$, and let $\beta > 1/2$. Suppose that for every prime $d \equiv d_0 \pmod{q_0}$, $R_{q_0}(x) \leq x^{\beta - 1}$ for all large $x$. Then $L(\rho, \psi) \neq 0$ for every character $\psi$ modulo $q_0$ and every $\rho \neq 1$ with $\operatorname{Re} \rho > \beta$.

Lean: `New.LFunction_ne_zero_of_primeRemainder_le` (New/Reduction/Zeros/Criterion.lean).

*Proof.* See [the criterion of Landau type](/chapter/landau-criterion/). $\square$

**Remark (Formalization).** Compact `entireL_ne_zero_of_primeError_le` (in `New/Endgame/OneSidedCriterion.lean`) has the class $a$ as a unit of $\mathbb{Z}/M$, and it asks the condition $d \equiv 7 \pmod 8$ and $\gcd(M, d) = 1$ for each prime $d$ of the class, with the bound. Its conclusion is $\tilde L(\rho, \chi) \neq 0$, where $\tilde L$ is `entireL`, the L-function times $s - 1$ for a principal character. So it has no hypothesis $\rho \neq 1$. Both files cite Landau (1905) and Montgomery and Vaughan, Sections 15.1 and 15.2, as related work.

### The one-sided bound and the half-plane theorem

**Theorem (One-sided bound).** Let $q_0 > 0$ be a multiple of $18480$, let $d \equiv q_0/2 - 1 \pmod{q_0}$ be a prime, and let $\varepsilon > 0$. Then $R_{q_0}(y) \leq y^{-1/2 + \varepsilon}$ for all large real $y$.

Lean: `New.eventually_primeRemainder_le_rpow` (New/Reduction/OneSidedBound.lean).

*Proof.* See [the main inequality and the end of the proof](/chapter/main-inequality/), and Section 4 of this chapter for the step at $x_1$. $\square$

**Theorem (The half-plane theorem).** The half-plane statement holds.

Lean: `New.grh` (New/Reduction/OneSidedBound.lean).

*Proof.* Let $\chi$ be a character modulo $q$ and let $\operatorname{Re}\rho > 1/2$, with $\chi \neq \chi_0$ or $\rho \neq 1$. If $\rho = 1$, then $\chi \neq \chi_0$ and $L(1, \chi) \neq 0$ by Dirichlet's theorem (Mathlib: `DirichletCharacter.LFunction_ne_zero_of_one_le_re`). Let $\rho \neq 1$. Choose $\beta$ with $1/2 < \beta < \operatorname{Re}\rho$. Put $q_0 = 18480 q$ and $d_0 = 9240 q - 1 = q_0/2 - 1$. Then $8 \mid q_0$, $d_0 \equiv 7 \pmod 8$ and $d_0$ is prime to $q_0$. The one-sided bound with $\varepsilon = \beta - 1/2$ gives the hypothesis of the criterion. So the induced character modulo $q_0$ has $L(\rho, \chi') \neq 0$. Since $L(s, \chi')$ is $L(s, \chi)$ times a finite product, $L(\rho, \chi) \neq 0$. $\square$

**Remark (Formalization).** The compact proofs have the same outline with other constants. Compact `eventually_primeError_le_rpow` takes $0 < \varepsilon < 1/100$ and proves $R_{N_0}(x) \leq x^{8\varepsilon - 1/2}$. Compact `New.grh` fixes $\varepsilon = (\min(\operatorname{Re}\rho, 1) - 1/2)/51$ and $\beta = 8\varepsilon + 1/2$. It uses `entireL` and so it needs no separate case $\rho = 1$. The readable bound is first proved at integers with the constant $64\varphi(q_0) + 3$ and exponent $-1/2 + 6\delta$ (`New.eventually_primeRemainder_natCast_le`), and then for all $\varepsilon > 0$. The largest difference is at the second cut-off $x_1$, in the proof of the one-sided bound. Section 4 explains it.
