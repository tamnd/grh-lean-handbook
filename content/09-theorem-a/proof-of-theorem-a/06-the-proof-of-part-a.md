---
title: The proof of part (a)
lean:
  - New/Reduction/ShortAndEnough.lean
decls:
  - New.Data.span_short_integralRamified_eq_top
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The proof of part (a)

This section proves part (a) of Theorem A. The proof uses the spanning by short forms, the seesaw identity for the trivial twist, the size of the composite lift, the size of the good part, the factor $c_B$ at infinity and the bound for $\log c_B$. At the end, one inequality between the sizes of the data absorbs all the errors. The section tracks each term of the exponent.

### The statement

**Theorem (Theorem A (a), short forms).** The span over $\mathbb{C}$ of the set of $\varphi \in \mathrm{src}_{\mathrm{int}}$ such that

$$\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 \leq \exp\bigl(\mathrm{mainAmount} - m\cdot\mathrm{rem} + f a\log^4 b\bigr)$$

for every $s \in \bar G$ and every automorphism $\sigma$ of $\mathbb{C}$ is all of $\mathrm{src}$.

Lean: `New.Data.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean).

*Proof.* Let $W$ be the set of the statement. By the theorem on short ramified forms, the $e^{\mathrm{err}_0}$-short ramified source forms span $\mathrm{src}$, where $\mathrm{err}_0 = f a\log^3 b$. The span is monotone. So it suffices to show that every $e^{\mathrm{err}_0}$-short ramified form $\varphi$ lies in $W$. Fix such a form $\varphi$. Being short, it has two properties.

- (I) For every prime $p$ and every embedding $\iota_p : \mathbb{C} \to \mathbb{C}_p$, $\mathrm{GaugeLe}(1, 1, \varphi)$.
- (S) For every automorphism $\sigma$ and every finite adelic point $g$ of the unitary group of $X_0$, $|\sigma\varphi(g)|^2 \leq e^{\mathrm{err}_0}$.

*Step 1: integrality.* Let $\iota$ be a pair of a prime $\ell$ and an isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$. Property (I) at $\ell$ and the place of $\iota$ says that every value of $\varphi$ has gauge at most $1$. This is the membership of $\varphi$ in the integral source forms at the place of $\iota$. As $\varphi$ is ramified, $\varphi \in \mathrm{src}_{\mathrm{int}}$.

*Step 2: the seesaw identity.* Fix $s \in \bar G$ and an automorphism $\sigma$. Apply the seesaw identity for $c_{ss}^{-1}\mathcal{P}$ to the trivial $m$-fold twist. Its underlying twist is trivial, and its tame character is the trivial character. This gives a chain datum $\Psi$ for the trivial twist with

$$\iota_1\bigl(\mathcal{P}(c_{ss}^{-1}\psi)\bigr) = B_{1,\Psi}\psi \qquad \text{for all } \psi \in \mathrm{src}.$$

Put $z = \mathcal{P}(c_{ss}^{-1}\varphi)$, a form of principal level on $Y_0$. Then $\iota_1 z = B_{1,\Psi}\varphi$.

*Step 3: the size of the chain.* Put

$$\beta = \mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\sum_{\ell\in\mathcal{S}}\mathrm{gain}_\ell\log\ell + \mathrm{err}_0.$$

This is the number $\beta$ of the theorem on the size of the composite lift, as $\mathrm{err}_0 = f a\log^3 b$. That theorem applies to $\Psi$, to $\sigma$ and to $\varphi$ with $B = \mathrm{err}_0$, by (S). For every finite adelic point $y$ of the unitary group of $Y_m$ it gives

$$|\sigma(\iota_1 z)(y)|^2 = |\sigma(B_{1,\Psi}\varphi)(y)|^2 \leq \exp(\mathrm{err}_0 + \beta).$$

*Step 4: the passage to the target.* The form $s\mathfrak{p}_0\,\varphi$ is $\#\bar G\,e_0\,s\,z$, and $\Theta_1(s\mathfrak{p}_0\,\varphi)$ is $\iota_1(\#\bar G\,e_0\,s\,z)$ at the level of the trivial twist. The lemma on the size of the good part, with $B = \mathrm{err}_0 + \beta$, gives

$$\|\Theta_1(s\mathfrak{p}_0\,\varphi)\|_\sigma^2 \leq \exp\bigl(x^{99} + \mathrm{err}_0 + \beta\bigr).$$

*Step 5: the factor $c_B$.* The lemma on the factor $c_B$ at infinity and Step 4 give

$$\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 = \exp(2\log c_B)\,\|\Theta_1(s\mathfrak{p}_0\,\varphi)\|_\sigma^2 \leq \exp\bigl(2\log c_B + x^{99} + \mathrm{err}_0 + \beta\bigr).$$

*Step 6: the exponent.* As $\exp$ is increasing, it suffices to show

$$2\log c_B + x^{99} + \mathrm{err}_0 + \beta \leq \mathrm{mainAmount} - m\cdot\mathrm{rem} + f a\log^4 b.$$

The lemma on the logarithm of the gain factor gives

$$2\log c_B \leq -2\sum_{\ell\in\mathcal{S}}\mathrm{gain}_\ell\log\ell + 2\,\mathrm{err}_0 + 2b.$$

Add $x^{99} + \mathrm{err}_0 + \beta$ to both sides and insert the definition of $\beta$. The two sums over $\mathcal{S}$ cancel. The result is

$$2\log c_B + x^{99} + \mathrm{err}_0 + \beta \leq \mathrm{mainAmount} - m\cdot\mathrm{rem} + x^{99} + 4\,\mathrm{err}_0 + 2b.$$

So it suffices to show the size inequality

$$x^{99} + 4 f a\log^3 b + 2b \leq f a\log^4 b. \tag{E}$$

This is a consequence of the logarithmic bounds of the data, as the next subsection explains. With (E), $\varphi \in W$. $\square$

### The exponent term by term

The table lists the terms of the final exponent. The column "from" gives the step that adds the term.

| Term | Value | From |
|---|---|---|
| size of $\varphi$ | $\mathrm{err}_0$ | Step 3, property (S) |
| main amount | $\mathrm{mainAmount}$ | Step 3, the size of the chain |
| remainder | $-m\cdot\mathrm{rem}$ | Step 3, the size of the chain |
| gains in the chain | $+2\sum_{\mathcal{S}}\mathrm{gain}_\ell\log\ell$ | Step 3, the size of the chain |
| error of the chain | $\mathrm{err}_0$ | Step 3, the size of the chain |
| good part | $x^{99}$ | Step 4 |
| gains in $c_B$ | $-2\sum_{\mathcal{S}}\mathrm{gain}_\ell\log\ell$ | Step 6, bound for $\log c_B$ |
| errors in $c_B$ | $2\,\mathrm{err}_0$ | Step 6, property 3 of the errors |
| integer parts in $c_B$ | $2b$ | Step 6, the logarithms of the primes |

The sum of the column is $\mathrm{mainAmount} - m\cdot\mathrm{rem} + x^{99} + 4\,\mathrm{err}_0 + 2b$. The gains cancel exactly, with no loss. This is the reason for the factor $2$ in the size of the chain: it is a squared norm, and $c_B$ enters the squared norm as $c_B^2$. The losses are of three kinds: four copies of $\mathrm{err}_0$, the term $x^{99}$ of the good part, and the term $2b$ of the floors. Inequality (E) absorbs all three into $f a\log^4 b$.

### The size inequality

In the source, (E) is an instance of the general tactic for logarithmic bounds of the data (`le_of_hasLogBound`). The proof by hand is short. Recall from [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes) that $f \geq 1$ (the field $E$ has an infinite place), $a = xb$, $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$, and that $x \geq 1$.

1. $x^{99} \leq x^{10^6} \leq x_1 \leq b \leq xb = a$, as $x \geq 1$.
2. $2b \leq 2a$, as $x \geq 1$.
3. So $x^{99} + 4 f a\log^3 b + 2b \leq 3a + 4 f a\log^3 b \leq f a(3 + 4\log^3 b)$.
4. The scale inequalities give $\log x \geq 6.4 \cdot 10^{15}$, and $b \geq x$, so $\log b \geq 7$. Then $3 + 4\log^3 b \leq \log^3 b\,(3/343 + 4) \leq 5\log^3 b \leq \log^4 b$.

So the left side of (E) is at most $f a\log^4 b$. The margin is wide: the inequality holds with $\log b \geq 5$ in place of $\log b \geq 7$.

**Remark (Formalization).** The constant $f a\log^4 b$ is fixed by the statement of the source, and the constant $\exp(\mathrm{err}_0)$ of the short forms is fixed by the theorem on short ramified forms. No other constant enters. The source closes Step 6 with `grw` and `linarith`: it rewrites with the lemma on the factor $c_B$ at infinity, uses Step 4, merges the exponentials, and leaves a linear inequality between real numbers. The inputs of `linarith` are the bound for $\log c_B$ and (E).

### What the proof uses about $\varphi$

The proof uses (I) only in Step 1, and (S) only in Step 3. In particular, the archimedean bound of part (a) does not need the integrality of $\varphi$. The integrality is part of the statement, because part (b) and the main inequality need integral forms. The spanning set of part (a) is a set of integral forms, so part (b) applies to its images.

The proof uses only the trivial twist. For a twist $\vartheta \neq 1$ the size theorem is not proved, and the bound in the statement is only for $\Theta_1$. In the main inequality, the archimedean size enters through $\Theta_1$ alone, and the other twists enter only through integrality, in part (b).

**Example (One form).** Suppose that $\mathcal{S}$ is empty. Then $c_B = N^{-g_N}$, and $\beta = \mathrm{mainAmount} - m\cdot\mathrm{rem} + \mathrm{err}_0$. For a short form $\varphi$, Steps 3 to 5 give the bound $\exp(2\log c_B + x^{99} + 2\,\mathrm{err}_0 + \mathrm{mainAmount} - m\cdot\mathrm{rem})$. Here $\log c_B = -g_N\log N \leq (\mathrm{err}(N) + 1)\log N \leq \mathrm{err}_0 + b$. The factor $c_B \geq 1$ makes the form larger at infinity. In exchange it makes the form integral at $N$ in part (b). The bound of the theorem holds with room to spare: the excess $x^{99} + 4\,\mathrm{err}_0 + 2b$ is at most $f a\log^4 b$ by (E).
