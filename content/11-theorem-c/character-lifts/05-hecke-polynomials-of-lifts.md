---
title: Hecke polynomials of lifts
lean:
  - New/OneLift/HeckeValues/CharacterLift.lean
  - New/OneLift/HeckeValues/CharacterLiftNorm.lean
decls:
  - New.DescentPair.heckePolyOnForms_liftHeckeRoot_eq_zero
  - New.LValueData.hasLiftHeckePolynomial_trivialLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Hecke polynomials of lifts

At a split place off the level, a theta lift from a space of rank $r$ to a space of rank $N$ has a Hecke polynomial with a special shape. It is a product of $t = N - r$ linear factors, which come from the trivial representation of the complement of $W$ in $V$, times a rescaled Hecke polynomial of rank $r$. This section proves two facts about this shape. First, for a descent pair of any rank, a form with the Hecke polynomials of a lift is killed by the Hecke polynomial operator at one explicit number $x_w$, the zero of the last linear factor. The previous chapter uses this to show that the theta lift lies in the kernel of an explicit operator. Second, the lift $\varphi_X$ of a character has the Hecke polynomials of a lift of the trivial system.

### The objects

In this section $O$ is a descent pair from a space $W$ of rank $r = \#r$ to the standard space $V$ of rank $N = \#n$, with $r < N$ (`O.rank_lt`). The difference of ranks is $t = $ `O.rankDiff` $= N - r$. Let $w$ be a finite place of $E$ that is split ($\bar w \neq w$) and such that neither $w$ nor $\bar w$ is a place of $O$. Let $q$ be the norm of $w$. The background on Hecke operators at split places is in [Iwahori-Hecke algebras and the Satake transform](/chapter/iwahori-satake/) of Volume 5, and the objects of descent pairs are in [the objects of the upper bound](/chapter/upper-bound-objects/) of Volume 9. We recall the definitions that the proof uses.

- The Hecke polynomial operator is $H_w(T) = \sum_{i=0}^{N} (-T)^i\, q^{\binom{i}{2}}\, T_{w,i}$, where $T_{w,i}$ is the Hecke operator of the $i$-th elementary divisor at $w$ (`heckePolyOp`). On `O.FormV` it is `O.heckePolyOnForms hw hw_level T`: a form of the level of $O$ is spherical at $w$, so each $T_{w,i}$ keeps the space of forms.
- A vector $y$ has the Hecke polynomial $p$ at $w$ (`HasHeckePolynomial`) if $y$ is spherical at $w$ and $H_w(T)\,y = p(T)\,y$ for every $T \in \mathbb{C}$.
- For a polynomial $p$ with this property, $H_w(T)\,y = p(T)\,y$ on `O.FormV` as well (`heckePolyOnForms_eq_smul`).
- The $q$-Pochhammer product is $(T; q)_m = \prod_{l=0}^{m-1} (1 - q^l T)$ (`SiegelWeil.qPochhammer q m`).
- For a character $a$ of $U(1)$ and a rank $m$, the Frobenius value is $a.\mathrm{frobValue}(m, w) = \chi_{a,m}(\varpi_w)\, q^{m/2}$, where $\chi_{a,m}$ is the Hecke character $x \mapsto a(x/\bar x)\,\upsilon(x)^{-m}$ of $E$ and $\varpi_w$ is the chosen uniformizer at $w$.
- Put $\nu = $ `O.charW.frobValue r w` and $\nu' = $ `O.charV.frobValue n w`.
- A form $y$ has the Hecke polynomials of a lift of a family $z$ (`O.HasLiftHeckePolynomial y z`) if at every such $w$ it has the Hecke polynomial
$$p_w(T) = (\nu T; q)_t\cdot H^{(r)}_{z(w)}\big(q^t \nu \nu'^{-1} T\big),$$
where $H^{(r)}_{z(w)}(T) = \sum_{i=0}^{r} (-T)^i\, q^{\binom i2}\, z(w)_i$ is the polynomial of rank $r$ with coefficients $z(w)$ (`heckePolyEval r w (z w)`).
- The root is $x_w = $ `O.liftHeckeRoot w` $= (\nu\, q^{t-1})^{-1}$.

### The root lemma

**Theorem (Root of the Hecke polynomial of a lift).** Let $w$ be split with $w$ and $\bar w$ off the places of $O$. Let $y$ be in `O.FormV`, and let $z$ be a family with `O.HasLiftHeckePolynomial y z`. Then

$$H_w(x_w)\, y = 0, \qquad x_w = (\nu\, q^{t-1})^{-1}.$$

Lean: `New.DescentPair.heckePolyOnForms_liftHeckeRoot_eq_zero` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Step 1. Since $r < N$, the difference $t = N - r$ is at least $1$. Write $t = k + 1$ with $k \in \mathbb{N}$.

Step 2. The number $\nu$ is not zero. Indeed $\nu = \chi(\varpi_w)\, q^{r/2}$, the value $\chi(\varpi_w)$ is the value of a unitary character at an idele, so it has absolute value $1$, and $q^{r/2} > 0$. So $x_w$ is a well defined number and $\nu x_w = q^{-k}$.

Step 3. The $q$-Pochhammer factor at $\nu x_w$ is

$$(\nu x_w; q)_{k+1} = \prod_{l=0}^{k} \big(1 - q^l\, \nu x_w\big) = \prod_{l=0}^{k-1}\big(1 - q^{l-k}\big)\cdot\big(1 - q^k\, q^{-k}\big).$$

The last factor is $1 - 1 = 0$, so the product is $0$.

Step 4. By hypothesis $y$ has the Hecke polynomial $p_w$ at $w$. By `heckePolyOnForms_eq_smul`, $H_w(x_w)\,y = p_w(x_w)\,y$. By Step 3, $p_w(x_w) = 0 \cdot H^{(r)}_{z(w)}(\dots) = 0$. So $H_w(x_w)\,y = 0$. $\square$

**Remark (Formalization).** The Lean definition of $x_w$ is an inverse in $\mathbb{C}$, and $0^{-1} = 0$ in Mathlib. If $\nu$ were $0$, then $x_w$ would be $0$ and the first factor would be $1$, not $0$. So Step 2 is needed. In the proof it appears inside `simp`, through the unfolding of `AutChar.frobValue` and `HeckeChar.atUniformizer`: the value at the uniformizer is the value of a unit of $\mathbb{C}$ (`Units.ne_zero`), and $\sqrt q \neq 0$ since $q \geq 2$. The polynomial factor $H^{(r)}_{z(w)}$ is not used, so the theorem holds for every family $z$.

The theorem says that $x_w$ is a root of the Hecke polynomial of every form with the Hecke polynomials of a lift, whatever the eigensystem of the source. In the previous chapter this makes the theta lift lie in the kernel of $H_w(x_w)$ at every split place off the level. The chapter [false lifts](/chapter/false-lifts/) defines the false lifts as the forms in this kernel.

### The Hecke polynomials of the lift of a character

Now return to data $X$ for a lift from $U(1)$, with descent pair `X.descentPair`, where $r = 1$ and $t = N - 1$. Let $\alpha = $ `charW.frobValue Unit w` and $\beta = $ `charV.frobValue n w`.

**Theorem (Hecke polynomials of the lift).** The lift $\varphi_X$ has the Hecke polynomials of a lift of the trivial system: `X.descentPair.HasLiftHeckePolynomial φ_X 1`. That is, at every split place $w$ with $w$ and $\bar w$ off the places of $X$, $\varphi_X$ is spherical and

$$H_w(T)\,\varphi_X = \Big(\prod_{l=0}^{N-2}\big(1 - q^l \alpha T\big)\Big)\big(1 - q^{N-1}\alpha\beta^{-1} T\big)\,\varphi_X.$$

Lean: `New.LValueData.hasLiftHeckePolynomial_trivialLift` (New/OneLift/HeckeValues/CharacterLiftNorm.lean).

*Proof.* Fix $w$ as in the statement.

Step 1. The constant function $1$ on $U(1)$ has the Hecke polynomial $(T; q)_1 = 1 - T$ at $w$ (`hasHeckePolynomial_qPochhammer`, applied to a function that is invariant under all translations). So $H_w(T)\,1 = (1 - T)\cdot 1$.

Step 2. For the trivial system $z = 1$ in rank $1$, the polynomial is $H^{(1)}_1(Y) = \sum_{i=0}^{1}(-Y)^i\, q^{\binom i2} = 1 - Y$. So it equals $(Y; q)_1$.

Step 3. The previous chapter proves that the theta lift transfers Hecke polynomials (`hasHeckePolynomial_thetaLift`): if a form $\xi$ on $W$ has the Hecke polynomial $H^{(r)}_{z(w)}$ at $w$, then $\Theta_W(\xi)$ is spherical at $w$ and has the Hecke polynomial $(\nu T; q)_t\, H^{(r)}_{z(w)}(q^t\nu\nu'^{-1}T)$. Apply this to $\xi = 1$, using Steps 1 and 2.

Step 4. By Section 4, $\varphi_X = [K_0(U(1)) : K_M]\,\Theta_W(1)$. The spherical vectors form a subspace, so $\varphi_X$ is spherical. The operator $H_w(T)$ is linear, so it commutes with the scalar, and $H_w(T)\,\varphi_X = p_w(T)\,\varphi_X$. $\square$

The congruences of Volume 12 use this theorem to compare the Hecke eigenvalues of the lift with those of other forms.
