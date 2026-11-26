---
title: The chapter
lean:
  - New/Appendix/DiscreteSeries/PositionGroup.lean
  - New/Appendix/DiscreteSeries/Periods.lean
decls:
  - New.DiscreteSeries.IsSteep.exists_volume_le_mul_norm_integral_dsCoeff
  - New.DiscreteSeries.IsLaplaceDatum.laplace_method
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter

This chapter proves a lower bound for a period of two discrete series coefficients. The period is an integral over a unitary group $U(p,q)$ of a coefficient of $U(p,q)$ times the conjugate of a coefficient of a larger group $U(p+1,q)$ or $U(p,q+1)$, restricted to $U(p,q)$. The bound says that the period is not small. It is at least the volume of a unit ball, divided by a power of a size parameter $\beta$. The method is Laplace's method. The integrand is close to a Gaussian near the identity, it has a phase that can be removed, and it decays away from a compact subgroup. The chapter makes each of these statements exact, with explicit constants.

The place of this chapter in the whole argument is given in [The theorem and the plan](/chapter/theorem-and-plan/). The source uses the bound twice. At the archimedean places of the deep level argument it gives a nonzero local period (see [/chapter/deep-level-poincare/](/chapter/deep-level-poincare/)). In the spanning argument it gives a large value of a Bessel function at the real place (see [/chapter/bessel-real-place/](/chapter/bessel-real-place/)).

### The setting

Let $n$ be a finite set and let $\varepsilon : n \to \{\pm 1\}$ be a vector of signs. Write $J_\varepsilon$ for the diagonal matrix with entries $\varepsilon_i$ and
$$G = U(\varepsilon) = \{ g \in GL_n(\mathbb{C}) : g^* J_\varepsilon g = J_\varepsilon \}.$$
If $\varepsilon$ has $p$ entries $+1$ and $q$ entries $-1$, then $G \cong U(p,q)$. The maximal compact subgroup $K$ is the set of block diagonal elements, so $K \cong U(p) \times U(q)$.

A discrete series of $G$ is given by its Harish-Chandra parameter $\lambda$. The source stores the doubled parameter $l = 2\lambda \in \mathbb{Z}^n$. The lowest $K$-type of the representation has a highest weight $\mu \in \mathbb{Z}^n$; in this chapter $\mu$ is always this weight, seen as the diagonal matrix $\operatorname{diag}(\mu_i)$. The coefficient $c_l$ is the matrix coefficient of a unit highest weight vector of the lowest $K$-type. It satisfies $c_l(1) = 1$. The previous chapter, [Discrete series through one matrix coefficient](/chapter/discrete-series/), defines $c_l$ by the integral of Flensted-Jensen and proves the facts that we use.

A parameter has gap $A$ if its entries are distinct, of the parity of $\#n - 1$, and two entries of $\lambda$ at indices of opposite sign differ by at least $A$. A parameter has large gap $h$ if it has gap $500(\#n)^3 + h$. A large gap gives fast decay of $c_l$ away from $K$.

### The main theorem

The main result is the restriction bound. Let $\varepsilon \oplus 1$ be the vector of signs on $n \sqcup \{\ast\}$ that is $\varepsilon$ on $n$ and $+1$ at the new index. Then $g \mapsto g \oplus 1$ embeds $U(\varepsilon)$ in $U(\varepsilon \oplus 1)$. The norm in this statement is the operator norm.

**Theorem (Restriction).** Let $X$ be a finite set and let $M$ be even. Let $l$ be a parameter of $U(\varepsilon)$ that is steep for a splitting $e : X \sqcup \{0, \dots, M-1\} \cong n$ and a constant $B \geq 1$. Let $l'$ be a parameter of $U(\varepsilon \oplus 1)$ such that $-l'$ is steep for a splitting $e' : X \sqcup \{0, \dots, M\} \cong n \sqcup \{\ast\}$ and the same $B$. Let both have large gap $h$, and let all entries of $l$ and $l'$ have absolute value at most $L$. Write $N = \#n$. Let $\beta \geq 10^{12}$ with
$$ 2N + 1 + L \leq \beta, \qquad (N+1)^4 (6B)^{2M+2} \leq \beta, \qquad 10^{30}\big((2N+1)^2 \log \beta\big)^3 \leq h. $$
Then there is $y \in U(\varepsilon \oplus 1)$ with $\|y\|^2 \leq \beta$ and
$$ \operatorname{vol}\{ g \in U(\varepsilon) : \|g - 1\| \leq 1 \} \leq \beta^{20(2N+1)^2} \left| \int_{U(\varepsilon)} c_l(g)\, \overline{c_{l'}\big(y^{-1}(g \oplus 1) y\big)}\, dg \right|. $$
Lean: `New.DiscreteSeries.IsSteep.exists_volume_le_mul_norm_integral_dsCoeff` (New/Appendix/DiscreteSeries/PositionGroup.lean).

Section 8 proves this theorem. Section 2 defines steep parameters. The measure on $U(\varepsilon)$ is a Haar measure that the source makes from Lebesgue measure by a Cayley chart, with the normalisation of the compact dual. The left side is a positive constant that depends only on $\varepsilon$.

**Remark (Formalization).** In the source the numbers $2N+1$ and $N+1$ appear as $\#(n \sqcup \{\ast\}) + \#n$ and $\#(n \sqcup \{\ast\})$. The conclusion is an inequality of real numbers, so it does not say that the integral exists. The integrability is a part of the general theorem below.

### Laplace's method in general

The restriction bound is a special case of a general statement about a group $S$ with a homomorphism $j : S \to U(\varepsilon) \times U(\eta)$. For $s \in S$ write $j(s) = (g, g')$. Let $\varphi : S \to \mathbb{C}$ be a function. The integrand is
$$ \theta(s) = c_l(g)\, \overline{c_k(g')}\, e^{-\varphi(s)}. $$
A Laplace datum is a list of conditions on $l$, $k$, $j$ and $\varphi$. The main ones are: $l$ is steep, $\varphi(s)$ is the difference $\operatorname{tr}\mu(g-1) - \operatorname{tr}\mu'(g'-1)$ of the two phases, $\varphi$ is additive and imaginary, and the image of $j$ contains a diagonal copy of $U(X)$. Section 2 gives the full list.

**Theorem (Laplace's method).** Let $(l, k, j, \varphi)$ be a Laplace datum with $B \geq 1$, for a right invariant measure $\nu$ on $S$ that is finite on compact sets. Let $s \mapsto g$ be proper and let $s \mapsto g'$ be continuous. Let $l$ and $k$ have large gap $h$ and entries of absolute value at most $L$. Let $\beta \geq 10^{12}$ with $\#n + \#m + L \leq \beta$ and $10^{30}((\#n + \#m)^2 \log \beta)^3 \leq h$. Then $\theta$ is integrable, and
$$ \nu\{ s : \|g\| \leq \beta + 1,\ \|g'\| \leq \beta + 1 \} \leq \beta^{20(\#n + \#m)^2} \left| \int_S \theta \, d\nu \right|. $$
Lean: `New.DiscreteSeries.IsLaplaceDatum.laplace_method` (New/Appendix/DiscreteSeries/Periods.lean).

Here the norm is the operator norm. Section 6 proves this theorem.

### What the chapter uses

From the previous chapter we use five facts about $c_l$. First, $c_l(1) = 1$. Second, $c_{-l} = \overline{c_l}$ if $l$ has a gap. Third, on $K$ the coefficient is an explicit product of principal minors, raised to powers given by the weight $\mu$. Fourth, if $l$ has gap $h$ and $c \leq h$, then
$$ |c_l(g)|^2\, |\det a|^c \leq 1, $$
where $a$ is the block diagonal part of $g$. Fifth, $c_l$ is at least $1/2$ in a small ball about $1$, and the volume of a ball is bounded by the integral of $|c_l|^2$ over it. The exact statements are in [/chapter/discrete-series/](/chapter/discrete-series/), at [the value at one](/decl/New.dsCoeff_one/), [the conjugate](/decl/New.dsCoeff_neg/), [the restriction to K](/decl/New.dsCoeff_of_mem_maxCompactU/), [the decay](/decl/New.norm_dsCoeff_sq_mul_det_pow_le_one/), [the lower bound near one](/decl/New.half_le_norm_dsCoeff/) and [the volume bound](/decl/New.measure_ball_le_integral_dsCoeff/).

We also use elementary matrix analysis: the polar decomposition, the power series of the logarithm, and Schwarz's lemma for holomorphic functions of one variable.

### A sketch of the proof

The proof has four steps.

The first step is localization. Write $g = a + y$, where $a$ is the block diagonal part and $y$ is the rest. The decay bound gives $|c_l(g)|^4 \leq (1 + \|y\|^2)^{-h}$. So the integrand is very small unless $y$ and $y'$ are small. If they are small, steepness and the imaginary phase show that $s$ can be moved, without change of $\theta(s)$, to a point where $g$ and $g'$ are both near $1$ (section 3).

The second step is a second order expansion of one principal minor of a unitary matrix near $1$ (section 4). The third step multiplies these expansions. It gives the Gaussian shape: near $1$, the ratio $c_l(g)/\exp(\operatorname{tr}\mu \log g)$ is within $10\%$ of a number $\varrho \in [0,1]$, up to a tiny error (section 5).

The fourth step is Laplace's method itself. The phases $\exp(\operatorname{tr}\mu\log g)$ and $\exp(\operatorname{tr}\mu'\log g')$ cancel against $e^{-\varphi}$. So $\theta$ takes values in a cone about the positive real axis, up to a small error. A function with values in such a cone has an integral at least a fixed fraction of the integral of its modulus. A covering argument compares the large ball with the small ball where $|\theta| \geq 1/4$ (section 6).

Sections 7 and 8 construct the Laplace datum for the restriction problem. A stationary position is a flag $v_1, \dots, v_{j_0}$ and an isometry $i_0$ such that the subgroup of $g$ for which $g - 1$ lowers the flag has the right phase. The vectors are built from the values of polynomials at the weights, and their pairings are computed by residues.
