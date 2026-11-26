---
title: Orbital integrals and the Selberg principle
lean:
  - Lib/Adelic/TraceFormula/OrbitalUnfolding.lean
  - Lib/Adelic/TraceFormula/TraceComparison.lean
decls:
  - New.FrameClass
  - New.Space.orbitalIntegral
  - New.Space.classIntegral
  - New.Space.hasSum_classIntegral
  - New.Space.orbitalIntegral_unfold
  - New.Space.mul_orbitalIntegral_eq_zero
  - New.Space.orbitalIntegral_eq_zero
  - New.Space.geometricSide_singleton_eq_zero_of_norm_ne_one
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Orbital integrals and the Selberg principle

Now let $R$ be irreducible. This section unfolds $I_R$ into a sum of orbital integrals, one for each conjugacy class of rational points with characteristic polynomial $R$. It then proves the Selberg principle in the form that the argument needs: if some complex root of $R$ at some infinite place lies off the unit circle, every orbital integral of $e \otimes \varphi$ at such a point is $0$. So $I_R(\varphi) = 0$ for these $R$, and only the polynomials with all roots on the unit circle remain for Section 6.

### Classes and orbital integrals

The comparison in Section 6 matches conjugacy classes of two different spaces. To compare them, the source records a rational point together with the frame of its space.

**Definition (Frame classes).** A *frame class* is a class of pairs $(x, y)$, where $x$ is an element of $\mathrm{GL}_N(\mathbb{A}_{E,f})$ taken modulo the unitary group $U(1)(\mathbb{A}_{E,f})$ of the identity form on the right, and $y \in \mathrm{GL}_N(E)$. Two pairs are in the same class if $z \cdot (x, y) = (z x, z y z^{-1})$ carries one to the other for some $z \in \mathrm{GL}_N(E)$.
Lean: `New.FrameClass` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

For a space $V$ with finite frame $x_V$, the class of $(x_V, \gamma)$ is written $[x_V, \gamma]$ (`New.frameClass`). Two rational points $\gamma, \delta$ of $V$ have the same class if and only if they are conjugate under $U(V)(E)$ (`New.Space.frameClass_eq_iff_mem_orbit`). The finite frame is recorded because a matrix $z$ with $z x_V \in x_{V'} U(1)(\mathbb{A}_{E,f})$ is an isometry from $V'$ to $V$ at the finite places.

Let $\gamma$ be a rational point of $V$ and let $\Gamma_\gamma$ be the image in $G$ of its centraliser in $U(V)(E)$.

**Definition (Orbital integral).** For functions $k$ on $G_\infty$ and $\varphi$ on $G_f$, the *orbital integral* of $k \otimes \varphi$ at $\gamma$ is
$$ O_\gamma(k \otimes \varphi) = \int_{\Gamma_\gamma \backslash G} k\big((x^{-1} \gamma x)_\infty\big)\, \varphi\big((x^{-1} \gamma x)_f\big)\, dx. $$
Lean: `New.Space.orbitalIntegral` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

The measure on $\Gamma_\gamma \backslash G$ is built from Haar measure on $G$ and a cutoff for $\Gamma_\gamma$, as in Section 3. The integral is the Bochner integral. If the integrand is not integrable it is $0$ by definition. The unfolding theorem below shows that it is integrable when $R$ is irreducible.

**Definition (Class integral).** For a polynomial $R$ and a frame class $c$, put
$$ J_{R,c}(k \otimes \varphi) = \sum_{\gamma \,:\, [x_V, \gamma] = c} \int_{[G]} \mathbf{1}[\chi_\gamma = R]\; k\big((x^{-1} \gamma x)_\infty\big)\, \varphi\big((x^{-1} \gamma x)_f\big)\, dx. $$
Lean: `New.Space.classIntegral` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

**Theorem.** Let $N \geq 1$ and $B \geq 13 N^3$. Let $\varphi$ be a test function and $k$ a measurable function on $G_\infty$ with $|k(g)|\, \|g\|^B$ bounded. Let $R$ be irreducible. Then the family $(J_{R,c})_c$ over all frame classes is summable, with sum
$$ \int_{[G]} \sum_{\gamma \,:\, \chi_\gamma = R} k\big((x^{-1} \gamma x)_\infty\big)\, \varphi\big((x^{-1} \gamma x)_f\big)\, dx. $$
Lean: `New.Space.hasSum_classIntegral` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

*Proof.* The sum over $\gamma$ with irreducible $\chi_\gamma$ of the absolute values of the terms is bounded on $G$ (`New.Space.exists_tsum_enorm_irreducibleTerm_le`). Since $[G]$ has finite volume, the integral of this sum is finite, and the integral and the sum over $\gamma$ can be interchanged. Group the $\gamma$ by their frame class. $\square$

When $k$ is a cusp kernel of order $B$, the integral in the theorem is $I_R(\varphi)$.

**Theorem (Unfolding).** Let $N \geq 1$, $B \geq 13 N^3$, and let $\varphi$ and $k$ be as in the last theorem. Let $\gamma$ be a rational point with $\chi_\gamma$ irreducible. Then $x \mapsto k((x^{-1} \gamma x)_\infty)\, \varphi((x^{-1} \gamma x)_f)$ is integrable on $\Gamma_\gamma \backslash G$, and
$$ J_{\chi_\gamma, [x_V, \gamma]}(k \otimes \varphi) = O_\gamma(k \otimes \varphi). $$
Lean: `New.Space.orbitalIntegral_unfold` (Lib/Adelic/TraceFormula/OrbitalUnfolding.lean).

*Proof.* The rational points of class $[x_V, \gamma]$ are the conjugates $\delta \gamma \delta^{-1}$, $\delta \in U(V)(E)$, and they are in bijection with $U(V)(E) / \mathrm{Cent}(\gamma)$. The sum over them of the integrals over $\Gamma \backslash G$ is the integral over $\Gamma_\gamma \backslash G$, by unfolding in stages for the cutoff measures. The bound of the last proof gives the integrability. $\square$

### The Selberg principle

The classical principle is the following. Let $f$ be a matrix coefficient, or a pseudo-coefficient, of a discrete series representation of a real reductive group. Then the orbital integrals of $f$ vanish at the regular semisimple elements that are not elliptic. For this principle the source cites Harish-Chandra, *Discrete series II*, Acta Math. 116 (1966), Theorem 11; Blanc and Brylinski, *Cyclic homology and the Selberg principle*, J. Funct. Anal. 109 (1992); and Hochs and Wang, *Orbital integrals and K-theory classes* (2019), Corollary 4.8. This chapter has not compared these citations with their sources.

The proof in the source has a different form. It uses only that $e$ is an idempotent with enough decay, and it works with the adelic orbital integral directly. The idea is the trace property of a projection. Let $p$ be an idempotent operator and $D$ a derivation. Then $p\, D(p)\, p = 0$, since $D(p) = D(p^2) = D(p) p + p D(p)$ gives $p D(p) p = 2 p D(p) p$. Here $p$ is convolution by $e$, $D$ is the commutator with multiplication by a function $H$, and the trace is the orbital integral. A $\gamma$ that shifts $H$ by $\ell$ gives $\ell \cdot O_\gamma = 0$.

**Theorem.** Let $N \geq 1$ and $B \geq 13 N^3$, let $e$ be a cusp kernel of order $B$ and $\varphi$ a test function. Let $\gamma$ be a rational point with $\chi_\gamma$ irreducible. Let $H : G_\infty \to \mathbb{R}$ be measurable and $\ell \in \mathbb{R}$, with:

1. $|H(a b) - H(a)| \leq \|b\|$ for all $a, b \in G_\infty$;
2. $H(\gamma_\infty y) = \ell + H(y)$ for all $y$;
3. for every rational point $t$ that commutes with $\gamma$ there is $r \in \mathbb{R}$ with $H(t_\infty y) = r + H(y)$ for all $y$.

Then $\ell \cdot O_\gamma(e \otimes \varphi) = 0$.
Lean: `New.Space.mul_orbitalIntegral_eq_zero` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* Work on triples $(x, y, u)$ with $x \in \Gamma_\gamma \backslash G$ and $y, u \in G_\infty$. Write $c = x^{-1} \gamma x$ and, for brevity, $H(x)$ for $H(x_\infty)$. Put
$$ P(x, y, u) = e(y)\, e(u)\, e\big(u^{-1} y^{-1} c_\infty\big)\, \varphi(c_f). $$
With $p(a, b) = e(a^{-1} b)$ this is $p(x, x y)\, p(x y, x y u)\, p(x y u, \gamma x)$ at infinity. Since $e * e = e$, two integrations give $\int P = O_\gamma(e \otimes \varphi)$. Define the weights
$$ a_1 = H(x y) - H(x), \quad a_2 = H(x y u) - H(x y), \quad a_3 = \ell + H(x) - H(x y u). $$
Their sum is $\ell$. Item 1 and the decay of $e$ to order $B$ make $a_1 P$, $a_2 P$ and $P$ integrable (`New.Space.integrable_mul_tripleKernel`), and so $a_3 P$ is integrable.

First, $\int a_2 P = 0$. The weight $a_1 + a_2 = H(x y u) - H(x)$ depends on $y u$ only. After the substitution $(y, u) \mapsto (u, u^{-1} y)$ the integral over the inner variable is a convolution $e * e = e$. So $\int (a_1 + a_2) P = \int a_1 P$ (`New.Space.integral_mul_tripleKernel_mul`). This is the identity $p\, D(p)\, p = 0$.

Second, $\int a_1 P = \int a_2 P = \int a_3 P$. The rotation $(x, y, u) \mapsto (x (y, 1), u, u^{-1} y^{-1} c_\infty)$ replaces the points $x, x y, x y u$ by $x y, x y u, \gamma x$. It keeps $P$ and the measure (`New.Space.integral_mul_tripleKernel_tripleRotate`). It carries $a_1$ to $a_2$, and by item 2 it carries $a_2$ to $a_3$. The rotation is defined on $G$, not on $\Gamma_\gamma \backslash G$. It descends because the weights are invariant under left translation by $\Gamma_\gamma$, by item 3. This is the trace property.

So $\ell\, O_\gamma = \int (a_1 + a_2 + a_3) P = 3 \int a_2 P = 0$. $\square$

**Theorem (Selberg principle).** Let $N \geq 1$ and $B \geq 13 N^3$, let $e$ be a cusp kernel of order $B$ and $\varphi$ a test function. Let $\gamma$ be a rational point with $\chi_\gamma$ irreducible. Suppose that for some infinite place $v$ some complex root $\lambda$ of $\chi_\gamma$ at $v$ has $|\lambda| \neq 1$. Then $O_\gamma(e \otimes \varphi) = 0$.
Lean: `New.Space.orbitalIntegral_eq_zero` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* Let $A = \gamma_v$ in the frame, a matrix over $\mathbb{C}$. Since $\chi_\gamma$ is irreducible, it is separable, and $A$ is diagonalisable with distinct eigenvalues $d_j$: $k A k^{-1} = \operatorname{diag}(d)$. Let $\lambda = d_i$ and let $Q = E_{ii}\, k$, the $i$-th row of $k$. Put $H(y) = \log \|Q y_v\|$ and $\ell = \log |\lambda| \neq 0$. Then:

1. $H(a b) - H(a) = \log\big(\|Q a_v b_v\| / \|Q a_v\|\big) \leq \|Q a_v b_v\| / \|Q a_v\| \leq \|b_v\|$, since $\log r \leq r$. The other inequality follows from the same bound for $b^{-1}$, as $\|b_v^{-1}\| = \|b_v\|$ for a unitary matrix (`New.U.norm_inv`). Each factor of $\|b\|$ is at least $1$, so $\|b_v\| \leq \|b\|$. This gives item 1.
2. $Q A = \lambda Q$, so $H(\gamma_\infty y) = \ell + H(y)$.
3. A matrix $t_v$ that commutes with $A$ is diagonal in the basis of $k$, since the eigenvalues are distinct. So $Q t_v = \mu Q$ for a scalar $\mu \neq 0$, and $H$ shifts by $\log |\mu|$.

[The last theorem](/decl/New.Space.mul_orbitalIntegral_eq_zero/) gives $\ell \cdot O_\gamma = 0$, so $O_\gamma = 0$. $\square$

**Corollary.** Let $N \geq 1$ and $B \geq 13 N^3$, let $e$ be a cusp kernel of order $B$ and $\varphi$ a test function. Let $R$ be irreducible, and suppose some complex root of $R$ at some infinite place has absolute value $\neq 1$. Then $I_R(\varphi) = 0$.
Lean: `New.Space.geometricSide_singleton_eq_zero_of_norm_ne_one` (Lib/Adelic/TraceFormula/TraceComparison.lean).

*Proof.* A class $c$ with $J_{R,c} \neq 0$ contains a pair $(x_V, \gamma)$ with $\chi_\gamma = R$ (`New.Space.exists_frameClass_eq_of_classIntegral_ne_zero`). Then $J_{R,c} = O_\gamma = 0$ by [unfolding](/decl/New.Space.orbitalIntegral_unfold/) and the Selberg principle. So every $J_{R,c}$ is $0$, and $I_R(\varphi) = 0$ by [the summation theorem](/decl/New.Space.hasSum_classIntegral/). $\square$

**Remark (Formalization).** The complex roots of $R$ at $v$ are numbered by $n$ through a fixed embedding $\Phi_v : E \to \mathbb{C}$ of the CM type (`New.Variety.numberedRoots`). The numbering is a choice, and it does not matter: the hypothesis asks for one index $i$ with a root off the unit circle. The function $H$ depends on the choice of $k$ and $i$, but the proof only needs its three properties.

### Where the principle has content

If all signs $s_j$ at the infinite place $v$ are equal, then $U(\operatorname{diag} s)$ at $v$ is a compact group $U(N)$. Every element is unitary, and its eigenvalues have absolute value $1$. So for a definite space the hypothesis of the Selberg principle never holds at $v$. For an indefinite space it can. Take $N = 2$ and signs $(1, -1)$, so that $U(1,1)$ at $v$ contains the hyperbolic elements with eigenvalues $\lambda$ and $\bar\lambda^{-1}$, $|\lambda| \neq 1$. In general the eigenvalues of an element of $U(p, q)$ are stable under $\lambda \mapsto \bar\lambda^{-1}$. The terms of such $\gamma$ appear in the trace formula of an indefinite space and have no partner in a definite space. The Selberg principle removes them.
