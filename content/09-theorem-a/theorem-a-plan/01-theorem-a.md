---
title: Theorem A
lean:
  - New/Reduction/ShortAndEnough.lean
  - New/UpperBound/Size/ShortColumns.lean
  - New/Reduction/Lattices/Heights.lean
decls:
  - New.Data.integralRamified
  - New.Data.normalizedPoincare
  - New.Data.span_short_integralRamified_eq_top
  - New.Data.indexLe_normalizedPoincare
  - New.Data.divisibilityError
  - New.PrimePadicIso
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theorem A

This volume proves Theorem A, the upper bound of the argument. Theorem A says two things about a family of linear maps $s\mathfrak{p}$, one for each $s$ in a finite group $\bar G$, from a space of source forms to a space of target forms. Each map $s\mathfrak{p}$ is the translate by $s$ of the map $1\mathfrak{p}$. Part (a) says that the source is spanned by integral forms whose images are short at every archimedean conjugate. Part (b) says that the images of integral forms have small index in the target lattice. This chapter states Theorem A exactly, with all its sizes. It states the three inputs of the proof: the divisibility of a chain of theta lifts prime by prime, the seesaw identity, and the archimedean size of the chain. It shows how the three inputs meet, and it proves Theorem A from them. The last sections give a map of the fourteen later chapters of the volume, the prerequisites from the earlier volumes, exercises, and notes.

### Where Theorem A sits

[The plan](/chapter/theorem-and-plan/) of Volume 1 reduces the half-plane statement of the source to one inequality, the main inequality $m \cdot \mathrm{rem} \leq f a \log^5 b$ of [the main inequality](/chapter/main-inequality/). Here $\mathrm{rem}$ is the total remainder of [the prime sums](/chapter/prime-sums/), a sum of differences between prime sums and their expected values. The main inequality comes from a comparison of two bounds for the covolume of one twisted lattice of target forms. Theorem A gives the upper bound. Theorem B (Volume 10) says that the vectors of Theorem A fill almost all of the target. Theorem C (Volume 11) gives the lower bound by the product formula. [Theorems A, B and C](/chapter/theorems-a-b-c/) states the three theorems side by side and shows how the main inequality follows. This chapter takes that chapter as known and goes one level down: it opens the proof of Theorem A.

The upper bound has the term $-m\cdot\mathrm{rem}$ in its exponent. This is the place where the prime remainder enters the geometry. The lower bound of Theorem C has no such term.

### The objects

Fix the data $D$ of [the data and its sizes](/chapter/data-and-sizes/). The data give the scales $x$, $x_1$, $b$ with $(\log b)^{100} \leq x$, $x^{10^6} \leq x_1$ and $x_1^{10^6} \leq b$; the long order $a = x b$; the number of lifts $m \in [\sqrt{x}, 2\sqrt{x}]$, a power of $2$; the rank $r \in [x^5, 3x^5]$, a power of $3$; the rank $k = r + 1 - m$ of the source; the CM field $E = K(\zeta_{q_1})$ over $K = \mathbb{Q}(\sqrt{-d})$, with $f$ infinite places and $x^{11} \leq f \leq x^{12}$; the integer $M = p_0 p_1 \in [b^{20}, b^{22}]$; and the prime level $N$ with $\log N \in [m \log b, 30\, m \log b]$. The unit of loss is $\mathrm{errorUnit} = f a \log^3 b$.

Theorem A speaks about the following objects. [The objects of the upper bound](/chapter/upper-bound-objects/) constructs them, and [Theorems A, B and C](/chapter/theorems-a-b-c/) recalls them.

1. The *source forms* are algebraic forms on the definite unitary group of a hermitian space $X_0$ of rank $k$ over $E$, with values in a Weyl module and with a fixed level. They form a complex vector space of dimension $D_X$.
2. The *source* $\mathrm{src}$ is the subspace of ramified source forms. At each of the $f$ primes $w$ of $E$ above $N$ that divide a fixed element $\pi$ with $\pi\bar\pi = N$, there is a scaling $z_w$ of order $N - 1$ modulo $w$. A source form is ramified if, for each such $w$, the sum of its translates by $z_w^i$, $0 \leq i < N - 1$, is $0$. The source is also the image of the operator $\prod_w (1 - z_w)$.
3. The *target* $T$ is a space of good forms on the unitary group of a hermitian space $Y_0$. The finite group $\bar G$, a product of groups $\mathrm{GL}_r(\mathbb{F}_w)$, acts on the forms on $Y_0$, and $e_0$ is a central idempotent of $\mathbb{C}[\bar G]$ that cuts out the good part.
4. The *Poincaré map* $\mathcal{P}$ sends a source form to the form on $Y_0$ that represents its Bessel period in the Petersson inner product.
5. For each $m$-fold twist $\vartheta$ there is an injective linear map $\Theta_\vartheta$ from $T$ to forms on the unitary group of a space $Y_m$: the chain of $m$ theta lifts for the twist $\vartheta$, from $Y_0$ to $Y_m$. The trivial twist is $1$, and $\Theta_1$ is its chain. For an automorphism $\sigma$ of $\mathbb{C}$, $\|\Theta_1 y\|_\sigma^2$ is the squared norm of the $\sigma$-conjugate of $\Theta_1 y$ ([twisted lattices](/chapter/twisted-lattices/)).
6. The letter $\iota$ runs over the pairs of a prime $\ell$ and a ring isomorphism $\mathbb{C} \cong \overline{\mathbb{Q}}_\ell$ onto an algebraic closure of $\mathbb{Q}_\ell$. The place of $\iota$ is the embedding $\mathbb{C} \to \mathbb{C}_\ell$ that it induces.

Lean: `New.PrimePadicIso` (New/Reduction/Lattices/Heights.lean).

**Definition (Integral ramified forms).** A ramified source form $\varphi$ is *integral* if for every $\iota$ its values are integral at $\iota$ for the Weyl lattice at every finite adelic point. The set of these forms is $\mathrm{src}_{\mathrm{int}}$.

Lean: `New.Data.integralRamified` (New/Reduction/ShortAndEnough.lean).

The set $\mathrm{src}_{\mathrm{int}}$ is not a complex subspace. For each $\iota$ the integral forms are a module over the valuation ring $\mathcal{O}_\iota$ of $\iota$, and $\mathrm{src}_{\mathrm{int}}$ is the intersection of these modules over all $\iota$.

**Definition (The normalized map).** For $s \in \bar G$ the linear map $s\mathfrak{p} : \mathrm{src} \to T$ is

$$s\mathfrak{p}\,\varphi = c_B \cdot \#\bar G \cdot e_0\, s\, \mathcal{P}(c_{ss}^{-1}\varphi).$$

Here $c_B > 0$ is the rational gain factor and $c_{ss} \in \mathbb{C}^\times$ is the seesaw constant. Section 3 recalls both.

Lean: `New.Data.normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

As $e_0$ is central in $\mathbb{C}[\bar G]$, the map $s\mathfrak{p}$ is the translate by $s$ of $\mathfrak{p} = 1\mathfrak{p}$. The factor $c_B$ divides out the divisibility of the chain of lifts at the small primes. The factor $c_{ss}^{-1}$ makes the seesaw identity of Section 3 an identity with constant $1$.

### The statement

The main amount and the total remainder are the numbers of [the prime sums](/chapter/prime-sums/):

$$\mathrm{mainAmount} = m k \sum_{\tau \in \Phi}\bigl(s_\infty(\kappa(\tau)) - s_{\mathrm{fin}}(\kappa(\tau), \tau)\bigr), \qquad \mathrm{rem} = \sum_{\tau \in \Phi_a}\bigl(s_{\mathrm{fin}}(a, \tau) - s_{\mathrm{main}}\bigr).$$

Here $\Phi$ is the set of the $f$ infinite places of $E$, $\Phi_a \subset \Phi$ is the set of $a$-places, $\kappa(\tau)$ is the weight at $\tau$ ($\kappa = b$ on the $b$-places and $\kappa = a/x_1$ elsewhere), $s_\infty(j) = \log j! + j \log(M/\Omega)$ is the size of a derivative of order $j$, and

$$s_{\mathrm{fin}}(y, \sigma) = \sum_{1 \leq \nu \leq a} \Lambda_K(\nu)\bigl(y/\nu - \kappa(-\nu\sigma)\bigr)_+, \qquad \Lambda_K(\nu) = \Lambda(\nu)\bigl(1 - \chi_K(\nu)\bigr),$$

is the prime sum that measures its divisibility. The number $s_{\mathrm{main}} = a(\log a - \frac1f\sum_\tau \log\kappa(\tau) + c_1)$ is the expected value of $s_{\mathrm{fin}}(a, \tau)$.

**Theorem (Theorem A (a), short forms).** The span over $\mathbb{C}$ of the set of $\varphi \in \mathrm{src}_{\mathrm{int}}$ such that

$$\|\Theta_1(s\mathfrak{p}\,\varphi)\|_\sigma^2 \leq \exp\bigl(\mathrm{mainAmount} - m\cdot\mathrm{rem} + f a \log^4 b\bigr)$$

for every $s \in \bar G$ and every automorphism $\sigma$ of $\mathbb{C}$ is all of $\mathrm{src}$.

Lean: `New.Data.span_short_integralRamified_eq_top` (New/Reduction/ShortAndEnough.lean).

**Theorem (Theorem A (b), small index).** Let $t$ be a finite subset of $\bar G$, and let $y_1, \dots, y_n$ be target forms such that for each $i$ there are $s \in t$ and $\varphi \in \mathrm{src}_{\mathrm{int}}$ with $y_i = s\mathfrak{p}\,\varphi$. Then the family $y$ has index at most

$$\#t \cdot \dim_{\mathbb{C}} \mathrm{src} \cdot 2 f a \log^3 b$$

in the target lattice.

Lean: `New.Data.indexLe_normalizedPoincare` (New/Reduction/ShortAndEnough.lean).

The index is the notion of [twisted lattices](/chapter/twisted-lattices/). The family $y$ has index at most $\delta$ if there are numbers $e(\ell) \geq 0$ with $\sum_{\ell \in U} e(\ell)\log\ell \leq \delta$ for every finite set $U$ of primes, such that for every $\iota$ above $\ell$ a square matrix over $\mathcal{O}_\iota$ carries $y$ into the target forms integral at $\iota$ with loss $e(\ell)$. A target form is integral at $\iota$ if $\Theta_\vartheta y$ is integral at $\iota$ for every $m$-fold twist $\vartheta$ whose modulus has norm prime to $\ell$.

Part (a) is a statement about all $\sigma$ at once, and it uses only the trivial twist. Part (b) is a statement about all $\iota$ at once, and it uses every twist of level prime to $\ell$. Part (b) needs no shortness.

The proof of part (b) uses one chosen function.

**Definition (The divisibility errors).** The function $\mathrm{err} : \mathbb{N} \to \mathbb{R}$ is a choice of the numbers $\mathrm{err}(p)$ of the theorem on the divisibility of the composite lift ([Theorem](/decl/New.Data.exists_err_gaugeLe_compositeLift/)).

Lean: `New.Data.divisibilityError` (New/Reduction/ShortAndEnough.lean).

**Remark (Formalization).** The definition is `D.exists_err_gaugeLe_compositeLift.choose`. Nothing is known about the chosen function except the four properties of the theorem. The proof of the theorem names a witness, the allowed losses of Section 3, but the definition does not unfold to it, and no later proof uses the witness. So every statement about $\mathrm{err}$ holds for every function with the four properties. The definition of $\mathrm{src}_{\mathrm{int}}$ quantifies over all pairs $\iota$ of a prime and an $\ell$-adic place of $\mathbb{C}$ (the type `PrimePadicIso`). The integral source forms at $\iota$ are the source forms of gauge at most $1$ (`New.Data.integralSourceForms`), and they depend on the place through an instance `PadicPlace ℓ`. The ramified forms are defined as the common kernel of the operators $\sum_{i < N-1} z_w^i$, and `New.Data.ramifiedSourceForms_eq_range` proves that they are the image of $\prod_w (1 - z_w)$.

### The sizes

The sizes in Theorem A are explicit. By [the prime sums](/chapter/prime-sums/), $\mathrm{mainAmount} \geq x^4 f a$. The error in part (a) is $f a \log^4 b$. As $(\log b)^{100} \leq x$, we have $\log^4 b \leq x^{1/25}$, so the error is at most $x^{-3.96}$ times the main amount. The error in part (b) is $2 f a \log^3 b$ per dimension of the source and per translate. Theorem B chooses the translates with $\#t \cdot \dim\mathrm{src} \leq 5\, d_T \log(1 + 2b^2)$, where $d_T = \dim T$. As $\log(1 + 2b^2) \leq 3\log b$, the index of part (b) is then at most $30\, d_T\, f a \log^4 b$.

The number $m\cdot\mathrm{rem}$ is not small in general. Each prime sum $s_{\mathrm{fin}}(a, \tau)$ lies between $0$ and $4 a \log x_1$, as only the $\nu \leq x_1$ contribute, and $s_{\mathrm{main}}$ has the same order. So the trivial bound for $|m\cdot\mathrm{rem}|$ has the order $m\,\#\Phi_a\, a \log b$. The main inequality asks for $f a \log^5 b$, and $f = \#\Phi_a\, \varphi(q_0)$. So the argument must save about the factor $m \geq \sqrt{x}$ over the trivial bound. Theorem A is one step toward that bound. It does not bound $\mathrm{rem}$ by itself.

### A sketch of the proof

Take a short integral source form $\varphi$. The seesaw identity replaces $\Theta_1(\mathcal{P}\varphi)$ by a composite lift $B_1\varphi$ along an upper chain of lifts, on which the theta kernels act on $\varphi$ directly. The archimedean size bounds every conjugate of $B_1\varphi$ by $\mathrm{mainAmount} - m\cdot\mathrm{rem} + 2\sum_p\mathrm{gain}_p\log p$, plus errors, where $\mathrm{gain}_p$ is the divisibility at the small nonsplit prime $p$. The divisibility says that $B_\vartheta\varphi$ is divisible by $p^{\mathrm{gain}_p - \mathrm{err}(p)}$ on a submodule of small colength. The gain factor $c_B$, about $\prod_p p^{-\mathrm{gain}_p}$, keeps the images integral, and its square cancels the term $2\sum_p\mathrm{gain}_p\log p$. The colengths give the index of part (b).

### The plan of the chapter

Section 2 works out a model case: the theta series of an imaginary quadratic field, whose coefficients are rational integers, divisible at the nonsplit primes, and small. Section 3 states the three inputs. Section 4 proves Theorem A from them and adds up the errors. Section 5 gives the dependency diagram of the chapters of Volume 9, with one paragraph for each chapter, and the prerequisites from Volumes 3, 4, 5 and 6. Section 6 has exercises and notes.
