---
title: The scaled Hecke operator and the low columns
lean:
  - New/UpperBound/Divisibility/MarkedPrimes.lean
decls:
  - New.Data.integralSourceForms
  - New.Data.heckeScalingExponent
  - New.Data.sum_heckeScalingExponent
  - New.Data.IsMarked.maxCompactAt_le_levelX
  - New.Data.IsMarked.scaledHeckeOperator
  - New.Data.IsMarked.card_mul_transferExponent_add_sum_lowColumns_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The scaled Hecke operator and the low columns

At each prime $\mathfrak l$ of a marked set, this section defines an operator $p^{A_{\mathfrak l}}T_{\mathfrak l, r_p}$ on source forms. The exponent $A_{\mathfrak l}$ is chosen so that the operator preserves integrality at $p$ in the argument of [divisibility prime by prime](/chapter/divisibility/). The section then proves a bound that compares the cost of the low columns at the places inducing $\Lambda$ with the loss allowed at $p$.

### Integral source forms

Source forms are the algebraic forms on $X_0$ of weight $(\kappa, e_0)$ that are fixed by the level $K_0$, from [columns and the composite lift](/chapter/upper-bound-objects/#columns-and-the-composite-lift). Let $\mathcal O_\iota = \{z \in \mathbb C : |\iota_p z|_p \le 1\}$. The gauge $\|\xi\|_g$ of [automorphic forms](/chapter/automorphic-forms/) is a $p$-adic size of a vector $\xi$ of the Weyl module at a finite adelic point $g$. A form $\varphi$ has *gauge at most $c$ at $d$*, written $\mathrm{GaugeLe}(d, c, \varphi)$, if $\|\varphi(g)\|_{gd} \le c$ for all $g$ ([Definition](/decl/New.GaugeLe/)).

**Definition.** The module of *integral source forms* is the $\mathcal O_\iota$-module of source forms $\varphi$ with $\mathrm{GaugeLe}(1, 1, \varphi)$.

Lean: `New.Data.integralSourceForms` (New/UpperBound/Divisibility/MarkedPrimes.lean).

### The scaling exponent

**Definition.** For a prime $\mathfrak l$ of $E$, the scaling exponent is

$$A_{\mathfrak l} = a \cdot \#\{\tau \in \Phi_a : w_\tau = \mathfrak l\},$$

where $\Phi_a$ is the set of a-places.

Lean: `New.Data.heckeScalingExponent` (New/UpperBound/Divisibility/MarkedPrimes.lean).

The factor $a$ is the length of the one row of the weight at an a-place, from [weights and lift diagrams](/chapter/upper-bound-objects/#weights-and-lift-diagrams). So $A_{\mathfrak l}$ is the total degree, in the variables at the a-places that induce $\mathfrak l$, of a vector of the Weyl module on $X_0$.

**Lemma.** For every finite set $\Lambda$ of primes, $\sum_{\mathfrak l \in \Lambda} A_{\mathfrak l} = a \cdot \#(\Phi_a \cap \Phi_\Lambda)$.

Lean: `New.Data.sum_heckeScalingExponent` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* The sets $\{\tau \in \Phi_a : w_\tau = \mathfrak l\}$, $\mathfrak l \in \Lambda$, are disjoint. Their union is the set of a-places $\tau$ with $w_\tau \in \Lambda$, which is $\Phi_a \cap \Phi_\Lambda$. $\square$

### The Hecke operator at a marked prime

The Hecke operator at a split prime is that of [Iwahori and Satake](/chapter/iwahori-satake/). For a split prime $w$ of $E$, let $K_w$ be the subgroup of the standard maximal compact subgroup of elements with component $1$ away from $w$ and $\bar w$ ([Definition](/decl/New.maxCompactAt/)). A vector is spherical at $w$ if $K_w$ fixes it. On spherical vectors, $T_{w, j}$ is the operator of the double coset of $\mathrm{diag}(\varpi 1_j, 1)$ in $\mathrm{GL}_n(E_w)$. If $K$ lies in the standard maximal compact subgroup and $v$ is spherical at $w$ and of level $K$, then $T_{w,j}v$ is of level $K$ (`New.heckeSplit_mem_levelSpace`).

The level $K_0$ of source forms contains the principal congruence subgroup of level $\pi_M\pi$, where $\pi_M\bar\pi_M = M$ and $\pi\bar\pi = N$ ([Lemma](/decl/New.Data.principalLevel_le_levelX/)).

**Lemma.** Let $\Lambda$ be marked and $\mathfrak l \in \Lambda$. Then $K_{\mathfrak l} \le K_0$ in the unitary group of $X_0$.

Lean: `New.Data.IsMarked.maxCompactAt_le_levelX` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* Let $v$ be a prime above $p$. If $\pi_M\pi \in v$, then $MN = \pi_M\bar\pi_M\pi\bar\pi \in v$, so $p \mid MN$. This contradicts Section 2, since $p < x_1$ is non-split. So neither $\mathfrak l$ nor $\bar{\mathfrak l}$ contains $\pi_M\pi$. An element of $K_{\mathfrak l}$ is integral everywhere and equal to $1$ away from $\mathfrak l$ and $\bar{\mathfrak l}$. At $\mathfrak l$ and $\bar{\mathfrak l}$ the number $\pi_M\pi$ is a unit, so the congruence modulo $\pi_M\pi$ asks nothing there. So the element lies in the principal congruence subgroup of level $\pi_M\pi$, and so in $K_0$. $\square$

**Definition (Scaled Hecke operator).** Let $\Lambda$ be marked and $\mathfrak l \in \Lambda$. The scaled Hecke operator at $\mathfrak l$ is the $\mathcal O_\iota$-linear map

$$\varphi \mapsto p^{A_{\mathfrak l}}\, T_{\mathfrak l, r_p}\,\varphi$$

on the space of source forms, where $r_p = \lceil \log_p m \rceil$.

Lean: `New.Data.IsMarked.scaledHeckeOperator` (New/UpperBound/Divisibility/MarkedPrimes.lean).

The definition needs two facts. The prime $\mathfrak l$ is split (Section 3), so $T_{\mathfrak l, r_p}$ is defined. A source form is fixed by $K_0 \ge K_{\mathfrak l}$, so it is spherical at $\mathfrak l$, and $T_{\mathfrak l, r_p}$ keeps it in level $K_0$. So the operator maps source forms to source forms.

**Remark (Formalization).** The operator is the complex linear map $p^{A_{\mathfrak l}}T_{\mathfrak l, r_p}$, restricted to source forms and then read as $\mathcal O_\iota$-linear by restriction of scalars. The definition does not claim that it maps integral source forms to integral source forms. That claim, with the scale $p^{A_{\mathfrak l}}$, is proved in [divisibility prime by prime](/chapter/divisibility/). The index $r_p$ is fixed for all primes of $\Lambda$.

### The low columns at the places inducing $\Lambda$

The next numbers are from [short columns and the gain](/chapter/short-columns-gain/). For $j < m$ and a place $\tau$, $L_j(\tau)$ is the number of columns at $\tau$ of height $h < n_{j+1}$ with $h \ne 1$. There it is proved that $L_j(\tau) \le \kappa(\tau) + x^{60}$ for $j < m$. The transfer exponent is $\nu_p = r_p f (n_m + r_p)$. The unit of loss at $p$ is

$$\mathrm{loss}(p) = f (\log b)^2 \frac{a}{p} \cdot \begin{cases} m & \text{if } p \equiv \pm 1 \pmod m, \\ 1 & \text{otherwise}, \end{cases}$$

and it is at least $f (\log b)^2 a/p$.

**Theorem (Cost of the low columns).** Let $j < m$, and let $\Lambda$ be a marked set of primes above $p$. Then

$$\#\Lambda \cdot \nu_p + r_p \sum_{\sigma \in \Phi_\Lambda} L_j(\sigma) \le \frac{\mathrm{loss}(p)}{m} + \#(\Phi_a \cap \Phi_\Lambda) \cdot \frac{a}{x_1}.$$

Lean: `New.Data.IsMarked.card_mul_transferExponent_add_sum_lowColumns_le` (New/UpperBound/Divisibility/MarkedPrimes.lean).

*Proof.* *Step 1: one place.* We prove, for each $\sigma \in \Phi_\Lambda$,

$$r_p L_j(\sigma) \le \frac{a}{pm} + [\sigma \in \Phi_a]\,\frac{a}{x_1}. \tag{1}$$

By Section 3, $\kappa(\sigma) = a/x_1$, so $L_j(\sigma) \le a/x_1 + x^{60}$. There are two cases.

If $p \le m$, then $a/(pm) \ge a/m^2$. The left side of (1) is at most $r_p(a/x_1 + x^{60})$, with $r_p \le \lceil\log_2 m\rceil$. The ratio $a/x_1$ is far smaller than $a/m^2$, and $x^{60}$ is far smaller than both. So (1) holds, whether or not $\sigma$ is an a-place. The source proves the inequality by the size automation of [the table of sizes](/chapter/data-and-sizes/#the-table-of-sizes), with the bound $p < x_1$.

If $p \ge m$, then $r_p = 1$. The odd number $o_0$ is at most $r_p = 1$ (a condition of exceptional primes), so $o_0 = 1$: the place $[-p]$ has class $1$ modulo $q_0$. The prime $w_\sigma$ is induced by an a-place $\tau$, so by Section 2 the place $\sigma$ lies in the orbit of $\tau$ under $[-p]$. All places of this orbit have the class of $\tau$ modulo $q_0$, so $\sigma$ is an a-place. It remains to show $r_p(a/x_1 + x^{60}) = a/x_1 + x^{60} \le a/(pm) + a/x_1$, that is $x^{60} \le a/(pm)$. This holds by the size automation, since $p < x_1$.

*Step 2: the sum.* Sum (1) over $\sigma \in \Phi_\Lambda$:

$$r_p \sum_{\sigma \in \Phi_\Lambda} L_j(\sigma) \le \#\Phi_\Lambda \frac{a}{pm} + \#(\Phi_a \cap \Phi_\Lambda)\frac{a}{x_1}.$$

The last term is the last term of the claim. By Section 3, $\#\Lambda \le f$, so $\#\Lambda\, \nu_p \le f^2 r_p (n_m + r_p)$. Since $\mathrm{loss}(p) \ge f(\log b)^2 a/p$, it remains to prove

$$f^2 r_p (n_m + r_p)\, p + \#\Phi_\Lambda \frac{a}{m} \le \frac{f a (\log b)^2}{m}.$$

Here $\#\Phi_\Lambda \le f$, and $f$, $r_p$, $n_m$, $p$ and $m$ are all small powers of $x$ or $x_1$ against the scale $a$. The source proves this last inequality by the size automation. $\square$

**Remark.** The bound has two terms. The term $\mathrm{loss}(p)/m$ is the share of one lift in the total loss at $p$. The term $\#(\Phi_a \cap \Phi_\Lambda)\,a/x_1$ is the cost of about $a/x_1$ low columns at each a-place that induces a prime of $\Lambda$. By the lemma on $\sum A_{\mathfrak l}$, the scaled Hecke operators at the primes of $\Lambda$ carry the total factor $p^{a\,\#(\Phi_a \cap \Phi_\Lambda)}$. The use of the two facts together is in [divisibility prime by prime](/chapter/divisibility/).

**Remark (Formalization).** The statement is an inequality of real numbers, with $\mathrm{loss}(p)/m$ a real quotient. The hypothesis $j < m$ is used only in the bound $L_j(\sigma) \le \kappa(\sigma) + x^{60}$. The instance `PadicPlace p` fixes the embedding $\iota_p$ that defines the induced primes.
