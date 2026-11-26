---
title: Theta lifts and every rank
lean:
  - Lib/GaloisRep/Main/ThetaLift.lean
  - Lib/GaloisRep/Main/AllRanks.lean
decls:
  - New.exists_theta_lift_heckePoly
  - New.AutChar.exists_pair_heckeCoeff_ne
  - New.GaloisRep.isGoodAt_hasJumpsAt_of_trace_eq_sub
  - New.GaloisRep.Attached.exists_attached_of_mul_prod
  - New.GaloisRep.sphericalCompat_std
  - New.Patching.Isotypic.galRep
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Theta lifts and every rank

Section 4 gives representations for forms of odd rank. This section removes the parity condition. A form of rank $n$ is lifted to rank $2n + 1$ by a theta lift. The Hecke polynomials of the lift are those of the form times $n + 1$ linear factors that come from Hecke characters. The representation of the lift then contains, at the level of traces, the wanted representation plus $n + 1$ characters. Two lifts with different characters let the source cancel the characters. The result is [the theorem on every rank](/decl/New.GaloisRep.sphericalCompat_std/).

### The textbook idea

Blasius and Rogawski, *Motives for Hilbert modular forms*, Invent. Math. 114 (1993), and Shin, *Galois representations arising from some compact Shimura varieties*, Ann. of Math. 173 (2011), reduce even rank to odd rank by endoscopic transfer: a representation of $U(n)$ is combined with a character of $U(1)$ to give a representation of $U(n+1)$ in odd rank, and the Galois representation of the result is split into its two parts. Harris, Soudry and Taylor, *$\ell$-adic representations associated to modular forms over imaginary quadratic fields I*, Invent. Math. 112 (1993), use theta lifts with a varying character for a similar purpose. The source uses a theta lift in place of endoscopic transfer. The theta lift from definite $U(n)$ to definite $U(n+s)$ with $s > n$ is in the convergent range, and Rallis' inner product formula shows that it is injective. See [the Rallis inner product formula](/chapter/rallis-inner-product/) and [theta lifts and the seesaw](/chapter/theta-lifts-seesaw/) in Volume 6.

### The theta lift and its Hecke polynomials

Let $b$ be a character of $U(1)(\mathbb A)/U(1)(E)$. It *has weight* $c$ if $b(u) = \prod_v u_v^{c_v}$ for every $u$ with integral finite part. Such a character, with the splitting character $\upsilon$ of the Weil data, gives algebraic Hecke characters

$$\theta_{k,j}(x) = b(x/\bar x)\,\upsilon(x)^{-k}\,|x|^{j - k/2}$$

for integers $k$ and $j$ (Lean: `New.AutChar.HasWeight.toAlgebraic`). For a split place $w$, write $\theta_{k,j}(w)$ for the value of $\theta_{k,j}$ at a uniformizer of $w$.

**Theorem (Theta lift and Hecke polynomials).** Let $E$ have Weil data. Let $f \neq 0$ be a form of rank $n \geq 1$ and weight $(\kappa, e)$, and let $b$ have weight $c \leq e$. Let $s > n$. Let $\kappa'_v(h)$ be $\kappa_v(h)$ for $h < n$, $e_v - c_v$ for $h = n$, and $0$ for $h > n$. Then there is a form $F$ of rank $n + s$ and weight $(\kappa', 0)$ such that:

1. $F \neq 0$;
2. $F$ is spherical at every place where $f$ is spherical;
3. at such a split place $w$, if $f$ has Hecke polynomial $P$, then $F$ has a Hecke polynomial $Q$ with

$$z^{\deg Q}\, Q(X/z) = P(X) \prod_{l < s} \bigl(X - \theta_{n+s,\,s-l}(w)\bigr), \qquad z = \theta_{s,s}(w).$$

Lean: `New.exists_theta_lift_heckePoly` (Lib/GaloisRep/Main/ThetaLift.lean).

In Lean, part 3 reads `Q.scaleRoots (heckeCoeff (hb.toAlgebraic s s) ∅ w) = P * ∏ l : Fin s, (X - C (heckeCoeff (hb.toAlgebraic (card n + s) (s - l)) ∅ w))`. The polynomial `Q.scaleRoots z` is $z^{\deg Q} Q(X/z)$: its roots are the roots of $Q$ multiplied by $z$, and its leading coefficient is that of $Q$. So the roots of $Q$, multiplied by $\theta_{s,s}(w)$, are the roots of $P$ and the $s$ values $\theta_{n+s,s-l}(w)$.

*Proof.* The Weil representation of the dual pair $(U(n), U(n+s))$, built from the Weil data, gives a theta kernel. At infinity the source chooses a Fock vector that lifts forms of weight $(\kappa, e)$ to forms of weight $(\kappa', 0)$. At the finite places it chooses a datum that is sharp for a level that fixes $f$, and the vacuum vector at every place where $f$ is spherical. Since $2n < n + s$, Rallis' inner product formula shows that the lift is injective on forms of that level. So $F \neq 0$. The vacuum vector is fixed by the maximal compact subgroup at $w$, so $F$ is spherical where $f$ is. The Hecke eigenvalues of the lift at $w$ come from those of $f$, rescaled, times a $q$-Pochhammer factor for the $s$ new steps. $\square$

The extra factors in part 3 are the model case of [Section 1](/decl/New.isSplit_of_q_prime/): each is the Frobenius value of a Hecke character, and so of a character of the Galois group.

### Two disjoint strings of characters

**Lemma (Two characters with disjoint values).** Let $E$ have Weil data and let $e$ assign an integer to each infinite place. There are two characters $\mu_0, \mu_1$ of $U(1)(\mathbb A)/U(1)(E)$ with trivial tame part and weights $c_0, c_1$ such that:

1. $c_i \leq e$ at every infinite place;
2. for all integers $k, j, j'$ and every split finite place $w$, the value at $w$ of $\theta_{k,j}$ made from $\mu_0$ differs from the value at $w$ of $\theta_{k,j'}$ made from $\mu_1$.

Lean: `New.AutChar.exists_pair_heckeCoeff_ne` (Lib/GaloisRep/Main/AllRanks.lean).

Part 2 holds at every split place, not only at most places. So the two strings of extra roots never meet, and the Galois characters of the two strings are different.

### Cancelling the characters

**Lemma (Subtraction of characters).** Let $r$ be continuous with a non-degenerate trace form. Suppose that $\operatorname{tr} r = \operatorname{tr} \rho - \sum_l \operatorname{tr} \chi_l$ for a continuous $\rho$ and continuous characters $\chi_l$. Let $A$ be a place of $\Omega$. Suppose that $\rho$ and every $\chi_l$ are unramified or crystalline at $A$, with jumps $J + \sum_l j_l$ for $\rho$ and $j_l$ for $\chi_l$. Then $r$ is unramified or crystalline at $A$ with jumps $J$. Every polynomial that kills an element $s$ at $A$ for $\rho$ and for every $\chi_l$ also kills it for $r$.

Lean: `New.GaloisRep.isGoodAt_hasJumpsAt_of_trace_eq_sub` (Lib/GaloisRep/Main/AllRanks.lean).

*Proof.* The representations $r \oplus \bigoplus_l \chi_l$ and $\rho$ have the same trace, and $r$ has a non-degenerate trace form. The source carries the local properties through this equality of traces. The count of a jump in $J$ is its count in $J + \sum_l j_l$ minus its counts in the $j_l$. For the kill condition, all members of the family are killed by the same polynomial, and a sum of two killing polynomials kills, and so does a multiple of one. $\square$

**Theorem (Attached after cancellation).** Let $\rho_0$ and $\rho_1$ have rank $|n| + |T|$, and let $\rho_i$ be attached to the polynomials $P_w \prod_{l \in T} (X - c_{i,l}(w))$. Suppose that at most Frobenius data, $P_w$ is monic of degree $|n|$ and $\iota_\ell(c_{i,l}(w))$ is the value at the Frobenius element of a continuous character $\psi_{i,l}$. Suppose also that no $\psi_{0,l}$ is equal to a $\psi_{1,l'}$. Then some representation of rank $|n|$ is attached to $P$, and every representation $r$ attached to $P$ has trace $\operatorname{tr} \rho_i - \sum_l \psi_{i,l}$ for both $i$.

Lean: `New.GaloisRep.Attached.exists_attached_of_mul_prod` (Lib/GaloisRep/Main/AllRanks.lean).

*Proof.* Fix $g$. The trace of $\rho_i(g)$ is minus the coefficient of degree $|n| + |T| - 1$ of its characteristic polynomial. This is the limit of the same coefficient of $P_w \prod_l (X - c_{i,l}(w))$, and for monic products this coefficient is additive. So $\operatorname{tr}\rho_i(g) - \sum_l \psi_{i,l}(g)$ is the limit of $-\iota_\ell(P_{w,|n|-1})$, for both $i$, and the two differences agree. Since no $\psi_{0,l}$ equals a $\psi_{1,l'}$, a lemma on semisimple representations gives $r_0$ of rank $|n|$, with a non-degenerate trace form, whose trace is this difference (Lean: `New.IsTraceNondeg.exists_cancel_chars`). The traces of powers give $\det(X - \rho_0(s)) = \det(X - r_0(s)) \prod_l (X - \psi_{0,l}(s))$. Cancel the monic factor in the approximation for $\rho_0$. So $r_0$ is attached to $P$ (Lean: `New.GaloisRep.Attached.of_trace_sub`). Every attached $r$ has the same limit as its trace. $\square$

### Every rank

**Theorem (Every rank).** Let $E$ be a CM field with Weil data and a CM type, and let $n$ be a nonempty finite set. Let $w$ be a finite place. Then $\mathrm{SphericalCompat}$ holds for $E$, the index set $n$, rank $|n|$ and $w$. So every eigenform $f$ of weight $\kappa$ on the standard definite unitary group of rank $|n|$, with Hecke polynomials $P$, has an attached representation. If $f$ is spherical at $w$, every representation attached to $P$ is unramified or crystalline at each place of $\Omega$ over $w$, has the jumps of $\kappa$, and, if $w$ is split, its geometric Frobenius elements are killed by $\iota_\ell(P_w)$.

Lean: `New.GaloisRep.sphericalCompat_std` (Lib/GaloisRep/Main/AllRanks.lean).

*Proof.* Let $t = |n| + 1$, so that $|n| + t = 2|n| + 1$ is odd. Take $\mu_0, \mu_1$ from the lemma on disjoint values, with $e = \kappa_2$, the determinant part of the weight. Let $\theta_{i,l} = \theta_{|n|+t,\,t-l}$ made from $\mu_i$, for $l < t$, and let $\psi_{i,l}$ be its $\ell$-adic avatar. For each $i$, the theta lift of $f$ along $\mu_i$ is a nonzero form of odd rank $2|n| + 1$. By [the odd rank theorem](/decl/New.GaloisRep.sphericalCompat_of_odd/) it has an attached representation. After a twist by the avatar of $\theta_{t,t}$, this gives $\rho_i$ attached to $P_w \prod_l (X - \theta_{i,l}(w))$, with the local properties at $w$ if $f$ is spherical at $w$. The values of $\mu_0$ and $\mu_1$ differ at every split place, and Frobenius elements at most Frobenius data are dense, so no $\psi_{0,l}$ is equal to a $\psi_{1,l'}$. The theorem on cancellation gives an attached $r$, and the trace of every attached $r$ is $\operatorname{tr} \rho_0 - \sum_l \psi_{0,l}$. The characters $\psi_{0,l}$ are unramified at $w$ and have known jumps. So the lemma on subtraction gives the local clauses for $r$ from those of $\rho_0$. $\square$

### A worked example

Let $n = 2$, so $|n| = 2$ and $t = 3$. A form $f$ of rank $2$ lifts to rank $5$. At a split place $w$ where $f$ is spherical, write $P_w = (X - \alpha)(X - \beta)$. The lift along $\mu_i$ has a Hecke polynomial whose roots, after multiplication by $\theta_{3,3}(w)$, are

$$\alpha,\quad \beta,\quad \theta_{5,3}(w),\quad \theta_{5,2}(w),\quad \theta_{5,1}(w),$$

with $\theta_{5,j}(x) = \mu_i(x/\bar x)\,\upsilon(x)^{-5}\,|x|^{j - 5/2}$. The odd rank theorem gives $\rho_i$ of rank $5$. Its trace at a Frobenius element at $w$ is close to $\iota_\ell(\alpha + \beta + \sum_j \theta_{5,j}(w))$. For the two choices $i = 0, 1$ the last three terms are different at every split $w$. The wanted representation of rank $2$ has trace $\operatorname{tr}\rho_0 - \sum_j \psi_{0,j}$. Its characteristic polynomial at Frobenius elements is close to $\iota_\ell((X - \alpha)(X - \beta))$.

### Choosing one representation

Volume 12 needs a function, not an existence statement. The source defines it on isotypic spaces. An isotypic space is a space of forms cut out by a system of Hecke eigenvalues at almost all places.

**Definition (The chosen representation).** For an isotypic space $x$, let $t_x$ be a chosen system of Hecke eigenvalues that cuts out $x$ (Lean: `New.Patching.Isotypic.heckeEigenvalues`), and let $P_x$ be its Hecke polynomials. The representation $\rho_x$ is a chosen representation attached to $P_x$.

Lean: `New.Patching.Isotypic.galRep` (Lib/GaloisRep/Main/AllRanks.lean).

If $x$ contains a nonzero form, then $\rho_x$ is attached to $P_x$ (Lean: `New.Patching.Isotypic.attached_galRep`). The proof applies the theorem on every rank at an arbitrary place. The existence clause of $\mathrm{SphericalCompat}$ does not depend on the place.

**Remark (Formalization).** The definition of `Isotypic.galRep` is `Classical.epsilon (Attached x.heckePolyAt)`. If no representation is attached, for example if $x$ is the zero space, the value is an arbitrary homomorphism with no meaning. The eigenvalue system `Isotypic.heckeEigenvalues` is also a choice, made by `Exists.choose`. Two systems that cut out the same space agree at almost all places, so the choice changes $P_x$ only at finitely many places, and the notion "attached" ignores finitely many places. The representation $\rho_x$ is determined by $P_x$ only up to conjugation. Statements in Volume 12 that use $\rho_x$ use only its trace or properties that are invariant under conjugation. The theorem on every rank needs `[WeilData E]`, which is stronger than the root of unity condition of Section 4. The kill condition in the local clause has two forms. If $\ell$ is a unit at $A$, it says $P(r(s)) = 0$. If $A$ lies above $\ell$, it says that $P$ kills the Weil pairs of $s$ along each local datum at $A$, as in [the previous chapter](/chapter/attached-representations/).
