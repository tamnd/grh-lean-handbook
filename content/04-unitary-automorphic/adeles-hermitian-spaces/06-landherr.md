---
title: Landherr's theorem in the source
lean:
  - Lib/Adelic/Landherr.lean
  - Lib/ClassField/Global/NormTheorems.lean
decls:
  - New.hasse_norm
  - New.exists_norm_eq_of_forall_mem_closure
  - New.exists_norm_eq_sq_add_sq
  - New.exists_sq_add_sq_quadraticAlgebra
  - New.Core.exists_form_pos_and_unit
  - New.Core.exists_form_eq_one
  - New.Core.exists_rat_frame_of_adelic
  - New.Space.landherr
  - New.Space.exists_x_eq_and_ratEmbed_conj_eq
  - New.U.hasse_principle_coboundary
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Landherr's theorem in the source

Section 3 stated Landherr's theorem: a hermitian space over a CM extension $E/F$ is determined up to isometry by its dimension, its discriminant and its signatures at the real places of $F$. The usual proof uses the Hasse-Minkowski theorem for the trace form, or Galois cohomology (Kneser, TIFR Lectures 47 (1969), Section 5.5, which the source cites with Landherr, Abh. Math. Sem. Hamburg 11 (1936)). The source proves a special case by a different route. It uses Hasse's norm theorem for totally positive elements and strong approximation for the adeles. This section gives the steps.

Throughout, $E$ is a CM field with a CM type and the standing condition, and $F = E^+$. For a vector $u$ over $E$ and a hermitian matrix $K$, write $N(u) = u^* K u$, an element of $F$.

### Norms and sums of two squares

**Theorem (Hasse's norm theorem, totally positive case).** Let $L/K$ be a cyclic extension of number fields. Let $x \in K^\times$ be totally positive and a local norm at every finite place, in the sense that it lies in the closure of the norms of $L$ in each completion $K_v$. Then $x$ is a norm of an element of $L^\times$.

Lean: `New.hasse_norm` (Lib/ClassField/Global/NormTheorems.lean).

The classical theorem asks that $x$ be a local norm at every place. At a real place that ramifies in $L$ the local norms are the positive numbers, so a totally positive $x$ is a local norm at every real place. The source proves the theorem from its own class field theory, which [class field theory](/chapter/class-field-theory/) describes.

**Proposition (Sums of two squares).** Let $M$ be a number field and let $x \in M$ be totally positive and a sum of two squares in the closure, at each finite place of $M$. Then $x$ is a sum of two squares in $M$.

Lean: `New.exists_norm_eq_of_forall_mem_closure` (Lib/Adelic/Landherr.lean).

*Proof.* If $-1$ is a square in $M$, every element is a sum of two squares, since $x = ((x+1)/2)^2 + (i(x-1)/2)^2$. Otherwise $M(\sqrt{-1})/M$ is cyclic of degree $2$, its norms are the sums of two squares, and Hasse's norm theorem applies. $\square$

**Proposition.** The norm from $E$ to $F$ of every element of $E$ is a sum of two squares in $F$.

Lean: `New.exists_norm_eq_sq_add_sq` (Lib/Adelic/Landherr.lean).

*Proof.* Under the standing condition $E = F(i)$ with $i^2 = -1$. For $x = a + bi$ with $a, b \in F$ the norm is $\bar x x = a^2 + b^2$. $\square$

This is the step where the source uses the root $i$. It turns local questions about norms from $E$ into questions about sums of two squares, which keep their form over an extension of $F$.

**Proposition.** Let $p, q, B \in F$, let $p$ be totally positive, and let $S$ be a finite set of finite places of $E$ such that $p$ is a unit outside $S$ and $q$ is a unit at the places of $S$ and of $\bar S$. Then $p$ is a norm from the algebra $A[X]/(X^2 + 1)$, where $A = F[Y]/(Y^2 - (qp - B^2))$.

Lean: `New.exists_sq_add_sq_quadraticAlgebra` (Lib/Adelic/Landherr.lean).

*Proof.* If $\mu = qp - B^2$ is a square in $F$, work in $F$. If not, work in the field $F(\sqrt\mu)$. In both cases the previous propositions show that $p$ is a sum of two squares locally at every finite place, from the hypotheses on the valuations of $p$ and $q$. The sums of two squares proposition then makes $p$ a global sum of two squares. $\square$

### Representing one

**Proposition (Positive and unit values).** Let $K$ be an $n \times n$ matrix over $E$, let $z$ be an adelic vector with $z^* K z = 1$, and let $S$ be a finite set of finite places. Then there is a rational vector $u$ such that $N(u)$ has positive real part under every embedding of the CM type and is a unit at the places of $S$ and $\bar S$.

Lean: `New.Core.exists_form_pos_and_unit` (Lib/Adelic/Landherr.lean).

*Proof.* The two conditions define an open set of adeles that contains $N(z) = 1$. By strong approximation, $z$ is the limit of vectors $u + y$ with $u$ rational and $y$ supported at the finite places outside $S \cup \bar S$. The term $y$ does not change the value at the places that the conditions involve. $\square$

**Theorem (Hasse principle for representing one).** Let $K$ be a hermitian matrix over $E$, possibly degenerate. If $z^* K z = 1$ for an adelic vector $z$, then $w^* K w = 1$ for a vector $w$ over $E$.

Lean: `New.Core.exists_form_eq_one` (Lib/Adelic/Landherr.lean).

*Proof.* Take $u$ by the previous proposition with $S = \emptyset$. Then $N(u)$ is totally positive. Let $S$ be the finite set of places where $N(u)$ is not a unit, and take $v$ with $N(v)$ a unit at $S$ and $\bar S$. Put $2B = u^* K v + v^* K u$ and $\mu = N(v)N(u) - B^2$. The previous proposition, with $p = N(u)$ and $q = N(v)$, writes $N(u)$ as a sum $(p_1 + r_1\sqrt\mu)^2 + (p_2 + r_2\sqrt\mu)^2$ with $p_1 r_1 + p_2 r_2 = 0$. With $i$ from the standing condition, these coefficients give an explicit $w$ in the span of $u$ and $v$ with $N(w) = 1$. $\square$

The proof reduces the question to the binary hermitian form on the span of $u$ and $v$. Only the local conditions at the finitely many places of $S$ enter, and the norm theorem is applied to one element.

**Theorem (Hasse principle for partial frames).** Let $J$ be a hermitian matrix over $E$, possibly degenerate, let $s$ be signs, let $t \subseteq n$, and let $D$ be the diagonal matrix with $s_i$ at $i \in t$ and $0$ elsewhere. If $X^* J X = D$ for an adelic square matrix $X$, then $A^* J A = D$ for a matrix $A$ over $E$.

Lean: `New.Core.exists_rat_frame_of_adelic` (Lib/Adelic/Landherr.lean).

*Proof.* Induction on $t$. For a new index $j$, column $j$ of $X$ times the sign $s_j$ has norm $1$ for $s_j J$. The previous theorem gives a rational $w$ with $w^* J w = s_j$. Replace $J$ by its projection $J'$ to the orthogonal complement of $w$. Shear $X$ so that its column $j$ becomes $0$, and change its other columns so that the Gram matrix for $J'$ is the old one for the indices of $t$. The induction hypothesis gives a rational frame for $J'$. Project its columns to the orthogonal complement of $w$ and put $w$ in column $j$. $\square$

### Landherr's theorem

**Theorem (Landherr, case of the source).** Let $V$ and $W$ be spaces with the same signs $s$. Then $a^* J_V a = J_W$ for some $a \in \mathrm{GL}_n(E)$.

Lean: `New.Space.landherr` (Lib/Adelic/Landherr.lean).

*Proof.* It suffices to show that $J_V$ is congruent over $E$ to $\mathrm{diag}(s)$, the matrix of the signed space. The adelic matrix $X = x_V x_s^{-1}$ has $X^* J_V X = \mathrm{diag}(s)$, since both points give the standard form. Apply the previous theorem with $t = n$. The resulting $A$ is invertible, since $A^* J_V A = \mathrm{diag}(s)$ is. $\square$

**Theorem (Landherr for spaces with a point).** Let $V$ and $W$ be spaces with the same signs $s$. Then there are $a \in \mathrm{GL}_n(E)$ with $a^* J_V a = J_W$ and $g \in G$ with $x_W = a^{-1} x_V g$. For every $\gamma \in U(J_W)(E)$,
$$x_V^{-1}(a\gamma a^{-1})x_V = g \,(x_W^{-1}\gamma x_W)\, g^{-1}.$$
So the rational points of $V$ and of $W$ are conjugate in $G$: $\Gamma_V = g \Gamma_W g^{-1}$.

Lean: `New.Space.exists_x_eq_and_ratEmbed_conj_eq` (Lib/Adelic/Landherr.lean).

*Proof.* Take $a$ from the previous theorem. Then $a x_W$ is a second point of $J_V$, so $g = x_V^{-1} a x_W$ preserves the standard form and lies in $G$. The formula for $\gamma$ follows by substitution. $\square$

**Remark (Formalization).** The classical theorem covers all hermitian spaces over $E/F$. The source proves it only for spaces in the sense of Section 4: identity form at every finite place, and the same signature at every infinite place. For such spaces the classical invariants agree when the signs agree. The discriminant is a local norm at every finite place, by the point, and its sign at each real place is $(-1)^q$, where $q$ is the number of signs $-1$. So the statement of the source is a special case of the classical one. The proof does not use Hasse-Minkowski. It uses Hasse's norm theorem for the extension $M(\sqrt{-1})/M$ of a number field $M$, strong approximation, and the root $i$ of the standing condition. The source states the theorem with the standing condition, which the classical theorem does not need.

**Remark (Formalization).** The source proves Landherr's theorem by representing $1$ and splitting off one vector at a time. It does not prove the local classification of Section 3, nor the fact that the classical invariants determine the local spaces. The spaces of the source carry the local data in their point, so the local classification is not needed.

### Where the argument uses it

In the source, Landherr's theorem enters through the second form, `New.Space.exists_x_eq_and_ratEmbed_conj_eq`. It is used in Lib/Adelic/TraceFormula/TraceComparison.lean in Lib/Weil/Construction/CanonicalTheta.lean, and in New/Determinant/Exchange/StableSpacesStandardData.lean and New/Determinant/Exchange/RemovingPlanes.lean. In each case it replaces a space by another space with the same signs, at the cost of a conjugation in $G$. Section 5 used the first form for the existence of splittings. The theorem also gives the Hasse principle for unitary cocycles that the base change argument of the source uses, in Lib/GaloisRep/BaseChange/TwistedTraceIdentity.lean.

**Theorem (Hasse principle for unitary cocycles).** Let $E'/E$ be a Galois extension of CM fields of prime degree $\ell$, let $\sigma$ generate its group, and let $E$ have a CM type and the standing condition. Let $s \in U_n(E')$, with $U_n$ the group of $g$ with $g^* g = 1$, and suppose that $s = u\,\sigma(u)^{-1}$ for some $u \in G_f(E')$ and that $s\,\sigma(s) \cdots \sigma^{\ell - 1}(s) = 1$. Then $\sigma(g) = s^{-1} g$ for some $g \in U_n(E')$.

Lean: `New.U.hasse_principle_coboundary` (Lib/Adelic/Landherr.lean).

*Proof.* By Hilbert 90 for $\mathrm{GL}_n$, the cocycle $s$ is a coboundary in $\mathrm{GL}_n(E')$: $s = b\,\sigma(b)^{-1}$ for some invertible $b$. Since $s$ is unitary, the matrix $J = b^* b$ is fixed by $\sigma$, so it comes from a hermitian matrix over $E$. Since $u$ and $b$ both split $s$, the matrix $u^{-1} b$ is fixed by $\sigma$ and comes from the finite adeles of $E$. With $b$ at the infinite places, it gives a point for $J$, so $J$ is a definite space over $E$. Landherr's theorem compares it with the standard space $I_n$ and gives $l$ over $E$ with $l^* J l = 1$. Then $g = bl$ is unitary, and $\sigma(g) = \sigma(b) l = s^{-1} b l = s^{-1} g$. $\square$

**Remark (Formalization).** This is the case of $H^1(\mathrm{Gal}(E'/E), U_n)$ that base change needs: a class that is trivial over the finite adeles is trivial. The classical statement follows from the Hasse principle for $H^1$ of unitary groups (Kneser, as above). The source proves it only for the definite form $1$ and for cyclic extensions of prime degree.
