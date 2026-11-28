---
title: "A model case: congruences and denominators"
lean:
  - New/Congruences/FirstOrder/DenominatorBound.lean
  - New/Congruences/FirstOrder/TraceRelations.lean
decls:
  - New.Selmer.IsLiftGenerator
  - New.Selmer.liftValuationBound
  - New.Selmer.exists_operator_ellVal_le_liftValuationBound
  - New.Selmer.exists_operator_det_clearingBound
status: drafted
drafted_by: writer@claude-opus-5-5
---
## A model case: congruences and denominators

This section shows in a small example why a denominator of a projection is a congruence, and why the source bounds it by a Selmer group. Then it states the bound of the source for one space of lifts.

### A lattice of rank two

Let $O = \mathbb{Z}[i]$ and let $L = O^2$, with the hermitian form $\langle y, y'\rangle = y_1 \overline{y'_1} + y_2 \overline{y'_2}$. Fix an integer $a \geq 1$ and put
$$u = (1, a), \qquad u' = (-a, 1), \qquad N = 1 + a^2 .$$
Then $\langle u, u'\rangle = -a + a = 0$ and $\langle u, u\rangle = \langle u', u'\rangle = N$. Let $Z = \mathbb{C} u$ be the line of $u$. It plays the part of the space of lifts, and $\mathbb{C} u'$ plays the part of the forms that are not lifts.

The orthogonal projection to $Z$ is $\mathrm{pr}_Z\, y = \langle y, u\rangle u/N$. For the first basis vector, $\mathrm{pr}_Z\, e_1 = u/N$. The integral vectors on $Z$ are the multiples $c u$ with $c \in O$, since the first coordinate of $u$ is $1$. So the projection of the integral vector $e_1$ has the denominator $N$: no smaller multiple of $u/N$ is integral.

The denominator is a congruence. We have
$$a u' - u = (-a^2 - 1, 0) = -N e_1, \qquad \text{so} \qquad a u' \equiv u \pmod{N}.$$
A vector of $Z$ and a vector orthogonal to $Z$ are congruent modulo $N$, and the integral vector $e_1 = (u - a u')/N$ has the projection $u/N$. Conversely, if an integral vector $y$ has a projection with the denominator $\ell^{e}$, then $\ell^{e}\,\mathrm{pr}_Z\, y$ is integral and congruent modulo $\ell^{e}$ to $-\ell^{e}(y - \mathrm{pr}_Z\, y)$, a vector orthogonal to $Z$.

Two cases show the size of the effect. For $a = 1$ and $\ell = 2$, the denominator is $2$, and $u = (1, 1)$ is congruent modulo $2$ to $u' = (-1, 1)$. For $a = 2$ and $\ell = 5$, the denominator is $5$, and $2u' = (-4, 2) \equiv (1, 2) = u$ modulo $5$.

### The index of the projected lattice

The Gram determinant of the lifts measures all denominators at once. Let $L_Z = L \cap Z$ be the lattice of integral vectors in $Z$, and let $L_Z^{\#} = \{z \in Z : \langle z, L_Z\rangle \subseteq O\}$ be its dual in $Z$.

**Proposition (Projections of a unimodular lattice).** Let $O$ be the ring of integers of an imaginary quadratic field with class number $1$, and let $L$ be a free $O$-lattice in a hermitian space $V$ with $\langle L, L\rangle \subseteq O$ and $L^{\#} = L$. For every subspace $Z$ of $V$, we have $\mathrm{pr}_Z(L) = L_Z^{\#}$. Thus the index of $L_Z$ in $\mathrm{pr}_Z(L)$ is the absolute norm of the Gram determinant of a basis of $L_Z$.

Not in the source. The source bounds the denominator of the projection directly, by an operator on $Z$ (the theorem on the bound for denominators below).

*Proof.* For $y \in L$ and $z \in L_Z$, we have $\langle \mathrm{pr}_Z\, y, z\rangle = \langle y, z\rangle \in O$, so $\mathrm{pr}_Z(L) \subseteq L_Z^{\#}$. Conversely, let $\varphi \in L_Z^{\#}$. The quotient $L/L_Z$ embeds in $V/Z$, so it has no torsion. Since $O$ is a principal ideal domain, $L_Z$ is a direct summand of $L$, and the $O$-linear map $z \mapsto \langle z, \varphi\rangle$ from $L_Z$ to $O$ extends to an $O$-linear map $\lambda : L \to O$. Since $L$ is unimodular, $\lambda = \langle \cdot, y\rangle$ for some $y \in L$. Then $\mathrm{pr}_Z\, y$ and $\varphi$ have the same inner products with $L_Z$. Since $L_Z$ spans $Z$, $\mathrm{pr}_Z\, y = \varphi$. For the index, the quotient $L_Z^{\#}/L_Z$ is isomorphic to $O/(\det G)$, where $G$ is the Gram matrix of a basis of $L_Z$, and this quotient has $|\mathrm{Nm}(\det G)|$ elements. $\square$

In the example, $L_Z = O u$, the Gram matrix is $(N)$, and the index is $N^2$, the norm of $N$ from $\mathbb{Q}(i)$ to $\mathbb{Q}$. The projected lattice $\mathrm{pr}_Z(L) = O u/N$ has the basis $u/N$, and an operator $\Lambda = N$ on $Z$ takes it into $L_Z$. Then $\det \Lambda = N$ on the line $Z$, which is the form of the condition in the definition of `ClearsProjection`. In general, an operator $\Lambda$ on $Z$ with $\Lambda(\mathrm{pr}_Z\, L) \subseteq L_Z$ has $\det \Lambda \in O$ divisible by the index, and the $\ell$-adic part of $\det \Lambda$ bounds the $\ell$-adic part of the Gram determinant.

The lattices of the source are not unimodular, and the forms are tested only against the integral forms orthogonal to the false lifts. The idea is the same. A bound for the projection becomes a bound for the Gram determinant of the lifts, and a congruence between a lift and a form orthogonal to the lifts is the only obstruction.

### From congruences to Selmer classes

The source bounds the congruences by Galois cohomology. The model for this is the theorem of Ribet.

**Theorem (Ribet).** Let $p$ be a prime and $k$ an even integer with $2 \leq k \leq p - 3$. If $p$ divides the Bernoulli number $B_k$, then the $\omega^{1-k}$-part of the $p$-part of the class group of $\mathbb{Q}(\mu_p)$ is not zero. Here $\omega$ is the Teichmüller character.

Not in the source. The source uses no Bernoulli numbers and no class groups of $\mathbb{Q}(\mu_p)$; it uses an algebraic form of Ribet's method (`New.Selmer.exists_isCommonRibetElement_addVal_le`, applied to Galois representations in `New.Selmer.ribet_columns`), which gives the bound for denominators below in terms of Selmer groups.

This is the main theorem of [Ribet 1976]. The proof has two steps. First, the divisibility $p \mid B_k$ gives a congruence modulo $p$ between an Eisenstein series and a cusp form. Second, the $p$-adic Galois representation of the cusp form is irreducible, but its reduction has the characters of the Eisenstein series as its factors. A suitable lattice in the representation gives a nonsplit extension of these characters, and this extension is a nonzero unramified class.

The source uses the same link in the other direction, and as a bound. A congruence modulo $\ell^{e}$ between a lift and a form orthogonal to the lifts gives, by the same construction, a class of order $\ell^{e}$ in a Selmer group of the main summand attached to the lift, twisted by the $\ell$-adic avatar of $\vartheta^{-1}$. If the Selmer group has length at most $e'$, then the congruences have depth at most $e'$, up to explicit losses. The losses come from the local conditions above $\ell$, from the places of the twist, and from the class groups and automorphisms of the data. This heuristic explains the form of the bound below.

**Remark (Formalization).** The model case is not in the source: it states neither the proposition on projections of a unimodular lattice nor Ribet's theorem, nor the heuristic. They only motivate the bound below.

### The lift generators

For a twist $\vartheta$, a descent pair $O$, an element $E$ of the group algebra and a subspace $Z$, the source gives a set of forms that span the space of lifts.

**Definition (Lift generators).** A form $y$ is a *lift generator* for $\vartheta$, $O$, $E$, $Z$ and a bound $\mathrm{sel}$ if:

1. $y \in Z$;
2. there is a type $c$ in lift setting for $O$ and $\vartheta$ such that $y$ is in the range of the projection to the type $c$, and this range lies in the image of $E$;
3. there are Hecke values $z$ with `O.HasLiftHeckePolynomial` $y$ $z$, a main summand $R$ for $z$ at a pair $V$ with $O.\mathrm{u1Char} = V.\mathrm{u1Char} \cdot \vartheta$, and $\gamma$, $s$ such that the twisted Selmer groups with divisible coefficients have length at most $\mathrm{sel}$ (`HasDivisibleSelmerLengthLe` $\vartheta.\mathrm{invAvatar}$ $R$ $\vartheta.Q$ $\gamma$ $s$ $\mathrm{sel}$).

Lean: `New.Selmer.IsLiftGenerator` (New/Congruences/FirstOrder/DenominatorBound.lean).

Section 6 defines main summands and the Selmer condition. Here it is enough that each generator carries a Galois representation with a short Selmer group.

### The bound for one space

**Definition (The valuation bound for a lift).** For a prime $\ell$, a descent pair $O$ with the index type $r$ and the rank difference $t' = O.\mathrm{rankDiff}$, and $\mathrm{ram}, \mathrm{sel} \in [0, \infty]$, put
$$\mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel}) = \mathrm{sel} + 2 t' \cdot \mathrm{ram} + \#r \cdot \mathrm{localDefectBound}(\ell) + \mathrm{denominatorError}(\ell).$$

Lean: `New.Selmer.liftValuationBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

The four terms have four sources. The term $\mathrm{sel}$ is the length of the Selmer group. The term $2t' \cdot \mathrm{ram}$ is the cost of the ramification of the twist, with $\mathrm{ram}$ a bound for the valuations $v_\ell(\psi(\sigma) - 1)$ at the tame generators. The term $\#r \cdot \mathrm{localDefectBound}$ is the local loss above $\ell$, one copy per row. The term $\mathrm{denominatorError}$ pays for the class groups, the level, the idempotent and the automorphisms. Section 5 defines the last two.

The $\ell$-adic valuation of the source is
$$\mathrm{ellVal}(x) = \begin{cases} \infty & \text{if } \|x\| = 0, \\ \max(0, -\log_\ell \|x\|) & \text{otherwise,}\end{cases}$$
for $x \in \overline{\mathbb{Q}}_\ell$, with values in $[0, \infty]$.

**Theorem (Bound for denominators).** Fix a prime $\ell$ and the isomorphism $\iota_\ell : \mathbb{C} \to \overline{\mathbb{Q}}_\ell$. Let $\vartheta$ be a twist with `IsAuxTwist` (badPlaces $D$ $\ell$) $\vartheta.Q$ $\vartheta.\mathrm{invAvatar}$ $\mathrm{ram}$, let $\mathrm{sel} \neq \infty$, and let $Z$ lie in the span of the lift generators for $\vartheta$, $O$, $E$, $Z$ and $\mathrm{sel}$. Then there is a linear map $\Lambda : Z \to Z$ such that:

1. $\Lambda$ preserves the eigenspaces of the Hecke polynomials;
2. every eigenvalue $\mu$ of $\Lambda$ has $\mathrm{ellVal}(\iota_\ell\, \mu) \leq \mathrm{liftValuationBound}(\ell, O, \mathrm{ram}, \mathrm{sel})$;
3. for every form $y$ that is integral at $\iota_\ell$ and orthogonal to the false lifts, the form $\Lambda(\mathrm{pr}_Z\, y)$ is integral at $\iota_\ell$.

Lean: `New.Selmer.exists_operator_ellVal_le_liftValuationBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

The proof is the subject of [the bound for denominators](/chapter/denominator-bound/). It chooses a basis of $Z$ among the lift generators. For each basis vector it takes an operator from Ribet's method to first order, diagonal in the basis. Then it takes one integral combination of these operators that works for all basis vectors.

**Theorem (The operator form with the clearing bound).** Fix $\ell$ and $\iota_\ell$. Let $\vartheta$ be a twist with `IsAuxTwist` (badPlaces $D$ $\ell$) $\vartheta.Q$ $\vartheta.\mathrm{invAvatar}$ $e'_\ell$, where $e'_\ell = \mathrm{twistError}(\ell)$, and let $Z$ lie in the span of the lift generators for the bound $e'_\ell$. Then there is a linear map $\Lambda : Z \to Z$ such that:

1. $\exp(-\dim Z \cdot \#r \cdot \mathrm{clearingBound}(\ell) \log \ell) \leq \|\iota_\ell(\det \Lambda)\|$;
2. for every form $y'$ that is integral at $\iota_\ell$ and orthogonal to the false lifts, the form $\Lambda(\mathrm{pr}_Z\, y')$ is integral at $\iota_\ell$;
3. for every form $y$ that is integral at every embedding into $\mathbb{C}_\ell$ and every $y'$ as in 2, we have $\|\iota_\ell \langle y, \Lambda(\mathrm{pr}_Z\, y')\rangle\| \leq 1$.

Lean: `New.Selmer.exists_operator_det_clearingBound` (New/Congruences/FirstOrder/DenominatorBound.lean).

*Proof.* If every lift generator is $0$, then $Z = 0$, and $\Lambda = 1$ satisfies all three conditions: the determinant of the identity of the zero space is $1$, and all projections are $0$. Otherwise, take a nonzero lift generator. Its type $c$ is in lift setting, so $1 \leq \#r \leq r$ and $t' \leq t$. Section 5 gives the arithmetic lemma
$$\mathrm{liftValuationBound}(\ell, O, e'_\ell, e'_\ell) + v_\ell(N_g) \leq \#r \cdot \mathrm{clearingBound}(\ell),$$
where $N_g$ is `D.chosenGroupOrder`. Take $\Lambda_0$ from the bound for denominators with $\mathrm{ram} = \mathrm{sel} = e'_\ell$, and put $\Lambda = N_g \Lambda_0$. Every eigenvalue of $\Lambda$ is $N_g \mu$ with $\mu$ an eigenvalue of $\Lambda_0$. Since $\mathrm{ellVal}$ of a product is at most the sum, and $\mathrm{ellVal}(N_g) = v_\ell(N_g)$, each eigenvalue of $\Lambda$ has $\mathrm{ellVal}$ at most $\#r \cdot \mathrm{clearingBound}(\ell)$. The determinant is the product of the $\dim Z$ eigenvalues, with multiplicity, so condition 1 holds. An integer multiple of an integral form is integral, so condition 2 holds. For condition 3, the inner product of $y$ with the integral form $\Lambda_0(\mathrm{pr}_Z\, y')$ can have a denominator, but the factor $N_g$ clears it. $\square$

The second theorem has the form of `New.Selmer.DenominatorLe` of Section 3, with $\beta = \mathrm{clearingBound}(\ell) \log \ell$. This is the result `New.Selmer.denominatorLe_clearingBound` of Section 6.

**Remark (Formalization).** The bounds take values in $[0, \infty]$, as elements of `ENNReal`. The bound $\mathrm{liftValuationBound}$ is infinite if $\mathrm{sel} = \infty$, and then condition 2 of the first theorem says nothing. So the first theorem asks for $\mathrm{sel} \neq \infty$. In the second theorem $\mathrm{sel} = e'_\ell$ is a finite real number. The error term $\mathrm{denominatorError}(\ell)$ is finite (`New.Selmer.denominatorError_ne_top`), and the clearing bound uses its real part, through `ENNReal.toNNReal`. Also $\mathrm{ellVal}$ is clipped at $0$: an element of norm larger than $1$ has $\mathrm{ellVal}$ equal to $0$. So the condition on eigenvalues does not bound their size from above. It only says that no eigenvalue is too divisible by $\ell$.
