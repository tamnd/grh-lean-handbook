---
title: What the chapter proves
lean:
  - New/Determinant/Exchange/RealVectors.lean
  - New/Determinant/Exchange/RemovingPlanes.lean
  - New/Determinant/Exchange/VanishingDescends.lean
  - New/Determinant/Exchange/TheoremForPartners.lean
  - New/OneLift/ComparisonOperator/OneExchange.lean
  - New/OneLift/ComparisonOperator/ExchangeData.lean
  - New/OneLift/ComparisonOperator/DeterminantProducts.lean
  - New/Determinant/Exchange/ExplicitMatching.lean
decls:
  - New.Exchange.exchange_identity
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter finishes the exchange identity. [The first part](/chapter/exchange-identity-1/) reduced the identity for a *large triple* $V = V' \oplus W_1$ to a *period identity* over $[U(W_1)]$. This chapter proves the period identity with real vectors that it constructs, removes hyperbolic planes until it reaches the general pair, passes from the standard data to all matched data, and computes the size of the constant. At the end it states the identity for data modulo an ideal $\mathfrak{m}$, which is the form that the rest of the volume uses. The last sections give the forms of the identity that the comparison operator of [the plan](/chapter/theorem-c-plan/) needs: one exchange with a class sum, and the explicit matching with determinant products at the real places.

### The statement

We use the notation of [the first part](/chapter/exchange-identity-1/). Let $E$ be a CM field with Weil data. Let $W$, $V$ and $V'$ be hermitian spaces with bases indexed by $n$, $a$ and $b$, and with signs $s$, $t$ and $t'$ at the infinite places. Write $\operatorname{neg}(s)$ for the number of signs $-1$ of $s$. For a modulus $\mathfrak{m}$ and a function $\Phi$ on matrices over $O_E/\mathfrak{m}$, the datum $\operatorname{modDatum}(\Phi, x)$ has the real part $x$, the function $\Phi$ at the primes of $\mathfrak{m}$, and the vacuum at the other finite places. A character $\nu$ of $[U(1)]$ is *tame for* $(\mathfrak{m}, \mu, \chi)$ if $\mathfrak{m} \neq (1)$, $\nu$ has weight $\mu$, its tame part is ramified exactly at the primes of $\mathfrak{m}$, and the tame part gives the character $\chi$ of $O_E/\mathfrak{m}$. Write $\gamma = \nu^{-1}\upsilon^{\lfloor |n|/2 \rfloor}$ for the *rank twist* of $\nu^{-1}$, where $\upsilon$ is the splitting character of the Weil data on the norm one ideles. The number $L_{\mathfrak{m}}(\nu, e)$ is the product $L_*(e)$ of [the tower](/chapter/rallis-inner-product/#the-tower) for the set $S$ of primes of $\mathfrak{m}$.

**Theorem (The exchange identity).** Let $\sigma \colon b \sqcup a \simeq n$. Suppose that

1. $\operatorname{neg}(s) = \operatorname{neg}(t) + \operatorname{neg}(t')$,
2. $|a| = |b| + 2e$ with $e \in \mathbb{N}$,
3. $2\operatorname{neg}(s) + 2 \leq |n|$,
4. $|n| \leq 2\mu_\tau + 2\operatorname{neg}(s)$ at every infinite place $\tau$,

and let $v$ be a Schwartz vector for $(V', W)$. Then there are a real $C > 0$ and a Schwartz vector $x$ for $(W, V)$ with this property. For every modulus $\mathfrak{m}$ and every $\nu$ that is tame for $(\mathfrak{m}, \mu, \chi)$ there is $c \in \mathbb{C}$ such that

(a) $|c|^2 = C\, L_{\mathfrak{m}}(\nu, e)$ and $C\, L_{\mathfrak{m}}(\nu, e) \neq 0$;

(b) for all characters $\alpha$, $\alpha'$ of $[U(1)]$ whose space characters on $V$ and $V'$ have product $(\nu \circ (z \mapsto z/\bar z))^{-1}$, all matched functions $\Phi$, $\Psi$ modulo $\mathfrak{m}$ for $\chi$ and $\sigma$, and all $g \in U(W)(\mathbb{A})$,
$$\int_{[U(V)]} \theta^{W,V}_{\gamma, \alpha}\bigl(\operatorname{modDatum}(\Phi, x)\bigr)(g, h)\, dh = c \int_{[U(V')]} \theta^{V',W}_{\alpha', \gamma}\bigl(\operatorname{modDatum}(\Psi, v)\bigr)(h, g)\, dh.$$

Lean: `New.Exchange.exchange_identity` (New/Determinant/Exchange/TheoremForPartners.lean).

The vector $x$ and the constant $C$ are chosen before $\mathfrak{m}$ and $\nu$. Only the modulus of $c$ is given. Section 5 proves the theorem.

### What the chapter uses

From [the first part](/chapter/exchange-identity-1/) the chapter uses matched functions, the equivariant difference, the vanishing on matched data, the theorem on cone images, the theorem on equal ranks and the theorem "exchange from periods". From [the tower](/chapter/rallis-inner-product/#the-tower) of Volume 6 it uses the products $L_*(e)$ and $L^\sharp(z)$ with their recursions, the zeta integral, the theorem on one plane and the functional equation on a real interval. From [the Weil representation](/chapter/weil-representation/) it uses the Fock model, the real Weil action and the mixed model of a splitting. From [adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/) it uses the theorem of Witt and the automorphic quotients with their measures. No file of this chapter imports a file that the volume puts in a later chapter.

### The plan

The argument runs in this order.

1. Section 2 proves a smooth form of the theorem of Witt at the real places. With it, it builds real vectors $\Phi$ for $(X, V' \oplus W_1)$ and $\Lambda$ for $(X, V')$ that satisfy the period identity, with period the equal rank theta integral of a vector $v_1$. So the row-column exchange identity holds for the large triple, with the ratio $\ell = $ the equal rank ratio of $v_1$.
2. Section 3 removes one hyperbolic plane from the space $X$ and keeps the identity. The constant term along the plane changes the constant by $L^\sharp(z + 1)^2$, and the recursion of $L_*$ absorbs it. Induction removes any number of planes.
3. Section 4 proves that the vanishing of a theta integral on all standard data descends along hyperbolic planes. This uses the functional equation and the identity theorem for analytic functions.
4. Section 5 proves the theorem for partners: the identity for all matched data, the value of the equal rank ratio, and the theorem above.
5. Section 6 treats one exchange against a class sum, a reduction of class sums to row stabilizers, and the data of the three exchanges of the comparison operator.
6. Section 7 gives the explicit matching: the identity for a definite space $V$ with determinant products at the real places, and its inverse form.
7. Section 8 has the exercises and the notes.

### A sketch

The proof goes up a tower and then comes down. Fix $W$ of rank $|n|$, and a small partner $U$ of rank $|b|$. Put $W_1 = H \oplus W$, with $H$ a hyperbolic plane, and $X = H^{|b|} \oplus W_1$. So $X$ has $|b| + 1$ planes over $W$. On $X$ the source compares the large triple $(X, U \oplus W_1)$ with the pair $(X, U)$. There the period identity holds, by Section 2, and the theorem of the first part gives the row-column exchange identity. Then $|b| + 1$ planes are removed one at a time, from $X$ and from the large partner together, by Section 3. Each removal takes the constant term along an isotropic line. On the large side the constant term is a cone image times a constant $\gamma$, with $|\gamma|^2$ a ratio of two values of $L_*$. On the small side the constant term is the theta integral of the zero term. The result is the identity for $(W, V)$ and $(W, U)$ on the standard data.

The identity on the standard data passes to all matched data by the equivariant difference of the first part. The pair $(W, U^-)$ is turned into the pair $(U, W)$ by the adjoint of a datum. The size of the constant contains the equal rank ratio $r(z)$ of a vector $z$ for $(H \oplus W, H \oplus W)$. Section 5 shows that $r(z)$ is a nonzero constant $C_0$ for a good $z$. This is where Section 4 enters: if $r$ vanished, vanishing would descend to a definite space with no partner, where the theta integral of the vacuum is a volume and not zero.

**Remark (Formalization).** The statement asks $2\operatorname{neg}(s) + 2 \leq |n|$. The proof uses the margin $+2$ only once: with hypothesis 4 it gives $\mu_\tau \geq 1$, which a split tame character needs. Elsewhere the proof needs only $2\operatorname{neg}(s) \leq |n|$. Section 5 gives the details.
