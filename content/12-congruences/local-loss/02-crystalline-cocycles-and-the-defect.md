---
title: Crystalline cocycles and the defect
lean:
  - New/Congruences/LocalLoss/CrystallineCocycles.lean
decls:
  - New.Selmer.matrixLattice
  - New.Selmer.finrank_crysCocycles_eq_add_neg_jumps
  - New.Selmer.normLength_dualDefect_le_of_hasCupExponent
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Crystalline cocycles and the defect

This section proves two general facts on crystalline cocycles over a coefficient ring $O$. The first is the rank of $Z_f(L)$ over $O$, in terms of the jumps of $L$ at the complex embeddings of $E$. The second turns a *cup exponent*, a power of $\ell$ that carries $Z_f(L)$ into the cup orthogonal, into a bound for the dual defect. Every bound of [Section 4](/chapter/local-loss/#three-regimes-of-the-prime) in the first two regimes ends with the second fact.

### Background

We recall the objects of [local duality, crystalline cocycles](/chapter/local-duality/#duality-for-crystalline-cocycles), one line each. Let $\Gamma$ be a group with a map $j : \Gamma \to G_\ell$ with open image, and $L$ a lattice over $O$ with an action $\rho$ of $\Gamma$.

- $L$ is *potentially crystalline* if $B_{\max} \otimes L$ is spanned by the elements fixed by all $g$ near $1$. It then has a multiset of Hodge-Tate *jumps* at each $\mathbb{Z}_\ell$-algebra map $\gamma : O \to \mathbb{C}_\ell$. We write $\mathrm{jump}(L, \gamma, u)$ for the multiplicity of $u$.
- $Z_f(L)$ is the $O$-module of maps $c : \Gamma \to L$ such that $c$ is a coboundary in $B_{\max} \otimes L$.
- For a filter $F$ on $\Gamma$, sets $U(\gamma) \subset \mathbb{Z}$ and conditions $K(s)$ on polynomials, the class $\mathrm{InClass}(F, K, U)$ consists of the lattices $Y$ that are admissible along $F$ and the filter near $1$, whose jumps at $\gamma$ with nonzero multiplicity lie in $U(\gamma)$, and on whose periods $Q(s) = 0$ for $s$ in inertia with $K(s)(Q)$. Members are potentially crystalline. The class $\mathrm{InClass}(\top, \bot, U)$ is the crystalline class with jumps in $U$.
- For a class $\mathcal{Q}$, the *cup orthogonal* $\mathrm{Orth}_{\mathcal{Q}}(L)$ is the set of maps $c : \Gamma \to L$ whose cup product with every crystalline cocycle of every $Y \in \mathcal{Q}$, under every pairing $Y \times L \to \mathbb{Z}/\ell^n(1)$ of the allowed form, is a coboundary.
- The *dual defect* is $\delta_{\mathcal{Q}}(L) = \mathrm{relLen}(Z_f(L), \mathrm{Orth}_{\mathcal{Q}}(L))$, the length of $Z_f(L)/(Z_f(L) \cap \mathrm{Orth}_{\mathcal{Q}}(L))$, in $\mathbb{N} \cup \{\infty\}$. It is $0$ if and only if $Z_f(L) \subset \mathrm{Orth}_{\mathcal{Q}}(L)$.
- $L$ has *cup exponent* $e$ for $\mathcal{Q}$ if $\ell^e x \in \mathrm{Orth}_{\mathcal{Q}}(L)$ for every $x \in Z_f(L)$. A cup exponent $e$ is a cup exponent $e'$ for every $e' \geq e$.

The *normalised length* $\lambda_O$ takes a length over $O$ to a value in $[0, \infty]$, scaled so that $O/\ell O$ has length $1$. Thus $\lambda_O(\mathrm{length}(O/\ell^k)) = k$. The *Bloch-Kato rank formula* of [period rings](/chapter/period-rings/#the-bloch-kato-rank-formula) says: if $L$ is a potentially crystalline $\mathbb{Z}_\ell$-lattice with jump multiset $K$ over $\mathbb{Z}_\ell$, then $\mathrm{rank}_{\mathbb{Z}_\ell} Z_f(L) = \mathrm{rank}_{\mathbb{Z}_\ell} L + [G_\ell : j(\Gamma)] \cdot \#\{u \in K : u < 0\}$.

The source cites S. Bloch and K. Kato, *L-functions and Tamagawa numbers of motives*, Grothendieck Festschrift I (1990), Proposition 3.8 and Corollary 3.8.4, for the rank formula. The classical form is $\dim H^1_f(\mathbb{Q}_\ell, V) = \dim H^0(\mathbb{Q}_\ell, V) + \dim D_{\mathrm{dR}}(V)/\mathrm{Fil}^0$. The module $Z_f$ is a module of cocycles, not of classes, so the coboundaries add $\mathrm{rank}\,V - \dim H^0$, and the sum is the formula above.

### Matrix lattices

**Definition (Matrix lattice).** For a ring $R$ and a matrix representation $\rho : \Gamma \to \mathrm{GL}_n(R)$, the *matrix lattice* of $\rho$ is $R^n$ with $\Gamma$ acting by $g \cdot x = \rho(g) x$.

Lean: `New.Selmer.matrixLattice` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

All global lattices of the argument are matrix representations. Their restrictions to decomposition groups in [Section 6](/chapter/local-loss/#local-lattices) and the lattices of [Section 7](/chapter/local-loss/#tate-duality-and-ribet-cocycles) are matrix lattices.

### The rank over the coefficient ring

Let $E$ be a CM field that contains a primitive $5040$-th root of unity, and $e : E \to \bar{\mathbb{Q}}_\ell$ an embedding. Fix the isomorphism $\iota : \mathbb{C} \cong \bar{\mathbb{Q}}_\ell$ of the source. For $g \in G_\ell$, write $c_g : O \to \mathbb{C}_\ell$, $x \mapsto g(x)$, and $\sigma_{e,g} = \iota^{-1} \circ g^{-1} \circ e$. The map $j$ is a *completion group* for $e$ if it is an open embedding onto the elements of $G_\ell$ that fix $e(E)$. Both notions are in [weights, signs and b-places](/chapter/main-summands/#weights-signs-and-b-places). There, two facts are proved: every $\mathbb{Z}_\ell$-algebra map $O \to \mathbb{C}_\ell$ is some $c_g$, and $\sigma_{e,g} = \sigma_{e,g'}$ if and only if $gg'^{-1} \in j(\Gamma)$, so that the number of distinct $\sigma_{e,g}$ is $[G_\ell : j(\Gamma)]$.

**Theorem (Rank of crystalline cocycles).** Let $j$ be a completion group for $e$, and let $L$ be a potentially crystalline lattice over $O$. Let $J(\sigma)$ be a multiset of integers for each complex embedding $\sigma$ of $E$. Suppose that for each $g \in G_\ell$ the jumps of $L$ at $c_g$ are $J(\sigma_{e,g})$. Then
$$\mathrm{rank}_O Z_f(L) = \mathrm{rank}_O L + \sum_{\sigma \in \{\sigma_{e,g} : g \in G_\ell\}} \#\{u \in J(\sigma) : u < 0\},$$
where the count is with multiplicity.

Lean: `New.Selmer.finrank_crysCocycles_eq_add_neg_jumps` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* The idea is to apply the rank formula over $\mathbb{Z}_\ell$ and count the jumps in two ways.

For each map $\varphi : O \to \mathbb{C}_\ell$ choose $s_\varphi \in G_\ell$ with $c_{s_\varphi} = \varphi$, and let $K(\varphi)$ be the jumps of $L$ at $\varphi$. Over $\mathbb{Z}_\ell$, the jumps of $L$ are $\sum_\varphi K(\varphi)$. By the hypothesis, $K(c_g) = J(\sigma_{e,g})$ for each $g$.

Two sums are invariant. For fixed $g$, the map $\varphi \mapsto c_{g s_\varphi}$ is injective, since $g$ is injective, so it permutes the finite set of maps $O \to \mathbb{C}_\ell$. Hence $\sum_\varphi K(c_{g s_\varphi}) = \sum_\varphi K(\varphi)$. For each $\sigma$ in the set $\Sigma = \{\sigma_{e,g}\}$ choose $r_\sigma$ with $\sigma_{e, r_\sigma} = \sigma$. For fixed $g$, the map $\sigma \mapsto \sigma_{e, r_\sigma g}$ is injective on $\Sigma$, by the criterion for equal embeddings. So $\sum_{\sigma \in \Sigma} J(\sigma_{e, r_\sigma g}) = \sum_{\sigma \in \Sigma} J(\sigma)$.

Now sum $K(c_{r_\sigma s_\varphi})$ over $\sigma \in \Sigma$ and $\varphi$. Summing first over $\varphi$ gives $\#\Sigma \cdot \sum_\varphi K(\varphi)$, and $\#\Sigma = [G_\ell : j(\Gamma)]$. Summing first over $\sigma$, with $K(c_{r_\sigma s_\varphi}) = J(\sigma_{e, r_\sigma s_\varphi})$, gives $\sum_\varphi \sum_\sigma J(\sigma) = [O : \mathbb{Z}_\ell] \sum_{\sigma \in \Sigma} J(\sigma)$, as there are $[O:\mathbb{Z}_\ell]$ maps $\varphi$. Count the negative members on both sides:
$$[G_\ell : j(\Gamma)] \cdot \#\{\text{negative jumps over } \mathbb{Z}_\ell\} = [O : \mathbb{Z}_\ell] \sum_{\sigma \in \Sigma} \#\{u \in J(\sigma) : u < 0\}.$$
Multiply the claim by $[O : \mathbb{Z}_\ell]$. The ranks over $O$ become ranks over $\mathbb{Z}_\ell$. The rank formula over $\mathbb{Z}_\ell$ gives $\mathrm{rank}_{\mathbb{Z}_\ell} L + [G_\ell : j(\Gamma)]$ times the number of negative jumps, and the display turns this into $[O : \mathbb{Z}_\ell]$ times the right side of the claim. Cancel $[O : \mathbb{Z}_\ell] > 0$. $\square$

**Example.** Let $\Gamma = G_\ell$, so that the index is $1$, and $O = \mathbb{Z}_\ell$. For the trivial lattice $\mathbb{Z}_\ell$, with the single jump $0$, the theorem gives rank $1$. The coboundaries are $0$, and the crystalline classes are the unramified homomorphisms $G_\ell \to \mathbb{Z}_\ell$, a module of rank $1$. For $\mathbb{Z}_\ell(1)$, the Tate dual of the trivial lattice, the jump is $-1$ in the convention of the source, since a jump $u$ of $L^\vee(1)$ means that $-u-1$ is a jump of $L$. The theorem gives rank $2$: the coboundaries $g \mapsto (\chi(g) - 1)x$ give rank $1$, and the Kummer classes of the units of $\mathbb{Z}_\ell$ give the other.

### From a cup exponent to the defect

**Theorem (Exponent to defect).** Let $L$ be potentially crystalline over $O$, $\mathcal{Q}$ a class of lattices, $k \in \mathbb{N}$ and $y \geq 0$ a real number. Suppose $\mathrm{rank}_O L \cdot 2k \leq y$, and $L$ has cup exponent $k$ for $\mathcal{Q}$. Then
$$\lambda_O\big(\delta_{\mathcal{Q}}(L)\big) \leq [G_\ell : j(\Gamma)] \cdot y.$$

Lean: `New.Selmer.normLength_dualDefect_le_of_hasCupExponent` (New/Congruences/LocalLoss/CrystallineCocycles.lean).

*Proof.* Put $d = [G_\ell : j(\Gamma)]$. It is positive, since $j(\Gamma)$ is open in the compact group $G_\ell$. The module $Z_f(L)$ is finitely generated over $O$.

First we bound the rank of $Z_f(L)$. Let $K$ be the jumps of $L$ over $\mathbb{Z}_\ell$. The multiset $K$ has $\mathrm{rank}_{\mathbb{Z}_\ell} L$ members, so at most that many are negative. The rank formula over $\mathbb{Z}_\ell$ gives
$$\mathrm{rank}_{\mathbb{Z}_\ell} Z_f(L) \leq \mathrm{rank}_{\mathbb{Z}_\ell} L + d\,\mathrm{rank}_{\mathbb{Z}_\ell} L \leq 2d\,\mathrm{rank}_{\mathbb{Z}_\ell} L.$$
Divide by $[O : \mathbb{Z}_\ell]$: the rank $\rho$ of $Z_f(L)$ over $O$ is at most $2d\,\mathrm{rank}_O L$.

Next let $I = \ell^k O$. By the cup exponent, $I \cdot Z_f(L) \subset Z_f(L) \cap \mathrm{Orth}_{\mathcal{Q}}(L)$. So $Z_f(L)/(Z_f(L) \cap \mathrm{Orth})$ is a quotient of $Z_f(L)/I Z_f(L)$. The module $Z_f(L)$ is a submodule of a module of maps to a torsion-free module, so it is torsion free, hence free of rank $\rho$. Thus $Z_f(L)/IZ_f(L) \cong (O/\ell^k)^\rho$, of normalised length $\rho k$. Hence
$$\lambda_O(\delta_{\mathcal{Q}}(L)) \leq \rho k \leq 2d\,\mathrm{rank}_O L \cdot k \leq d y. \qquad \square$$

**Remark (Formalization).** The defect lies in $\mathbb{N} \cup \{\infty\}$ and the bound $y$ is a nonnegative real number. The theorem allows any $y \geq 2k\,\mathrm{rank}_O L$, so that later results can pass a bound of their own form. The factor $2$ comes from the crude bound of the number of negative jumps by the rank. It costs nothing in the argument, since the constants of [the data and its sizes](/chapter/data-and-sizes/) have room for it.

**Example.** If $k = 0$, the hypothesis says $Z_f(L) \subset \mathrm{Orth}_{\mathcal{Q}}(L)$, and the theorem gives $\lambda_O(\delta) \leq 0$ for $y = 0$. This agrees with the criterion that the defect is $0$ exactly when all crystalline cocycles are cup orthogonal.

The cup exponents in this chapter are large: they have the form $10^4 \cdot K \cdot (\text{a logarithm})$, with $K$ about $2\lambda/Q$. The theorem turns them into the term $\mathrm{rank}\,L \cdot \lfloor 2\lambda/Q \rfloor \cdot m$ of the bound of Section 4.
