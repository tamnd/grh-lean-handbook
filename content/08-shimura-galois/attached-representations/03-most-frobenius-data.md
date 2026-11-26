---
title: Most Frobenius data
lean:
  - Lib/GaloisRep/Main/Defs.lean
decls:
  - New.FrobeniusDatum
  - New.mostFrobenii
  - New.mostFrobeniiAt
  - New.tendsto_mostFrobeniiAt
  - New.tendsto_place_mostFrobenii
  - New.eventually_mostFrobenii
  - New.eventually_mostFrobenii_of_isOpenEmbedding
  - New.dense_of_mostFrobenii
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Most Frobenius data

The textbook says "for all Frobenius elements at almost all places". The source says "for most Frobenius data", and it makes this precise with a filter. This section defines the filter, compares it with the textbook phrase, and proves its basic properties. The main property is density: by Chebotarev, a property of most Frobenius elements holds on a dense subset of the Galois group. So the filter is not trivial, and limits along it are unique.

Throughout, $E$ is a number field inside $\Omega$, and $\Gamma_E = \mathrm{Gal}(\Omega/E)$ with its Krull topology. A place of $\Omega$ is a valuation subring $A$ of $\Omega$. For a finite place $w$ of $E$ and a place $A$ over $w$, an *arithmetic Frobenius* at $A$ for $q$ is an element $\sigma$ that keeps $A$ and acts as $x \mapsto x^q$ on $A$ modulo its maximal ideal ([Definition](/decl/New.IsFrob/), in [CM fields](/chapter/cm-fields/)).

### Frobenius data

**Definition (Frobenius datum).** A *Frobenius datum* for $E$ is a triple $(w, A, s)$ of:

1. a finite place $w$ of $E$ whose norm $q_w$ is a prime number;
2. a place $A$ of $\Omega$ over $w$;
3. an element $s \in \Gamma_E$ such that $s^{-1}$ is an arithmetic Frobenius at $A$ for $q_w$.

Lean: `New.FrobeniusDatum` (Lib/GaloisRep/Main/Defs.lean).

So $s$ is a *geometric* Frobenius. The source uses geometric Frobenius elements for all the comparisons with Hecke polynomials. This matches the convention of [class field theory](/chapter/class-field-theory/), where the Artin symbol of a uniformizer is a geometric Frobenius.

**Remark (Formalization).** The datum keeps only places of prime norm. These are places of degree one over $\mathbb{Q}$. A place whose norm is a proper prime power is never the place of a datum. By Chebotarev the places of degree one carry all the information, and the source never needs the others. For a fixed $w$ and $A$ the element $s$ is not unique: it is defined up to the inertia group at $A$, which in $\Gamma_E$ is never trivial.

### The filter

**Definition (Most Frobenius data).** A set $X$ of Frobenius data *contains most Frobenius data* if, for every nonempty open $V \subseteq \Gamma_E$, there is a nonempty open $O \subseteq V$ with this property: for all but finitely many places $w$, every datum $(w, A, s)$ with $s \in O$ lies in $X$. These sets form a filter $\mathcal{F}_E$ on Frobenius data. For $g \in \Gamma_E$, the filter $\mathcal{F}_E(g)$ is the infimum of $\mathcal{F}_E$ and the inverse image, under $(w, A, s) \mapsto s$, of the filter of neighbourhoods of $g$.

Lean: `New.mostFrobenii`, `New.mostFrobeniiAt` (Lib/GaloisRep/Main/Defs.lean).

The definition includes the proof that $\mathcal{F}_E$ is a filter. The set of all data qualifies: take $O = V$. A superset of a set that qualifies qualifies, with the same $O$. For the intersection of $X$ and $Y$, shrink twice. The set $X$ gives $O \subseteq V$, and the set $Y$, applied to the open set $O$, gives $O' \subseteq O$. For almost all $w$, data with $s \in O'$ lie in $X$, since $O' \subseteq O$, and they lie in $Y$. The union of two finite sets of exceptional places is finite.

A set in $\mathcal{F}_E(g)$ contains the data of a set in $\mathcal{F}_E$ whose Frobenius element lies in a neighbourhood of $g$. We write "for most data near $g$" for "along $\mathcal{F}_E(g)$".

### Comparison with the textbook

The textbook phrase is: for a finite set $S$ of places, for all $w \notin S$ and every Frobenius element at $w$. The following two examples show that the filter contains the textbook sets and more.

**Example.** For a finite set $S$ of places, the set of data whose place is not in $S$ contains most Frobenius data. For any $V$ take $O = V$, and let $S$ be the exceptional set. This is the next lemma.

**Lemma.** The place $w$ of a datum tends to the cofinite filter along $\mathcal{F}_E$: for every cofinite set $T$ of places, most data have their place in $T$. Hence, if a property $p$ of places holds for all but finitely many $w$, and $p(w)$ implies a property $q$ of every datum at $w$, then $q$ holds for most data.

Lean: `New.tendsto_place_mostFrobenii`, `New.eventually_mostFrobenii` (Lib/GaloisRep/Main/Defs.lean).

*Proof.* Let $T$ be cofinite. For a nonempty open $V$, take $O = V$. For every $w \in T$, which is all but finitely many $w$, every datum at $w$ has its place in $T$. The second statement follows by composition with $q$. $\square$

**Example.** The filter is strictly larger than the textbook family. Choose, by Chebotarev (below), places $w_1, w_2, \ldots$, distinct, and data $(w_k, A_k, s_k)$ with $s_k \to 1$. Let $Z = \{1, s_1, s_2, \ldots\}$. A convergent sequence with its limit is closed in a Hausdorff space, so $Z$ is closed. Every nonempty open set of $\Gamma_E$ contains a coset of an open subgroup, which is an infinite profinite group and so uncountable. So $V \setminus Z$ is a nonempty open set for every nonempty open $V$. Take $O = V \setminus Z$ and no exceptional places: the set $X$ of data with $s \notin Z$ contains most Frobenius data. But $X$ misses the datum $(w_k, A_k, s_k)$ at infinitely many places $w_k$. So $X$ contains no set of the form "every datum at every $w \notin S$".

In words: a set in $\mathcal{F}_E$ may miss the Frobenius elements in a closed set with empty interior, and the finite set of exceptional places may depend on the open set $O$. For the attached representations of Section 4, this is the first difference from the textbook.

**Remark (Formalization).** The definition is the one in `Lib/GaloisRep/Main/Defs.lean`, line 209. It is finding F-053 of the [register of findings](/chapter/register-of-findings/), together with the approximate condition of Section 4. The source does not state that a textbook attached representation is attached in its sense. The proof is short, and Exercise 2 of Section 8 asks for it.

### Limits along the filter

**Lemma.** Let $X$ be a topological space, $f : \Gamma_E \to X$ continuous and $g \in \Gamma_E$. Then $f(s) \to f(g)$ along $\mathcal{F}_E(g)$, where $s$ is the Frobenius element of the datum.

Lean: `New.tendsto_mostFrobeniiAt` (Lib/GaloisRep/Main/Defs.lean).

*Proof.* The filter $\mathcal{F}_E(g)$ is finer than the inverse image of the neighbourhoods of $g$. So $s \to g$ along $\mathcal{F}_E(g)$, and $f$ is continuous at $g$. $\square$

The next lemma moves the filter along an open embedding of Galois groups. The source uses it for complex conjugation and for restriction to subgroups.

**Lemma.** Let $E$ and $F$ be number fields inside $\Omega$, let $\varphi : \Gamma_E \to \Gamma_F$ be an open embedding, let $\pi$ be a map from the finite places of $E$ to those of $F$, and let $X$ contain most Frobenius data for $E$. Then for most Frobenius data $y$ for $F$ the following holds: every datum $x$ for $E$ with $\pi(\text{place of } x) = \text{place of } y$ and $\varphi(\text{Frobenius of } x) = \text{Frobenius of } y$ lies in $X$.

Lean: `New.eventually_mostFrobenii_of_isOpenEmbedding` (Lib/GaloisRep/Main/Defs.lean).

*Proof.* Let $V \subseteq \Gamma_F$ be nonempty and open. Suppose first that $\varphi^{-1}(V)$ is nonempty. It is open, since $\varphi$ is continuous. The hypothesis on $X$ gives a nonempty open $O \subseteq \varphi^{-1}(V)$ and a finite set $S$ of places of $E$ outside which every datum with Frobenius in $O$ lies in $X$. The image $\varphi(O)$ is open, nonempty and in $V$. The set $\pi(S)$ is finite. Let $y$ be a datum for $F$ with place $v \notin \pi(S)$ and Frobenius in $\varphi(O)$, and let $x$ be a datum for $E$ as in the statement. Since $\varphi$ is injective, the Frobenius of $x$ lies in $O$. If $x \notin X$, then the place of $x$ is in $S$, and $v = \pi(\text{place of } x) \in \pi(S)$, which is false. So $x \in X$.

Suppose next that $\varphi^{-1}(V)$ is empty. Take $O = V$. A datum $x$ as in the statement would have $\varphi(\text{Frobenius of } x) \in V$, which is impossible. So the condition holds with no exception. $\square$

**Remark (Formalization).** The map $\pi$ is any function. The lemma does not ask that $\pi$ sends a place to the place below it, and it does not ask that $\varphi$ is a homomorphism. The hypotheses that matter are on the data: a datum $x$ is compared with $y$ only through $\pi$ and $\varphi$. In the application to complex conjugation, $F = E$, $\pi$ is $w \mapsto \bar w$ and $\varphi$ is conjugation by a complex conjugation in $\mathrm{Gal}(\Omega/\mathbb{Q})$.

### Density

**Theorem (Density of most Frobenius elements).** Let $p$ be a property of elements of $\Gamma_E$, and suppose that $p(s)$ holds for most Frobenius data $(w, A, s)$. Then the set of $s \in \Gamma_E$ with $p(s)$ is dense in $\Gamma_E$.

Lean: `New.dense_of_mostFrobenii` (Lib/GaloisRep/Main/Defs.lean).

The proof uses Chebotarev in the existence form of Volume 3, [Theorem](/decl/New.chebotarev/): for a nonempty open $W \subseteq \Gamma_E$ and a finite set $S$ of places, there are a place $w \notin S$ of prime norm, a place $A$ over $w$, and an arithmetic Frobenius $\sigma$ at $A$ for $q_w$ with $\sigma \in W$.

*Proof.* Let $V$ be nonempty and open. The hypothesis gives a nonempty open $O \subseteq V$ and a finite set $S$ of places such that $p(s)$ holds for every datum $(w, A, s)$ with $w \notin S$ and $s \in O$. The set $O^{-1}$ is open and nonempty, since inversion is a homeomorphism. Chebotarev gives $w \notin S$ of prime norm, $A$ over $w$, and an arithmetic Frobenius $\sigma \in O^{-1}$ at $A$. Put $s = \sigma^{-1}$. Then $s \in O$, and $s^{-1} = \sigma$ is an arithmetic Frobenius, so $(w, A, s)$ is a Frobenius datum. So $p(s)$ holds, and $s \in O \subseteq V$. Every nonempty open set meets $\{p\}$. $\square$

**Remark (Non-triviality).** For every $g \in \Gamma_E$ the filter $\mathcal{F}_E(g)$ is not trivial: every set in it is nonempty.

*Proof.* Let $X$ contain most data and let $U$ be a neighbourhood of $g$. We must find a datum in $X$ with Frobenius in $U$. Apply the theorem to the property "$s$ is the Frobenius of some datum in $X$". The set of such $s$ is dense, so it meets $U$. $\square$

**Remark (Formalization).** The statement of non-triviality is an anonymous instance of `Filter.NeBot` in `Lib/GaloisRep/Main/Defs.lean`, line 315, so it has no name to cite. Lean finds it by instance search whenever a limit along $\mathcal{F}_E(g)$ must be unique. In particular $\mathcal{F}_E$ itself is not trivial. If it were, every property would hold for most data, and Section 4 would attach every representation to every family.

The theorem is where the arithmetic enters. The filter $\mathcal{F}_E$ is defined for any topological group with a notion of Frobenius data. Without Chebotarev, the set of Frobenius elements might avoid a nonempty open set, and $\mathcal{F}_E(g)$ would then be trivial for $g$ in that set.
