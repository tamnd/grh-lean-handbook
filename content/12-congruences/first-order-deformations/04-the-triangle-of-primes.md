---
title: The triangle of primes
lean:
  - New/Congruences/FirstOrder/EvenClasses.lean
  - New/Congruences/FirstOrder/TrianglePrimes.lean
decls:
  - New.Selmer.IsPrimeTriangle
  - New.Selmer.mul_prod_pow_sub_pow_dvd
  - New.Selmer.surjective_of_linearIndependent_cast
  - New.Selmer.exists_isKummerMap_notMem_span
  - New.Selmer.exists_apply_eq_prod_mul
  - New.Selmer.exists_separating_element
  - New.Selmer.additive_apply_pow_mul_conj
  - New.Selmer.HasKummerType.eventually_eq_two_mul
  - New.Selmer.evenClasses_eventually_eq_two_nsmul
  - New.Selmer.TriangleEntry
  - New.Selmer.TriangleEntry.MayFollow
  - New.Selmer.TriangleEntry.exists_mayFollow
  - New.Selmer.exists_forall_of_wellFoundedLT
  - New.Selmer.TriangleEntry.exists_forall_mayFollow
  - New.Selmer.TriangleEntry.nsmul_tameGenerator_eq_zero_of_mayFollow
  - New.Selmer.exists_isPrimeTriangle
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The triangle of primes

This section chooses the auxiliary places, the first main result of the chapter. They are Taylor-Wiles places of level $\ell^\nu$, and their number does not depend on $\nu$. Their tame generators and Frobenius elements cut down the even classes, one place after another, up to a power of $\ell$ that does not depend on $\nu$. The notation is that of [the first section](/chapter/first-order-deformations/#what-the-chapter-proves).

### The triangle condition

**Definition (Triangle of primes).** Let $J$ be a finite linearly ordered set. Let $w_j$ be primes of $E$, and let $\tau_j, \varphi_j \in G$, for $j \in J$. Let $a \in G$, let $t \geq 1$, and let $\mathrm{ty} \colon J \to \{e : 0 < e < t\}$ be monotone. Let $b, c \geq 0$. The data form a *triangle of primes* for $a$ with bounds $b$ and $c$ if these five conditions hold.

1. ($\tau, \varphi$ form a tame generator family.) Each $w_j$ is off $\ell$, $\varphi_j \in G_\nu$, and $\tau_j$ is the chosen tame generator at some place above $w_j$.
2. (Test points.) There is a finite set $s \subset \ker \mathrm{cyc}$ with $(\#J + \#s + 1)\, b \leq c$ with these properties. For every coefficient ring $O$ and every $e$, a locally constant cocycle in $(O/\ell^\nu)(-e)$ that is unramified off $\ell$ and vanishes at $a$ and on $s$ is zero. For every exponent $e$ and every $g \in s$, there is $j$ with $\mathrm{ty}(j) = e$ such that $z(\varphi_j) = 2 z(g)$ for every even class $z$ of exponent $e$ unramified off $\ell$, for every $O$.
3. (Separation.) With $u = \mathrm{cyc}(a^{-1})$, for every $e < t$ the product $\prod_{k < t,\, k \neq e} (u^e - u^k)$ divides $\ell^b$ in $\mathbb{Z}_\ell$.
4. (Triangle.) Let $z$ be an even class of exponent $\mathrm{ty}(j)$ for the primes $w_i$. Suppose that $z(\tau_i) = 0$ for all $i < j$, and that $z(\varphi_i) = 0$ for all $i < j$ with $\mathrm{ty}(i) = \mathrm{ty}(j)$. Then $\ell^b z(\tau_j) = 0$.
5. (Four.) For every $O$ and every $0 < e < t$, the element $4(\mathrm{cyc}(a)^{-e} - 1)^2$ of $O$ divides $\ell^b$.

Lean: `New.Selmer.IsPrimeTriangle` (New/Congruences/FirstOrder/EvenClasses.lean).

The source puts this definition in the later chapter [tied traces and even classes](/chapter/tied-traces/), which uses the triangle, and this section states it because it constructs one.

The name comes from condition 4: the condition at $j$ asks only for vanishing at the earlier indices, so the system is triangular. At the first index, $\ell^b$ kills $z(\tau_j)$ for every even class of that exponent.

### Arithmetic of the exponents

**Lemma.** Let $u \in \mathbb{Z}_\ell^\times$ such that $u^a - 1$ divides $\ell^h$ for every $0 < a < t$. Let $t + 2 \leq y$. If $n$ divides $\ell^{3h}$, then for every $a < t$,
$$n \prod_{k < t,\, k \neq a} (u^a - u^k) \mid \ell^{y h}.$$

Lean: `New.Selmer.mul_prod_pow_sub_pow_dvd` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* For $k < b$, $u^b - u^k = u^k (u^{b-k} - 1)$, and $u^k$ is a unit, so each factor divides $\ell^h$. There are $t - 1$ factors. So the left side divides $\ell^{3h + (t-1)h}$, and $3 + t - 1 \leq y$. $\square$

### Step 1: a new Kummer map and a separating element

**Lemma (Nakayama).** Let $\nu > 0$. Let $A$ be a group and $\psi_i \colon A \to \mathbb{Z}/\ell^\nu$, for $i$ in a finite set, be homomorphisms. If their reductions modulo $\ell$ are linearly independent over $\mathbb{F}_\ell$, then $a \mapsto (\psi_i(a))_i$ is onto $(\mathbb{Z}/\ell^\nu)^I$.

Lean: `New.Selmer.surjective_of_linearIndependent_cast` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* The image $N$ is a $\mathbb{Z}/\ell^\nu$-submodule. Its reduction spans $\mathbb{F}_\ell^I$ by the independence. So $N + \ell (\mathbb{Z}/\ell^\nu)^I$ is everything. The ideal $(\ell)$ is nilpotent, so it lies in the Jacobson radical, and Nakayama's lemma gives $N = (\mathbb{Z}/\ell^\nu)^I$. $\square$

**Lemma (A new Kummer map).** Let $\nu > 0$, let $E$ have at least four infinite places, and let $x_i$ be finitely many $\nu$-split places above distinct primes of $F$. Let $v_i \colon G_\nu \to \mathbb{F}_\ell$ be any maps with the same index set. Then there are a finite set $T \supseteq S_0$ and a Kummer map $\psi$ of exponent $e$ off $T$ for $x$ whose reduction is not in the span of the $v_i$.

Lean: `New.Selmer.exists_isKummerMap_notMem_span` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* By [many Kummer maps](/chapter/first-order-deformations/#kummer-maps-and-the-reciprocity-law) there is $T$ with $\dim K_e(x, T) > \#I$. The span of the $v_i$ has dimension at most $\#I$. So some generator of $K_e(x, T)$, the reduction of a Kummer map, lies outside it. $\square$

**Lemma (Conjugation separates the exponents).** Let $\gamma \in G$ and $g \in G_\nu$. Let $s$ be a finite set of exponents below $t$, and write $\bar{c} = \mathrm{cyc}(\gamma)$ modulo $\ell^\nu$. Then there is $g' \in G_\nu$ such that every $\psi$ of Kummer type with any exponent $d$ satisfies
$$\psi(g') = \prod_{a \in s} (\bar{c}^{\,d} - \bar{c}^{\,a})\, \psi(g).$$

Lean: `New.Selmer.exists_apply_eq_prod_mul` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* By induction on $s$. If $g'$ works for $s$, put $g'' = (\gamma g' \gamma^{-1})^{m} \cdot g'^{\,k}$, where $m$ represents $\bar{c}^{-1}$ and $k$ represents $-\bar{c}^{\,a}$. Then $g'' \in G_\nu$, and by the Kummer type
$$\psi(g'') = \bar{c}^{-1} \bar{c}^{\,d+1} \psi(g') - \bar{c}^{\,a} \psi(g') = (\bar{c}^{\,d} - \bar{c}^{\,a}) \psi(g'). \qquad \square$$

**Lemma (Separating element).** Let $\nu > 0$ and $\gamma \in G$. Let $\psi_i$ have Kummer type of exponent $\mathrm{ty}(i) < t$, and let $\psi_0$ have Kummer type of exponent $e < t$. Suppose that the reductions of the $\psi_i$ with $\mathrm{ty}(i) = e$ are linearly independent, and that the reduction of $\psi_0$ is not in their span. Then there is $u \in G_\nu$ with $\psi_i(u) = 0$ for all $i$ and
$$\psi_0(u) = \prod_{k < t,\, k \neq e} (\bar{c}^{\,e} - \bar{c}^{\,k}).$$

Lean: `New.Selmer.exists_separating_element` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* The reductions of $\psi_0$ and of the $\psi_i$ with $\mathrm{ty}(i) = e$ are independent. By Nakayama on $G_\nu$, some $g \in G_\nu$ has $\psi_0(g) = 1$ and $\psi_i(g) = 0$ for those $i$. Apply the last lemma with $s = \{k \neq e\}$. A map of exponent $\mathrm{ty}(i) \neq e$ gets the factor $\bar{c}^{\,\mathrm{ty}(i)} - \bar{c}^{\,\mathrm{ty}(i)} = 0$. A map of exponent $e$ with $\psi_i(g) = 0$ stays $0$. The map $\psi_0$ gets the product. $\square$

### Step 2: a place with the right Frobenius element

The source asks the Frobenius data to lie in a set $W$ that contains *most Frobenius elements near* $\delta^{\ell^\nu} g'$ for some $\delta \in \ker \mathrm{cyc}$ ([what attached means](/chapter/attached-representations/)). The factor $\delta^{\ell^\nu}$ is invisible to all the functions in play, as the next lemma shows.

**Lemma.** Let $\delta, g \in \ker \mathrm{cyc}$ and $u \in G_\nu$. Let $f \colon G \to \mathbb{Z}/\ell^\nu$ satisfy $f(ab) = f(a) + f(b)$ whenever $\mathrm{cyc}(a) = 1$ and $b \in G_\nu$. Then
$$f(\delta^{\ell^\nu} g\, g^c\, u (u^c)^{-1}) = f(g) + f(g^c) + f(u) - f(u^c).$$

Lean: `New.Selmer.additive_apply_pow_mul_conj` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* The $\ell^\nu$ copies of $\delta$ give $\ell^\nu f(\delta) = 0$, and $f(u) = f(u (u^c)^{-1}) + f(u^c)$. $\square$

Put $\sigma = \delta^{\ell^\nu} g\, g^c\, u (u^c)^{-1}$.

**Lemma.** If $\psi$ has Kummer type of exponent $e$, then $\psi(s) = 2\psi(u)$ for all $s$ near $\sigma$.

Lean: `New.Selmer.HasKummerType.eventually_eq_two_mul` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* $\psi$ is locally constant. At $\sigma$, the last lemma and oddness give $\psi(g) - \psi(g) + \psi(u) + \psi(u) = 2\psi(u)$. $\square$

**Lemma.** For all $s$ near $\sigma$, every even class $z$ of exponent $e$ unramified off $\ell$, for every $O$, satisfies $z(s) = 2 z(g)$.

Lean: `New.Selmer.evenClasses_eventually_eq_two_nsmul` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* Such cocycles with values in $\mathbb{Z}/\ell^\nu$ are finitely many, so all are constant near $\sigma$. By [testing with maps to $\mathbb{Z}/\ell^\nu$](/chapter/first-order-deformations/#the-real-subfield-and-even-classes) it is enough to treat these. On $\ker \mathrm{cyc}$ the cocycle rule gives additivity, and evenness gives $z(g) + z(g^c) + z(u) - z(u^c) = 2 z(g)$. $\square$

### Step 3: entries, and choice in order

**Definition (Entry).** An *entry* at level $\nu$ is a $\nu$-split place with its Frobenius datum, a finite set of primes of $F$ to avoid, and a function $G \to \mathbb{Z}/\ell^\nu$, the candidate map.

Lean: `New.Selmer.TriangleEntry` (New/Congruences/FirstOrder/TrianglePrimes.lean).

**Definition (May follow).** Let $f_i$ be entries of exponents $\mathrm{ty}(i)$, for $i$ in a finite set. An entry $q$ of exponent $e$, with map $\psi_q$ and Frobenius element $\varphi_q$, *may follow* them with test element $g$, loss $n$ and set $W$ if these hold.

1. $\psi_q$ is a Kummer map of exponent $e$, off the primes $q$ avoids, for the earlier places of exponent $e$.
2. The primes $q$ avoids contain $S_0$ for those earlier places.
3. The reduction of $\psi_q$ is not in the span of the reductions of the earlier maps of exponent $e$.
4. $2 \psi_q(\varphi_q)$ divides $n$.
5. Every earlier map vanishes at $\varphi_q$.
6. Every even class $z$ of exponent $e$ unramified off $\ell$ has $z(\varphi_q) = 2 z(g)$.
7. The prime of $F$ below $q$ is not below an earlier place, not avoided by an earlier entry, and not avoided by $q$.
8. The Frobenius datum of $q$ lies in $W$.

Lean: `New.Selmer.TriangleEntry.MayFollow` (New/Congruences/FirstOrder/TrianglePrimes.lean).

**Lemma (One step).** Let $\nu > 0$, let $E$ have at least four infinite places, let $t + 2 \leq y$, let $\mathrm{cyc}(\gamma)^a - 1 \mid \ell^h$ for $0 < a < t$, let $4 \mid \ell^{3h}$, and let $g \in \ker \mathrm{cyc}$. For every $g'$, let $W$ contain most Frobenius elements near $\delta^{\ell^\nu} g'$ for some $\delta \in \ker \mathrm{cyc}$. Let $f_i$ be finitely many entries above distinct primes of $F$, whose maps have Kummer type of exponent $\mathrm{ty}(i)$, such that the reductions of those of exponent $e$ are independent. Then some entry may follow them, with test element $g$ and loss $\ell^{y h}$.

Lean: `New.Selmer.TriangleEntry.exists_mayFollow` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* Step 1 gives $T_0$ and a new Kummer map $\psi_0$ for the earlier places of exponent $e$, and a separating element $u$. Take $\delta$ for $g' = g\,g^c u (u^c)^{-1}$, and let $\sigma$ be as above. The filter of most Frobenius elements near $\sigma$ is proper by Chebotarev's theorem. So there is a datum $x_0$ in $W$ whose Frobenius element $\varphi$ is near $\sigma$ and in $G_\nu$, with prime off $\ell$, off $T_0$, and off the primes below or avoided by earlier entries. Then $\psi_0(\varphi) = 2\psi_0(u)$, each earlier map gives $2 \cdot 0 = 0$, and even classes give $2 z(g)$. Finally $2\psi_0(\varphi) = 4 \prod_{k \neq e} (\bar{c}^{\,e} - \bar{c}^{\,k})$, and this divides $\ell^{y h}$ by the arithmetic lemma with $n = 4$. The new entry is $x_0$ with $T_0$ and $\psi_0$. $\square$

**Lemma (Choice along a well-order).** Let $J$ be well-ordered by $<$ and $X$ nonempty. Let $P_j$ be a property of a value in $X$ and of the values before $j$. Suppose that, for every $f \colon J \to X$ and $j$, if each $f(i)$ with $i < j$ satisfies $P_i$ with the values before $i$, then some value satisfies $P_j$ with the values of $f$ before $j$. Then some $f$ satisfies $P_j$ at every $j$.

Lean: `New.Selmer.exists_forall_of_wellFoundedLT` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* Choose $f(j)$ by well-founded recursion, and use induction on $j$. $\square$

**Remark (Formalization).** The source chooses the value at $j$ with Hilbert's epsilon operator, so it needs $X$ to be nonempty. For entries, a global instance gives one: the zero map, with no primes to avoid, at a split place near $1$. The induction shows that this default is never taken.

**Lemma.** Under the hypotheses of the one-step lemma, for every finite linear order $J$, exponents $\mathrm{ty}$ and test elements $g_j \in \ker \mathrm{cyc}$, there are entries $f_j$ such that each $f_j$ may follow the $f_i$ with $i < j$, with test element $g_j$ and loss $\ell^{y h}$. The condition $4 \mid \ell^{3h}$ is needed only if $J$ is nonempty.

Lean: `New.Selmer.TriangleEntry.exists_forall_mayFollow` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* Apply the choice along the order. At $j$, the earlier places lie above distinct primes of $F$ by condition 7, and the earlier maps have Kummer type by condition 1. The earlier maps of exponent $\mathrm{ty}(j)$ are independent, because by condition 3 none is in the span of the ones before it, and such a family is linearly independent. So the one-step lemma applies. $\square$

**Lemma (The triangle condition).** Let entries $f_j$ along $J$ each follow the earlier ones with loss $n$. Let $z$ be an even class of exponent $\mathrm{ty}(j)$ for the places of all entries. Suppose that $z$ vanishes at the tame generators of the $i < j$, and at the Frobenius elements of the $i < j$ with $\mathrm{ty}(i) = \mathrm{ty}(j)$. Then $n\, z(\tau_j) = 0$.

Lean: `New.Selmer.TriangleEntry.nsmul_tameGenerator_eq_zero_of_mayFollow` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* The cocycle rule and evenness give $z((\tau^c)^{-1}) = -\mathrm{cyc}(\tau)^{e} z(\tau)$ for every $\tau \in G$, so $z$ also vanishes at the doubled family of the earlier tame generators. By [killing tame generators](/chapter/first-order-deformations/#the-real-subfield-and-even-classes), $z$ is an even class for the places $i \geq j$ only. The map $\psi_j$ of entry $j$ is a Kummer map off the primes it avoids, and the places $i \geq j$ avoid them by condition 7. It vanishes at the Frobenius elements of the later places by their condition 5. The class $z$ vanishes at the Frobenius elements of the earlier places of the same exponent. So [reciprocity with one term](/chapter/first-order-deformations/#kummer-maps-and-the-reciprocity-law) applies at $j$, the least of the indices $i \geq j$, and $2\psi_j(\varphi_j) \mid n$ gives $n z(\tau_j) = 0$. $\square$

### The main theorem

**Theorem (Triangle of primes).** Let $E$ have at least four infinite places, and let $E$ lie in the cyclotomic field of level $N > 0$. Let $N + t < y$. Let $\gamma \in G$ generate $G$ topologically modulo $\ker \mathrm{cyc}$. Let $\mathrm{cyc}(\gamma)^a - 1$ divide $\ell^h$ for $0 < a < t$. Let $\ell \leq y^2$ or $h = 0$. Let $W$ be a set of Frobenius data such that for all $\nu$ and $g$ there is $\delta \in \ker \mathrm{cyc}$ for which $W$ contains most Frobenius elements near $\delta^{\ell^\nu} g$. Then there are a finite linear order $J$ and a monotone map $\mathrm{ty}$ from $J$ to $\{e : 0 < e < t\}$ such that, for every $\nu > 0$, there are Taylor-Wiles places $Q$ of level $\ell^\nu$ indexed by $J$, with Frobenius data in $W$, that form a triangle of primes for $\gamma^{-1}$ with bounds $y h$ and $y^{22} h$.

Lean: `New.Selmer.exists_isPrimeTriangle` (New/Congruences/FirstOrder/TrianglePrimes.lean).

*Proof.* The bound on odd classes ([odd classes](/chapter/odd-classes/)) gives a finite set $s \subset \ker \mathrm{cyc}$ of test points such that every cocycle unramified off $\ell$ that vanishes at $\gamma^{-1}$ and on $s$ is zero, for all $O$, $\nu$ and $e$, with $\# s \leq y^{20}$ when $N \leq y$ and $\ell \leq y^2$. Well-order $s$. Let $J = \{e : 0 < e < t\} \times s$ with the lexicographic order, and let $\mathrm{ty}$ be the first coordinate. This $J$ does not depend on $\nu$.

Fix $\nu > 0$. Since $4 \mid \mathrm{cyc}(\gamma^e) - 1$ and that divides $\ell^h$, the element $4(\mathrm{cyc}(\gamma)^e - 1)^2$ divides $\ell^{3h}$. Choose entries $f_j$ along $J$ with test element $g_j$, the second coordinate of $j$, and loss $\ell^{y h}$. Their places lie above distinct primes of $F$, so they are distinct and apart from their conjugates ([split places](/chapter/first-order-deformations/#the-real-subfield-and-even-classes)). Their norms are $1$ modulo $\ell^\nu$. So they are Taylor-Wiles places of level $\ell^\nu$. Now check the five conditions with $b = y h$ and $c = y^{22} h$.

1. The entries form a tame generator family.
2. Take the test points $s$. At $j = (e, g)$ the even classes take twice their value at $g$, by condition 6. For the count, $\#J \leq t\, y^{20}$ and $\#s + 1 \leq 2 y^{20}$, so $\#J + \#s + 1 \leq (t + 2) y^{20} \leq y^{21}$. Then $(\#J + \#s + 1)\, y h \leq y^{22} h$. If $h = 0$ both sides are $0$.
3. The product for $\gamma^{-1}$ divides $\ell^{y h}$ by the arithmetic lemma with $n = 1$. Each factor for $\gamma^{-1}$ is a unit times a factor for $\gamma$, since $u^{-e} - u^{-k} = -u^{-e-k}(u^e - u^k)$.
4. This is the triangle lemma.
5. The arithmetic lemma with $n = 4 (\mathrm{cyc}(\gamma)^e - 1)^2$ and the part of the product it contains gives the divisibility in $\mathbb{Z}_\ell$, and its image in $O$. $\square$

The source claims this theorem, and Lean accepts it if the reported checks hold.

**Remark (Formalization).** The hypothesis on $W$ is weaker than a Chebotarev statement near every $g$. It allows a correction $\delta^{\ell^\nu}$ with $\delta \in \ker \mathrm{cyc}$, which may depend on $\nu$ and $g$. The proof uses only that the filter near a point is proper.

### A model case

Take $t = 2$, so the only exponent is $e = 1$, and suppose the test set is one point $g$. Then $J$ has one element, and the triangle is one place.

There are no earlier places, so $S_0$ is the set of primes above $\ell$. By [many Kummer maps](/chapter/first-order-deformations/#kummer-maps-and-the-reciprocity-law), the reductions of Kummer maps of exponent $1$ off some $T$ span a space of dimension at least $1$. So a Kummer map $\psi_0$ has nonzero reduction. Nakayama gives $g_0 \in G_\nu$ with $\psi_0(g_0) = 1$. With $s = \{0\}$, conjugation gives $u = (\gamma g_0 \gamma^{-1})^{m} g_0^{-1}$, with $m \equiv \bar{c}^{-1}$, and $\psi_0(u) = \bar{c} - 1$.

Chebotarev gives a place $w$ off $T$ whose Frobenius element $\varphi$ is near $\sigma = \delta^{\ell^\nu} g\, g^c u (u^c)^{-1}$. So $\psi_0(\varphi) = 2(\bar{c} - 1)$, and every even class of exponent $1$ unramified off $\ell$ has $z(\varphi) = 2 z(g)$.

Let $z$ be an even class of exponent $1$ that may ramify at $w$ and $\bar{w}$. The reciprocity law has one term:
$$\psi_0(\varphi) \cdot 2 z(\gamma_w) = 4(\bar{c} - 1) z(\gamma_w) = 0.$$
The chosen tame generator $\tau_w$ lies in inertia, so $z(\tau_w)$ is a multiple of $z(\gamma_w)$. Since $4 \mid \mathrm{cyc}(\gamma) - 1 \mid \ell^h$, the element $4(\mathrm{cyc}(\gamma) - 1)$ divides $\ell^{2h}$, so $\ell^{2h}$ kills $z(\tau_w)$. This is condition 4 for the single place, with a loss that does not depend on $\nu$.
