---
title: Why the argument needs them
lean:
  - New/Reduction/Data/Existence.lean
  - New/Reduction/Data/AdmissibleData.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Why the argument needs them

This chapter gives the background for one combinatorial input of the proof: large sets of integers with no three-term progressions. The source needs such a set for one purpose. It builds the set $\Phi_b$ of infinite places of the field $E$ that carry the large weight $b$. The chapter first gives the classical theory: the problem of Erdős and Turán, the constructions of Salem and Spencer and of Behrend, and the upper bounds of Roth type. Then it states exactly what the source proves, with every constant. Then it explains, with exact statements, the two places in the argument that use the set. A remark on the formalization follows each difference between the classical form and the form of the source.

A reader will first ask why a proof about the zeros of L-functions needs a set with no three-term progressions. This section answers that question. The answer has three parts: the set $\Phi_b$ must avoid certain configurations along the orbits of Frobenius; for a good choice of $\Phi_b$ these configurations are weighted three-term progressions of exponents; and $\Phi_b$ must be large, which rules out the easy constructions.

### Where the chapter sits

[The plan](/chapter/theorem-and-plan/) of the proof compares two bounds for the covolume of a lattice of theta lifts. The comparison holds for every term $D$ of the type of data. The data fix the scales $x$, $x_1$, $b$, the ranks $m$, $r$, the exponent $s$, the field $E = K(\zeta_{q_1})$ with $K = \mathbb{Q}(\sqrt{-d})$, a weight at each infinite place of $E$, and three primes. The chapter [the data and its sizes](/chapter/data-and-sizes/) lists the fields of $D$, and the chapter [the data exist](/chapter/data-exist/) of Volume 1 builds data at every large integer $x$. This chapter uses their notation.

Recall the notation. The parameters $P$ fix a multiple $q_0$ of $18480$ and a prime $d$. For the exponent $s \geq 1$ put
$$l_0 = 3^{\lfloor \log_3 s \rfloor + 4}, \qquad \operatorname{towerDeg}(s) = 3 l_0 2^s, \qquad q_1 = q_0 \operatorname{towerDeg}(s).$$
Then $l_0$ is the least power of $3$ above $27 s$, and $27 s < l_0 \leq 81 s$. The infinite places of $E$ form a group $\Phi$, and the action on $\zeta_{q_1}$ gives an isomorphism $\Phi \cong (\mathbb{Z}/q_1\mathbb{Z})^\times$. For a divisor $q$ of $q_1$, the class of a place modulo $q$ is its image in $(\mathbb{Z}/q\mathbb{Z})^\times$. For a prime $\ell$, write $q_1^{(\ell)}$ for the part of $q_1$ prime to $\ell$. Put $k = r + 1 - m$ and $t = 5r$. The data have $m \approx \sqrt{x}$, $r \approx x^5$, $2^s = m^{22} \approx x^{11}$, and $\log b \approx x^{\varepsilon}$ for a fixed $\varepsilon \in (0, 1/100)$.

The data contain a finite set $\Phi_b \subseteq \Phi$ with three properties:

1. every $\sigma \in \Phi_b$ has class $-1$ modulo $q_0$;
2. $\operatorname{towerDeg}(s) \leq \#\Phi_b \cdot \log b$;
3. $\Phi_b$ is *sparse* for the primes up to $kt$: for every prime $\ell \leq kt$ and all integers $0 < i < j < l_0$, there are no $\sigma, \tau, \rho \in \Phi_b$, distinct or not, and no signs $\epsilon, \epsilon' \in \{\pm 1\}$ such that
$$\tau/\sigma \equiv \epsilon\, \ell^i \quad\text{and}\quad \rho/\sigma \equiv \epsilon'\, \ell^j \pmod{q_1^{(\ell)}}.$$

The weight of a place is $b$ on $\Phi_b$ and $\lfloor xb/x_1 \rfloor$ elsewhere. The exact definition of sparseness is [Definition](/decl/New.Parameters.IsSparse/) in Volume 1. Exactly $\operatorname{towerDeg}(s)$ places have class $1$ modulo $q_0$, and the same number have class $-1$. So property 2 says that $\Phi_b$ has density at least $1/\log b$ among the places of class $-1$.

### Why sparseness: the orbits of Frobenius

Let $\ell$ be a prime and let $\lambda$ be a place of $E$ above $\ell$. The completion $E_\lambda$ and its embeddings into $\overline{\mathbb{Q}}_\ell$ are the setting of two later steps of the argument. Fix an isomorphism $\iota \colon \mathbb{C} \cong \overline{\mathbb{Q}}_\ell$. Then each embedding of $E$ into $\overline{\mathbb{Q}}_\ell$ gives a complex embedding, and so an infinite place. A Frobenius element at $\lambda$ acts on the roots of unity of order prime to $\ell$ by $\zeta \mapsto \zeta^{\ell}$. On the group $\Phi$, read modulo $q_1^{(\ell)}$, this is multiplication by $\ell$. So the Frobenius orbits of embeddings above $\lambda$ give orbits $\sigma, \ell\sigma, \ell^2\sigma, \dots$ of places, up to complex conjugation, which is the sign $-1$.

Along such an orbit the weights matter. The weight of a place becomes a Hodge-Tate weight at the corresponding embedding, and the weight $b$ is enormous next to the other sizes. Two later steps need that the large weights do not crowd together along a short piece of an orbit.

- In Volume 11, [the divisibility is sharp](/chapter/sharpness/), at a prime $p \leq k$ that does not split in $K$, a place $\tau$ is coupled with its partners $-p^e \tau$. A *near pair* is a $b$-place whose partner at a small exponent $e < l_0/2$ is again a $b$-place. The argument treats near pairs one at a time, and it needs that no place lies in two of them.
- In Volume 12, [the local loss at ℓ](/chapter/local-loss/), at a prime $\ell \leq kt$, the integral $p$-adic Hodge theory of the source bounds a cup product. The bound needs that no three $b$-places follow one another along an orbit of Frobenius with short gaps.

Both demands are the same statement: no three places $\sigma$, $\pm\ell^i\sigma$, $\pm\ell^j\sigma$ with $0 < i < j < l_0$ all lie in $\Phi_b$. This is property 3. Section 5 states both uses in full.

### From sparseness to progressions

The set $\Phi_b$ must avoid a configuration for each prime $\ell \leq kt$. There are about $kt/\log(kt)$ such primes, a power of $x$. A construction prime by prime is hopeless. The source finds a construction in which the configuration for every prime becomes the same linear equation.

Take an element $g \in \Phi$ and put $\Phi_b = \{-g^e : e \in S\}$ for a set $S$ of exponents. Then $\tau/\sigma = g^{e_2 - e_1}$ and $\rho/\sigma = g^{e_3 - e_1}$ for $\sigma = -g^{e_1}$, $\tau = -g^{e_2}$, $\rho = -g^{e_3}$. Suppose that $g^{e_2 - e_1} \equiv \pm\ell^i$ and $g^{e_3 - e_1} \equiv \pm\ell^j$. Raise the first relation to the power $2j$ and the second to the power $2i$. The signs disappear, and both sides become $\ell^{2ij}$. So
$$g^{2j(e_2 - e_1)} = g^{2i(e_3 - e_1)}, \qquad\text{that is}\qquad 2j\, e_2 \equiv 2(j - i)\, e_1 + 2i\, e_3 \pmod{\operatorname{ord}(g)}.$$
This is an equation $(\alpha + \alpha') e_2 \equiv \alpha e_1 + \alpha' e_3$ with the positive weights $\alpha = 2(j - i)$ and $\alpha' = 2i$, and $\alpha + \alpha' = 2j < 2 l_0$. The prime $\ell$ has disappeared. If $S$ has no solutions of these equations except $e_1 = e_2 = e_3$, the configuration can only be $\sigma = \tau = \rho$, and then $\ell^{2i} \equiv 1$. This is false when the order of $\ell$ is large, and an elementary bound on orders modulo a power of $2$ shows that it is large for $\ell \leq kt$.

For $i = 1$ and $j = 2$ the equation is $4 e_2 \equiv 2 e_1 + 2 e_3$, which comes from the three-term progression $2 e_2 = e_1 + e_3$. This is the reason for the title of the chapter.

**Example (Places modulo $128$).** Here is the model case in a small group. Take the group $(\mathbb{Z}/128\mathbb{Z})^\times$ in place of $\Phi$, the element $g = 5$, of order $32$, and the prime $\ell = 3$. Since $5^3 = 125 \equiv -3$, we have $3 \equiv -5^3 \pmod{128}$. The subgroup $\langle 5 \rangle$ does not contain $-1$, so the signs are fixed by the exponents. Let $\sigma = -5^{e_1}$, $\tau = -5^{e_2}$, $\rho = -5^{e_3}$. Then $\tau/\sigma = 5^{e_2 - e_1}$, and $\tau/\sigma = \pm 3^i = \pm 5^{3i}$ holds if and only if $e_2 - e_1 \equiv 3i \pmod{32}$. In the same way $\rho/\sigma = \pm 3^j$ if and only if $e_3 - e_1 \equiv 3j$. For $i = 1$ and $j = 2$ the pattern is $e_2 = e_1 + 3$, $e_3 = e_1 + 6$: a three-term progression with difference $3$. For $i = 1$ and $j = 3$ it is $e_2 = e_1 + 3$, $e_3 = e_1 + 9$, and $3e_2 = 2e_1 + e_3$. Every pattern satisfies $j(e_2 - e_1) \equiv i(e_3 - e_1) \pmod{32}$. A set $S$ of exponents that has no solutions of $(\alpha + \alpha')e_2 \equiv \alpha e_1 + \alpha' e_3$ with $e_1, e_2, e_3$ not all equal avoids every pattern at once, and it does so for every prime $\ell$ whose class lies in $\pm\langle 5 \rangle$.

### Why the set must be large

Property 2 asks for at least $\operatorname{towerDeg}(s)/\log b$ places. The group $\langle g \rangle$ in the source has order $2^s \approx x^{11}$, and $\log b \approx x^{\varepsilon}$. So $S$ must have size at least about $2^s / \log b$, that is, density about $N^{-\varepsilon/11}$ in $[0, N)$ with $N = 2^s$, up to a factor that is a power of $\log N$. The exponent $\varepsilon$ is fixed but small, and the proof works for each $\varepsilon \in (0, 1/100)$. So the construction must give, for every $\delta > 0$, sets of density at least $N^{-\delta}$, for all the weights up to $2 l_0 \approx \log N$ at once.

The main inequality uses property 2. Volume 1 shows, in [the main inequality](/chapter/main-inequality/), that the bound for the prime remainder $R_{q_0}(x)$ comes with a factor $\#\Phi_a / \#\Phi_b$, and property 2 bounds this factor by $\log b$. A smaller set $\Phi_b$ would cost a larger power of $\log b$ in the final bound, and the final bound has no room for a power of $x$.

This rules out the easy sets. By the theorem of Roth (Section 2), no set of positive density avoids three-term progressions, so one cannot take a fixed proportion of the exponents. The digit set of Erdős and Turán, the integers with digits $0$ and $1$ in base $3$, has density $N^{\log 2/\log 3 - 1} = N^{-0.369\ldots}$, which is too small. Sets of density $N^{-\delta}$ for every $\delta > 0$ were first found by Salem and Spencer. Behrend's construction gives them in a short proof, and it adapts at once to many weights and to a modulus. The source uses Behrend's construction with a fixed number $n$ of digits. This gives density about $H^{-2}$ for digits below $H \approx N^{1/n}$, that is, $N^{-2/n}$, which is enough when $n$ is large against $1/\varepsilon$.

### The plan of the chapter

Section 2 gives the classical theory: the Roth number $r_3(N)$, the constructions of Erdős and Turán, Salem and Spencer, and Behrend, with a complete proof of Behrend's bound, and the upper bounds from Roth to Kelley and Meka. It states the forms that Mathlib proves. Section 3 states the form of Behrend's construction in the source, with weights and a modulus, and gives its proof. Section 4 turns it into a sparse set of places and proves the count $\operatorname{towerDeg}(s) \leq \#\Phi_b \cdot W^6$. Section 5 states the two uses of sparseness in Volumes 11 and 12 and proves them from the definition. Section 6 has the exercises, the notes, and a summary of what this volume gives to the argument.
