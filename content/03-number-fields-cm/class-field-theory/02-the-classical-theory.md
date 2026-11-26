---
title: The classical theory
lean: []
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The classical theory

This section recalls the textbook statements that the source formalizes. It uses the notation of Neukirch, *Algebraic Number Theory* (Springer, 1999), Chapters V and VI, and of Milne, *Class Field Theory* (version 4.03, 2020). Nothing in this section is a statement of the source. Sections 3 to 7 give the source forms and compare them with the forms here.

### Ideles

Let $K$ be a number field. For each place $v$ of $K$ let $K_v$ be the completion. For a finite place $v$ let $\mathcal{O}_v$ be the valuation ring of $K_v$, let $\mathfrak{p}_v$ be its maximal ideal, and let $q_v = \#(\mathcal{O}_v/\mathfrak{p}_v)$ be the absolute norm of $v$.

**Definition (Idele group).** The *idele group* $J_K$ is the restricted product of the groups $K_v^\times$ over all places $v$ of $K$, with respect to the subgroups $\mathcal{O}_v^\times$ at the finite places. So an idele is a family $(a_v)_v$ with $a_v \in K_v^\times$ for every $v$ and $a_v \in \mathcal{O}_v^\times$ for almost all $v$. The topology has a base of neighbourhoods of $1$ formed by the sets $\prod_{v \in S} U_v \times \prod_{v \notin S} \mathcal{O}_v^\times$, with $S$ finite and containing the infinite places, and $U_v$ open in $K_v^\times$. The *finite ideles* $J_{K,f}$ are the same restricted product over the finite places only. The *idele class group* is $C_K = J_K / K^\times$, where $K^\times$ is embedded diagonally.

Neukirch defines these groups in Chapter VI, §1. There is a product decomposition $J_K = J_{K,f} \times K_\infty^\times$ with $K_\infty^\times = \prod_{v \mid \infty} K_v^\times$. The map that sends an idele to its ideal, $(a_v) \mapsto \prod_{v \nmid \infty} \mathfrak{p}_v^{v(a_v)}$, is surjective onto the group of fractional ideals. It induces an isomorphism from $J_K / K^\times (K_\infty^\times \times \prod_{v \nmid \infty} \mathcal{O}_v^\times)$ to the class group $\operatorname{Cl}_K$.

### The local Artin map

**Theorem (Local reciprocity).** Let $k$ be a finite extension of $\mathbb{Q}_p$. There is a unique homomorphism $\theta_k : k^\times \to \operatorname{Gal}(k^{\mathrm{ab}}/k)$ with two properties. First, for every uniformiser $\pi$ of $k$, $\theta_k(\pi)$ acts on the maximal unramified extension as the arithmetic Frobenius $x \mapsto x^{q}$ on residue fields, with $q$ the order of the residue field. Second, for every finite abelian extension $l/k$, $\theta_k$ induces an isomorphism $k^\times / N_{l/k} l^\times \cong \operatorname{Gal}(l/k)$.

This is Neukirch, Chapter V, §1 (the local reciprocity law) and Milne, Chapter I, Theorem 1.1. The cohomological construction is in Serre, *Local Fields* (Springer, 1979), Chapters XII to XIV, and in Milne, Chapter III. It goes in two steps.

1. The *invariant map* is an isomorphism $\operatorname{inv}_k : \operatorname{Br}(k) = H^2(\operatorname{Gal}(\bar{k}/k), \bar{k}^\times) \to \mathbb{Q}/\mathbb{Z}$. For an unramified character $\chi$ and $a \in k^\times$, it sends the cup product $a \cup \delta\chi$ to $v(a)\,\chi(\varphi)$, where $\varphi$ is the arithmetic Frobenius. Serre proves this in Chapter XIII, and Milne in Chapter III, §2.
2. The local Artin map is then the unique map with $\chi(\theta_k(a)) = \operatorname{inv}_k(a \cup \delta\chi)$ for every character $\chi : \operatorname{Gal}(\bar k/k) \to \mathbb{Q}/\mathbb{Z}$. Serre writes $(a, \chi)$ for $a \cup \delta\chi$ in Chapter XIV, §1. The existence of $\theta_k$ follows from the fact that the right side is a homomorphism in $\chi$, by Pontryagin duality for the profinite abelian group $\operatorname{Gal}(k^{\mathrm{ab}}/k)$.

The sign conventions vary between authors. With the convention above, a uniformiser goes to an arithmetic Frobenius. Some authors, for example Deligne, use the inverse map, so that a uniformiser goes to a geometric Frobenius. The source uses the geometric convention (Section 4).

### The global Artin map and reciprocity

**Theorem (Global reciprocity).** Let $K$ be a number field. The product of the local maps,
$$\theta_K : J_K \to \operatorname{Gal}(K^{\mathrm{ab}}/K), \qquad \theta_K((a_v)_v) = \prod_v \theta_{K_v}(a_v),$$
is a continuous homomorphism, and it is trivial on $K^\times$. For every finite abelian extension $L/K$ it induces an isomorphism $J_K / K^\times N_{L/K} J_L \cong \operatorname{Gal}(L/K)$.

The product is finite on each finite quotient, since almost all components are units at unramified places. Here $\theta_{K_v}$ for an infinite place $v$ is the sign map at a real place and trivial at a complex place. Neukirch proves the theorem in Chapter VI, §5. Milne states it in Chapter V and proves it in Chapter VII. The proof has two inequalities. The *first inequality* is $[J_K : K^\times N J_L] \geq [L : K]$ for cyclic $L/K$. The *second inequality* is $[J_K : K^\times N J_L] \leq [L : K]$ for every Galois $L/K$. Milne proves the second inequality by analysis in Chapter VI, and by algebra in Chapter VII. The source proves only the analytic form (Section 5).

### The existence theorem

**Theorem (Existence).** Every open subgroup of finite index of $C_K$ is the norm group $K^\times N_{L/K} J_L / K^\times$ of a unique finite abelian extension $L/K$.

Neukirch proves this in Chapter VI, §6, and Milne in Chapter VII. With reciprocity, it gives the main theorem: the map $L \mapsto N_{L/K} C_L$ is an inclusion reversing bijection from the finite abelian extensions of $K$ to the open subgroups of finite index of $C_K$. The map $\theta_K$ is surjective, and its kernel is the closure of $K^\times K_\infty^{\times,0}$, where $K_\infty^{\times,0}$ is the connected component of $1$ in $K_\infty^\times$. Milne states the theorems in this idelic form in Chapter V. The last statement comes from the existence theorem.

### Ray class fields

Let $\mathfrak{m} = \mathfrak{m}_0 \mathfrak{m}_\infty$ be a modulus: an integral ideal $\mathfrak{m}_0$ and a set $\mathfrak{m}_\infty$ of real places. The *ray class group* $\operatorname{Cl}_{\mathfrak{m}}$ is the group of fractional ideals prime to $\mathfrak{m}_0$ modulo the principal ideals $(x)$ with $x \equiv 1 \bmod \mathfrak{m}_0$ and $x$ positive at each place of $\mathfrak{m}_\infty$. In ideles, $\operatorname{Cl}_{\mathfrak{m}} \cong J_K / K^\times U_{\mathfrak{m}}$, where
$$U_{\mathfrak{m}} = \prod_{v \mid \mathfrak{m}_0} (1 + \mathfrak{p}_v^{n_v}) \times \prod_{v \in \mathfrak{m}_\infty} \mathbb{R}_{>0} \times \prod_{\text{other } v} \mathcal{O}_v^\times \ (\text{or } K_v^\times \text{ at infinite } v),$$
and $n_v$ is the exponent of $\mathfrak{p}_v$ in $\mathfrak{m}_0$. The *ray class field* $K^{\mathfrak{m}}$ is the class field of the open subgroup $K^\times U_{\mathfrak{m}}/K^\times$. So $\operatorname{Gal}(K^{\mathfrak{m}}/K) \cong \operatorname{Cl}_{\mathfrak{m}}$, and a prime $\mathfrak{p} \nmid \mathfrak{m}_0$ has its Frobenius equal to its class. Neukirch treats ray class fields in Chapter VI, §7. Every finite abelian extension lies in some ray class field.

**Example (The field of rational numbers).** Let $K = \mathbb{Q}$ and $\mathfrak{m} = m\infty$ for an integer $m \geq 2$. Then $\operatorname{Cl}_{\mathfrak{m}} \cong (\mathbb{Z}/m\mathbb{Z})^\times$, and the ray class field is $\mathbb{Q}(\zeta_m)$. For a prime $p \nmid m$ the Frobenius is $\sigma_p : \zeta_m \mapsto \zeta_m^p$. For $\mathfrak{m} = m$, with no infinite place, the ray class group is $(\mathbb{Z}/m\mathbb{Z})^\times/\{\pm 1\}$, and the ray class field is the real subfield $\mathbb{Q}(\zeta_m)^+$.

### The finite idele form

The source works with $J_{K,f}$ in place of $J_K$. The classical theory gives a statement about $J_{K,f}$ directly. Let $K^\times_+$ be the group of totally positive elements of $K^\times$: the $x$ with $\sigma(x) > 0$ for every real embedding $\sigma$.

**Proposition (Finite idele form).** The restriction of $\theta_K$ to $J_{K,f}$ is surjective onto $\operatorname{Gal}(K^{\mathrm{ab}}/K)$. Its kernel is the closure of $K^\times_+$ in $J_{K,f}$. For a finite abelian $L/K$, it induces $J_{K,f}/K^\times_+ N_{L/K} J_{L,f} \cong \operatorname{Gal}(L/K)$.

*Proof.* The group $K_\infty^{\times,0}$ is $\prod_{\text{real}} \mathbb{R}_{>0} \times \prod_{\text{complex}} \mathbb{C}^\times$, and $\theta_K$ is trivial on it. So $\theta_K$ factors through $J_K / K_\infty^{\times,0} = J_{K,f} \times \{\pm 1\}^{r_1}$. By weak approximation every sign vector is the sign vector of some $x \in K^\times$. So every class in $J_K / K^\times K_\infty^{\times,0}$ has a representative in $J_{K,f}$, and $\theta_K(J_{K,f}) = \theta_K(J_K)$, which is the full group. A finite idele $a$ lies in $K^\times K_\infty^{\times,0}$ exactly when $a = x$ in $J_{K,f}$ for some $x \in K^\times$ that is positive at each real place, that is, $x \in K^\times_+$. Pass to closures for the kernel, and to the norm group of $L$ for the last claim. $\square$

For a totally complex field, $K^\times_+ = K^\times$, and the proposition says that $J_{K,f}/K^\times$ has the abelianised Galois group as its profinite completion. This is the case of the existence theorem that the source proves (Section 7).

**Example (Finite ideles of $\mathbb{Q}$).** Every finite idele of $\mathbb{Q}$ is a product $r u$ with $r \in \mathbb{Q}_{>0}$ and $u \in \hat{\mathbb{Z}}^\times = \prod_p \mathbb{Z}_p^\times$, in a unique way. So $J_{\mathbb{Q},f} / \mathbb{Q}^\times_+ \cong \hat{\mathbb{Z}}^\times$, and the proposition becomes the theorem of Kronecker and Weber, $\operatorname{Gal}(\mathbb{Q}^{\mathrm{ab}}/\mathbb{Q}) \cong \hat{\mathbb{Z}}^\times$. With the arithmetic convention, the idele with $p$ at the place $p$ and $1$ elsewhere maps to $\sigma_p$ on $\mathbb{Q}(\zeta_m)$ for $p \nmid m$. This idele is $p \cdot u$ with $u_\ell = p^{-1}$ for $\ell \neq p$ and $u_p = 1$. The principal factor $p$ maps to $1$, so $u$ maps to $\sigma_p$. In general a unit idele $u$ acts on $\zeta_m$ as $\zeta_m \mapsto \zeta_m^{a}$, with $a \equiv u^{-1}$ modulo $m$. With the geometric convention of the source the exponent is $u$.

### Chebotarev and Hecke $L$-functions

**Theorem (Chebotarev density).** Let $L/K$ be a finite Galois extension with group $G$ and let $C \subseteq G$ be a conjugacy class. The set of primes $v$ of $K$, unramified in $L$, with Frobenius class $C$, has Dirichlet density $\#C / \#G$.

Neukirch proves this in Chapter VII, §13. Milne proves it in Chapter VIII, §7. The proof reduces to the cyclic case and then uses the nonvanishing at $s = 1$ of the $L$-functions of the characters of ray class groups. For a character $\psi$ of $J_K / K^\times$ of finite order and a finite set $S$ of places with $\psi$ unramified outside $S$, the partial $L$-function is
$$L_S(s, \psi) = \prod_{v \notin S} (1 - \psi(\pi_v) q_v^{-s})^{-1}, \qquad \operatorname{Re} s > 1,$$
with $\pi_v$ a uniformiser at $v$. Hecke proved that $L_S(s, \psi)$ has a meromorphic continuation to $\mathbb{C}$, holomorphic and nonzero at $s = 1$ for $\psi \neq 1$. Tate gave the idelic proof in his thesis, printed as Chapter XV of Cassels and Fröhlich, *Algebraic Number Theory* (Academic Press, 1967). Neukirch treats Hecke characters and Hecke $L$-series in Chapter VII, §§6 to 8. The source proves only the part on the real line near $s = 1$ (Section 5).
