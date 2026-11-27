---
title: Colength, index and the target lattice
lean:
  - New/Reduction/Lattices/Colength.lean
  - New/Reduction/Lattices/TwistedLattice.lean
  - New/Reduction/IntegralTargetForms.lean
  - New/UpperBound/Divisibility/LocalDivisibility.lean
decls:
  - New.ColengthDvd
  - New.ColengthDvd.comap
  - New.ColengthDvd.map
  - New.TwistedLattice.IndexLe
  - New.TwistedLattice.indexLe_of_colengthDvd
  - New.TwistedLattice.indexLe_card_mul
  - New.Data.targetLattice
  - New.Data.mem_integralVectors_targetLattice
  - New.GaugeLe.zpow_neg_smul
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Colength, index and the target lattice

Part (b) of Theorem A is a statement about the index of a family in the target lattice. Its proof moves a colength bound from source forms to target forms and then turns it into an index. This section states the notions and the rules that the proof uses. All of them are proved in Volume 1 or in [divisibility prime by prime](/chapter/divisibility/). The last subsection works out a small case.

### Colength

**Definition (Colength divides).** Let $O$ be a commutative ring, $M$ and $N$ submodules of an $O$-module $V$, and $z \in O$. The relation $\mathrm{ColengthDvd}(M, N, z)$ holds if for every finite family $\Phi_1, \dots, \Phi_n$ in $M$ there is a square matrix $u$ over $O$, indexed by $\{1,\dots,n\}$, with $\det u \mid z$ and $\sum_k u_{ik}\Phi_k \in N$ for every $i$.

Lean: `New.ColengthDvd` (New/Reduction/Lattices/Colength.lean).

The definition asks for no inclusion $N \subseteq M$ and no basis. Over a discrete valuation ring, and for $M$ finitely generated with $N \subseteq M$, it says that the length of $M/N$ is at most the valuation of $z$ ([colength](/chapter/twisted-lattices/#colength)).

**Lemma (Pull back).** Let $f : U \to V$ be $O$-linear, and let $M', N'$ be submodules of $U$. Suppose $\mathrm{ColengthDvd}(M, N, z)$, $f(M') \subseteq M$, and for every $x \in M'$ with $f(x) \in N$ also $x \in N'$. Then $\mathrm{ColengthDvd}(M', N', z)$.

Lean: `New.ColengthDvd.comap` (New/Reduction/Lattices/Colength.lean).

**Lemma (Push forward).** Let $f : V \to U$ be $O$-linear, and let $M', N'$ be submodules of $U$. Suppose $\mathrm{ColengthDvd}(M, N, z)$, $M' \subseteq f(M) + N'$ and $f(N) \subseteq N'$. Then $\mathrm{ColengthDvd}(M', N', z)$.

Lean: `New.ColengthDvd.map` (New/Reduction/Lattices/Colength.lean).

Both are proved in [colength](/chapter/twisted-lattices/#colength). The proof of the first applies the hypothesis to the family $f(\Phi_k)$ and uses that $M'$ is closed under combinations. The proof of the second writes $\Phi_k = f(x_k) + y_k$ with $x_k \in M$ and $y_k \in N'$, and applies the hypothesis to the family $x_k$.

### The index

A twisted lattice on a complex space $V$ has a set of twists $\xi$, a linear map $\Theta_\xi$ for each twist, a rule that says which twists are allowed at a prime $\ell$, and for each twist and each $\iota$ a lattice $\Lambda_{\xi,\iota}$. A vector $y \in V$ is integral at $\iota$ above $\ell$ if $\Theta_\xi y \in \Lambda_{\xi,\iota}$ for every twist $\xi$ allowed at $\ell$. These vectors form an $\mathcal{O}_\iota$-module ([twisted lattices, index and covolume](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume)).

**Definition (Index at most $\delta$).** A finite family $y = (y_k)_{k\in I}$ in $V$ has index at most $\delta$ if there are real numbers $e(\ell) \geq 0$, one for each natural number $\ell$, with two properties. For every finite set $U$ of primes, $\sum_{\ell\in U}e(\ell)\log\ell \leq \delta$. For every $\iota$ above $\ell$ there is a square matrix $u$ over $\mathcal{O}_\iota$, indexed by $I$, with $\|\iota(\det u)\| \geq \ell^{-e(\ell)}$ and with each $\sum_k u_{ik}y_k$ integral at $\iota$.

Lean: `New.TwistedLattice.IndexLe` (New/Reduction/Lattices/TwistedLattice.lean).

The matrix may depend on $\iota$. It does not depend on the twist.

**Theorem (Index from colength).** Let $y_1, \dots, y_n$ be a family in $V$ and $e : \mathbb{N} \to \mathbb{R}$ with $e(\ell) \geq 0$ for all $\ell$ and $\sum_{\ell\in U}e(\ell)\log\ell \leq \delta$ for every finite set $U$ of primes. Suppose that for every $\iota$ above $\ell$ there are a natural number $j \leq e(\ell)$ and an $\mathcal{O}_\iota$-submodule $M$ of $V$ such that every $y_i \in M$ and $\mathrm{ColengthDvd}(M, V_\iota, \ell^j)$, where $V_\iota$ is the module of vectors integral at $\iota$. Then $y$ has index at most $\delta$.

Lean: `New.TwistedLattice.indexLe_of_colengthDvd` (New/Reduction/Lattices/TwistedLattice.lean).

This is proved in [colength](/chapter/twisted-lattices/#colength). The colength gives a matrix $u$ with $\det u \mid \ell^j$ that carries $y$ into $V_\iota$, and a divisor of $\ell^j$ in $\mathcal{O}_\iota$ has absolute value at least $\ell^{-j} \geq \ell^{-e(\ell)}$.

**Theorem (Index of a union).** Let $t$ be a finite set of indices, and for $s \in t$ let $A_s \subseteq V$. Suppose that for each $s \in t$ every finite family with all members in $A_s$ has index at most $\delta$. Let $y$ be a finite family with each member in some $A_s$, $s \in t$. Then $y$ has index at most $\#t\cdot\delta$.

Lean: `New.TwistedLattice.indexLe_card_mul` (New/Reduction/Lattices/TwistedLattice.lean).

This is proved in [twisted lattices, index and covolume](/chapter/twisted-lattices/#twisted-lattices-index-and-covolume), by induction on $t$. The family splits into the members of $A_s$ and the rest. Indices add over a union of two families, as the numbers $e(\ell)$ add and the two matrices go into diagonal blocks.

### The target lattice

**Definition (The target lattice).** The target lattice is the twisted lattice on $T$ whose twists are the $m$-fold twists $\vartheta$. The map at $\vartheta$ is $\Theta_\vartheta$, to the forms on $Y_m$ of the level and character of $\vartheta$. The lattice at $\iota$ is the module of forms integral at the place of $\iota$. The twist $\vartheta$ is allowed at $\ell$ if $\ell$ is prime to $\mathrm{Nm}\,Q(\vartheta)$.

Lean: `New.Data.targetLattice` (New/Reduction/IntegralTargetForms.lean).

The definition has more fields: the coordinates for the trivial twist and their Gram matrix. Part (b) does not use them. [The target lattice](/chapter/integral-target-forms/#the-target-lattice) gives the full definition.

**Lemma (Integral target forms).** Let $y \in T$ and let $\iota$ lie above $\ell$. Then $y$ is integral at $\iota$ in the target lattice if and only if $\Theta_\vartheta y$ is integral at the place of $\iota$ for every $m$-fold twist $\vartheta$ with $\ell$ prime to $\mathrm{Nm}\,Q(\vartheta)$.

Lean: `New.Data.mem_integralVectors_targetLattice` (New/Reduction/IntegralTargetForms.lean).

*Proof.* This is the definition of the integral vectors of a twisted lattice, applied to the target lattice. $\square$

### Removing a power of the prime

The last rule is a gauge rule. It turns a divisibility by a real power of $p$ into integrality after a multiplication by an integer power.

**Lemma (Removing a power).** Let $p$ be a prime, $\iota_p : \mathbb{C} \to \mathbb{C}_p$ an embedding, $d$ a finite adelic point, $r$ real and $\beta$ an integer with $\beta \leq -r$. If a form $\varphi$ satisfies $\mathrm{GaugeLe}(d, p^r, \varphi)$, then $\mathrm{GaugeLe}(d, 1, p^{-\beta}\varphi)$.

Lean: `New.GaugeLe.zpow_neg_smul` (New/UpperBound/Divisibility/LocalDivisibility.lean).

*Proof.* The gauge is homogeneous: the gauge of $c\,\varphi(g)$ is $\|\iota_p c\|$ times the gauge of $\varphi(g)$. As $\|\iota_p p^{-\beta}\| = p^{\beta}$, the form $p^{-\beta}\varphi$ has gauge at most $p^{\beta + r}$. As $\beta + r \leq 0$, this is at most $1$. $\square$

The proof of part (b) uses the lemma with $r = \mathrm{err}(\ell) - \mathrm{gain}_\ell$ and $\beta = g_\ell = \lfloor\mathrm{gain}_\ell - \mathrm{err}(\ell)\rfloor$. Then $\beta \leq \mathrm{gain}_\ell - \mathrm{err}(\ell) = -r$.

### A small case

**Example (One prime, one twist).** Let $V = \mathbb{C}$ with one twist, $\Theta = \mathrm{id}$, allowed at every prime, and $\Lambda_\iota = \mathcal{O}_\iota$. Fix a prime $\ell_0$ and put $y_1 = \ell_0^{-1}$. Take $M = \ell_0^{-1}\mathcal{O}_\iota$ at $\iota$ above $\ell_0$, and $M = \mathcal{O}_\iota$ at the other $\iota$. At $\iota$ above $\ell_0$, the $1\times1$ matrix $(\ell_0)$ carries every family of $M$ into $\mathcal{O}_\iota$, so $\mathrm{ColengthDvd}(M, \mathcal{O}_\iota, \ell_0)$ with $j = 1$. At the other $\iota$, the identity matrix works with $j = 0$. With $e(\ell_0) = 1$ and $e(\ell) = 0$ otherwise, the theorem on index from colength gives index at most $\log\ell_0$. Any real number $e(\ell_0) \geq 1$ also works, with a weaker bound, as the theorem only asks $j \leq e(\ell)$. In part (b), $e(\ell) = D_X\,\mathrm{err}(\ell)$ is real and $j$ is a natural number below it.
