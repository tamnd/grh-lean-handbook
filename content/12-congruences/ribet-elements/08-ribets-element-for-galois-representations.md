---
title: Ribet's element for Galois representations
lean:
  - New/Congruences/FirstOrder/RibetElement.lean
decls:
  - New.Selmer.ribet_columns
  - New.Selmer.eventually_exists_map_eq
  - New.Selmer.eventually_exists_map_eq_and_eval_one
  - New.Selmer.IsTameGeneratorFamily.dvd_eval_cyclotomicInv_sub_one
  - New.Selmer.eventually_exists_twistedLattice_and_block_lattices
  - New.Selmer.IsLatticeIn.det_one_sub
  - New.Selmer.exists_length_le_loss_add_crystallineSelmerLength
  - New.Selmer.normLength_addVal_pow
  - New.Selmer.ellVal_add_le_of_addVal_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Ribet's element for Galois representations

This section applies the main lemma to Galois representations. The group is the absolute Galois group of the CM field $E$, and $O$ is a large coefficient ring inside the integers of $\overline{\mathbb{Q}}_\ell$. The output is the bound on the Ribet element that [The denominator bound](/chapter/regular-families-plan/#the-denominator-budget) of the plan needs.

### Background for the Galois case

The hypotheses come from other chapters. Each is stated here in one line.

- A lift setting is a descent pair $V$ with type polynomials at its chosen places above $p_0$ and $p_1$; $t' = \operatorname{rankDiff} V$ is the difference of its ranks, and $r' = \#r$ ([The main summands](/chapter/main-summands/)).
- An auxiliary twist $\psi$ has modulus $Q$ and ramification at most $\mathrm{ram}$ ([The main summands](/chapter/main-summands/)).
- A triangle of primes for $g_0$ is a family of places $w_j$ with tame generators $\tau_j$, elements $\varphi_j$ and types $0 < \mathrm{ty}(j) < t'$, up to $\ell^{\mathrm{halfGap}\,h}$ with bound $\mathrm{halfGap}^{22} h$ ([Tied traces and even classes](/chapter/tied-traces/)).
- A representation of type $V$ has inertia at the chosen places acting through the roots of the rescaled type polynomials and $1$ ([The main summands](/chapter/main-summands/)).
- The crystalline Selmer length of $T$ is the length of its Selmer group with coefficients in $K/O$, of cocycles zero at $\gamma$. The crystalline colength of $T$ modulo $\ell^m$ is the length of $\mathrm{Coc}(T, \ell^m)$ modulo the cocycles that obey the crystalline relations above $\ell$ ([The main summands](/chapter/main-summands/)).

Three results come from the later chapter [From a congruence to a Selmer class](/chapter/denominator-bound/). The file of this section imports them from there, as that chapter fixes the constants of the whole bound.

- $\mathrm{loc} = 4f\,\mathrm{defect}_\ell$, with $f$ the number of infinite places of $E$ and $\mathrm{defect}_\ell$ an explicit number that depends only on the data and $\ell$.
- $e_\ell = t\,v_\ell(\mathrm{oddClassBound}) + 8ft\,v + 2v + ((4t + 1)\mathrm{halfGap}^{22} + \mathrm{halfGap})\,v$, where $v = v_\ell(N)$.
- (Cocycle bound) If the $u_x$ are continuous and unramified off $\ell p_0 p_1$, $Q$, the $w_j$ and their conjugates, and $T$ is unramified off $\ell p_0 p_1$, $Q$ and $\bar Q$, then the cocycles in $\mathrm{Coc}_{\{\tau_j, \bar\tau_j^{-1}\}}(T, \ell^m)$ have length at most the crystalline colength of $T$ modulo $\ell^m$ plus the length of the Selmer cocycles of $T$ modulo $\ell^m$ that vanish at $\gamma$.

### The steps

**Lemma (Coefficient rings).** A polynomial over the integers of $\overline{\mathbb{Q}}_\ell$ is defined over every large coefficient ring $O$. For finitely many such polynomials $H_j$ with $H_j(1) = 1$, the models over $O$ can be chosen with $H'_j(1) = 1$.

Lean: `New.Selmer.eventually_exists_map_eq`, `New.Selmer.eventually_exists_map_eq_and_eval_one` (New/Congruences/FirstOrder/RibetElement.lean).

*Proof.* The finitely many coefficients lie in a finite extension of $\mathbb{Q}_\ell$, and so in its ring of integers. Every large $O$ contains this ring. The value at $1$ does not change under the inclusion, which is injective. $\square$

**Lemma (Ties on the characters).** For a tame generator family with $\varphi_j$ fixing the $\ell^\nu$-th roots of unity, the elements $\varphi_j$ and the inverses of their conjugates act on $O(-e)$ by scalars that are $1$ modulo $\ell^\nu$. If $H(1) = 1$, then the values of $H$ at these scalars are $1$ modulo $\ell^\nu$.

Lean: `New.Selmer.IsTameGeneratorFamily.dvd_eval_cyclotomicInv_sub_one` (New/Congruences/FirstOrder/RibetElement.lean).

*Proof.* The cyclotomic character of $\varphi_j$ is $1$ modulo $\ell^\nu$. For a polynomial $H$, $x - 1$ divides $H(x) - H(1)$. $\square$

This is hypothesis 3 of the main lemma, with $p = \ell^\nu$ and $\varepsilon_j = H_j$.

**Lemma (Models).** Let the $u_x$ be conjugate self-dual, and for $x \in \mathcal{X}$ let $u_x$ have the trace of $\psi \otimes R_x$ plus the characters $O(-e)$, $e < t$. Suppose each $x$ has twisted lattices over all large $O$. Then over every large $O$ there are twisted lattices $R_{0,x}$ that span all matrices, and lattices $u'_x$ in the $u_x$ that are block diagonal on $\mathcal{X}$. Also $\det(1 - R(g))$ is $\det \sum_{g'} \omega_{g'}(R_0(g') - 1)$ for $\omega = -[g]$.

Lean: `New.Selmer.eventually_exists_twistedLattice_and_block_lattices`, `New.Selmer.IsLatticeIn.det_one_sub` (New/Congruences/FirstOrder/RibetElement.lean).

*Proof.* There are finitely many $x$, so one large $O$ serves all of them. The traces agree with those of the block sum, so the semisimple representations agree, and a lattice can be chosen block by block. The second claim holds because $1 - R_0(g) = -(R_0(g) - 1)$ and the determinant does not depend on the lattice. $\square$

**Lemma (The block cost).** Let the classes of local lattices above $\ell$ contain the restrictions of all $u_x$ and of the summands. Let the normalised defects have sum at most $r' \cdot \mathrm{loc}$, and let the crystalline Selmer length $\mathrm{sel}_T$ of $T$ be finite. Then the cocycles of $T$ in $K/O$ that obey the relations, and vanish at the $\tau_j$, at the inverses of their conjugates and at $\gamma$, have length at most $b_0 = \mathrm{loss}_T + \mathrm{sel}_T$. The normalised sum of $\mathrm{loss}_T$ and of the colengths of the $O(-e)$ is at most $r' \cdot \mathrm{loc}$.

Lean: `New.Selmer.exists_length_le_loss_add_crystallineSelmerLength` (New/Congruences/FirstOrder/RibetElement.lean).

*Proof.* By the cocycle bound, modulo each $\ell^M$ the length is at most the crystalline colength plus the Selmer length. The colength is at most the loss $\mathrm{loss}_T$, the sum of the defects of $T$ above $\ell$. Both terms are finite, so part 4 of the last lemma before the proof of the main lemma gives the bound with coefficients in $K/O$. $\square$

**Lemma (Valuations).** Let $v$ be the $\ell$-adic valuation of $N$, $\mathrm{sep} = \mathrm{halfGap}\,h$, $t' \leq t$ and $h \leq v$. Let $v_O(d)$ be at most the sum of the losses, $\mathrm{sel}_T$, the odd lengths, $t'$ times the tame cost, and $(2t'\,n_{\mathrm{det}} + k + 1)\,v_O(\ell^{\mathrm{sep}})$, with $(k + n_{\mathrm{test}})\,\mathrm{sep} \leq \mathrm{halfGap}^{22} h$ and $n_{\mathrm{det}} \leq 2(k + n_{\mathrm{test}})$. Under the bounds on the odd lengths and the tame cost, the normalised valuation $v_\ell(d)$ satisfies $v_\ell(d) + 2v \leq \mathrm{sel} + 2t'\,\mathrm{ram} + \mathrm{loc} + e_\ell$.

Lean: `New.Selmer.normLength_addVal_pow`, `New.Selmer.ellVal_add_le_of_addVal_le` (New/Congruences/FirstOrder/RibetElement.lean).

*Proof.* The normalised length of $v_O(\ell^m)$ is $m$. Normalise each term and add. The terms in $\ell^{\mathrm{sep}}$ add up to at most a fixed multiple of $\mathrm{halfGap}^{22} h$, and the denominator error $e_\ell$ absorbs them together with the odd lengths and $-2v$. $\square$

### The theorem

**Theorem (Ribet's element for conjugate self-dual representations).** Let $V$ be a lift setting for $\vartheta$, and $\psi$ an auxiliary twist. Write $N$ for the chosen group order and $v = v_\ell(N)$. Let the $w_j$ form a triangle of primes for $g_0$ up to $\ell^{\mathrm{halfGap}\,h}$ with $h \leq v$. Let $u_x$, $x \in Y$, be finitely many conjugate self-dual representations of type $V$, with $(g - \psi(g))(g - 1) = 0$ on inertia above $Q$ and $\bar Q$. For $x \in \mathcal{X}$, let $u_x$ have the trace of $\psi \otimes R_x$ plus the characters $O(-e)$, $e < t'$, where $R_x$ is a main summand with a twisted lattice. Let $\mathcal{J}$ be a trace ideal for $\ell^\nu$ and the ties $\tau_j - 1 - X_j(\varphi_j - 1)H_j(\varphi_j)$, with $H_j(1) = 1$. At one $\pi \in \mathcal{X}$, let the Selmer group of $\psi \otimes R_\pi$ with divisible coefficients have length at most $\mathrm{sel} < \infty$. Then some $d$ is a common Ribet coefficient at $\pi$ for the functions $\det(1 - u_x(g))$, and
$$v_\ell(d) + 2v \leq \mathrm{sel} + 2t'\,\mathrm{ram} + r'\,\mathrm{loc} + e_\ell.$$

Lean: `New.Selmer.ribet_columns` (New/Congruences/FirstOrder/RibetElement.lean).

*Proof.* Choose $O$ large enough for the lemma on coefficient rings and the lemma on models. Use the lattices $u'_x$ for the $u_x$, and $T = \psi \otimes R_{0,\pi}$ for the block. The characters are $\xi_e = O(-e)$. The element $g_0$ separates them up to $\ell^{\mathrm{halfGap}\,h}$, and a power of $\ell^{\mathrm{halfGap}\,h}$ serves as $C$ in hypothesis 4. The inertial element $\gamma_x$ acts on the twisted lattice by $\zeta'_x$ with $\zeta'_x - 1$ a unit, and trivially on the characters, which gives hypothesis 2. Hypothesis 3 is the lemma on ties. The block cost gives hypothesis 5 with $b_0 = \mathrm{loss}_T + \mathrm{sel}_T$. The tame places give hypothesis 6. The triangle of primes gives the triangle costs $b_e$ and detection by the set $s$ of test points, which is hypothesis 7. The main lemma gives $c$, and the lemma on models turns $\det(1 - u_x(g))$ into the combination with $\omega = -[g]$. The lemma on valuations turns the bound of the main lemma into the stated bound. $\square$

**Remark (Formalization).** The coefficient ring $O$ is not fixed in advance. The statement holds over every large $O$, in the sense of a filter on coefficient rings, and the proof picks one. The valuation $v_\ell$ is normalised so that $O/\ell$ has length $1$.
