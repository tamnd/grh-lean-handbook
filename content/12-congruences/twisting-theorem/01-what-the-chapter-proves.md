---
title: What the chapter proves
lean:
  - New/Congruences/Selmer/StickelbergerSystems.lean
  - New/Congruences/Selmer/ClassSums.lean
  - New/Congruences/Selmer/LValueSystems.lean
  - New/Congruences/Selmer/StickelbergerLine.lean
  - New/Congruences/Selmer/Line.lean
  - New/Congruences/Selmer/RootsOfUnity.lean
  - New/Congruences/Selmer/GeneralTheorem.lean
  - New/Congruences/Selmer/MainSummands.lean
  - New/Congruences/Selmer/TwistingTheorem.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## What the chapter proves

This chapter proves the twisting theorem. For finitely many representations like main summands, it finds one anticyclotomic character $\tau$ of $\ell$-power order, ramified at new primes, such that each power $\xi = \tau^j$, $1 \leq j \leq m$, has three properties: its ramification is small, the Selmer groups of the twisted representations are short, and the ratios of twisted to untwisted $L$-values are barely divisible by $\ell$. The bound for all three is $e'_\ell = (4f + 3)\, r\, v(\mathrm{chosenGroupOrder}) + 2^{-\ell}$.

### Its place in the plan

[The chain of the proof](/chapter/regular-families-plan/#the-chain-of-the-proof) states the twisting theorem (`New.Selmer.exists_mFoldTwist_hasDivisibleSelmerLengthLe`) as step 3 of the proof of the existence of regular families, and points here for its proof. The last section of this chapter states it again and proves it. The proof has two parts.

- The *Selmer part* starts from [tied Selmer groups](/chapter/tied-selmer-groups/). Its file Line uses the descent of [the descent](/chapter/tied-selmer-groups/#the-descent), the sharp polynomial of [one system for all twists](/chapter/tied-selmer-groups/#one-system-for-all-twists) and the tie polynomial of [untied classes](/chapter/tied-selmer-groups/#untied-classes). Its file MainSummands uses the bound of [the global term](/chapter/tied-selmer-groups/#the-global-term).
- The *$L$-value part* is new here. The $L$-values of a ramified critical pair, as the twist varies, form a *Stickelberger system*: elements $\Theta_Q$ of group rings with a norm relation by Euler factors.

Both parts lead to the same problem. There are polynomials $P_k$ in variables $X_v$, one for each auxiliary prime $v$, and points $x$ with $v(x_v) \geq r$ at which $v(P_k(x))$ is small. The problem is to find roots of unity $\zeta_v$ such that $v(P_k(\zeta - 1))$ is still small. A harmonic-sum argument and an average over roots of unity solve it.

[Tied traces and even classes](/chapter/tied-traces/) gives the auxiliary primes, the tied primes and the characters $\prod_j y_j^{h_j}$. Its part 1 is used in the files Line and StickelbergerLine, and its part 2 (the condition `IsAuxTwist`) in TwistingTheorem. [The main summands](/chapter/main-summands/) gives the hypothesis `IsMainSummandLike` and the Selmer lengths `HasDivisibleSelmerLengthLe`. [The local loss at ℓ](/chapter/local-loss/) gives the lattices used by MainSummands.

### What it uses

Each section opens with the background it uses, each piece in one line with a link. The direct imports of the files of this chapter are in earlier chapters of this volume or in other volumes. MainSummands imports LocalLattices, which `volume.yaml` puts in the earlier chapter [the local loss at ℓ](/chapter/local-loss/), and TwistingTheorem imports EvenClasses of [tied traces and even classes](/chapter/tied-traces/). No file imports a file of a later chapter.

### Notation

Fix a prime $\ell$. Let $\Omega$ be the algebraic closure of $\mathbb{Q}$, $E \subseteq \Omega$ a CM field and $G = \mathrm{Gal}(\Omega/E)$. For a place $v$ of $E$, $\bar v$ is its conjugate, $\mathrm{N}v = v.q$ its norm, and for a set $Q$, $\bar Q$ is the set of conjugates. The valuation $v$ on $\bar{\mathbb{Q}}_\ell$ (`New.ellVal`) has $v(\ell) = 1$, takes values in $[0, \infty]$ and is $0$ on elements of norm at least $1$. The ring of integral elements is $\bar{\mathbb{Z}}_\ell$ (`New.intQpBar`). For a polynomial $g = \sum_i y_i Y^i$ over $\bar{\mathbb{Z}}_\ell$ and $\rho \geq 0$, the Gauss valuation is $v_\rho(g) = \min_i (v(y_i) + \rho i)$; for several variables the minimum runs over monomials and $i$ is the total degree. The isomorphism $\iota_\ell \colon \mathbb{C} \to \bar{\mathbb{Q}}_\ell$ is fixed (`PadicIso`). Lengths over a coefficient ring $O$ are normalized by $\mathrm{len}(O/\ell) = 1$ (`CoeffRing.normLength`).

A set $Q$ of finite places is *auxiliary* for $S$ (`New.IsAuxiliary`) if its places have prime norm, no place of $Q$ or $\bar Q$ lies in $S$, and $\bar Q \cap Q = \emptyset$. A character $\psi$ of $G$ is a *character for $Q$* if `IsFromU1` (places above $\ell$) $Q$ $\psi$ holds: $\psi$ is locally constant and $\psi(\mathrm{Art}\, y) = \eta(y/\bar y)$ for an idele class character $\eta$ of modulus $Q$ that is trivial above $\ell$ ([auxiliary primes](/chapter/tied-traces/#auxiliary-primes)).

### A sketch

Fix the bad places $S_0$ (those dividing $\ell p_0 p_1 N$) and the tame generator $g_0$ at a chosen place $w_0 \nmid \ell$. Each main summand gives a *Selmer datum* $T_i$ with a number $\beta_{T_i} \leq c$, and each ramified critical pair and sign gives a Stickelberger system $Y_k$ with a number $\beta_k$. The general theorem gives a set $Q$ and a character $\psi$ such that for each $j \leq m$: $\mathrm{len}\, \mathrm{Sel}_Q(T_i \psi^j) \leq \beta_{T_i} + \varepsilon$, $v(\psi^j(\Theta_Q)) \leq \beta_k + \varepsilon$, and $\sum_w v(\psi^j(\gamma_w) - 1) \leq \varepsilon$. Class field theory turns $\psi$ into a tame character $\tau$, and the bound for $\psi^j(\Theta_Q)$ becomes a bound for the ratio of $L$-values.

The general theorem is proved in four steps. First, tied primes $J$ from [the descent](/chapter/tied-selmer-groups/#the-descent) give polynomials for the Selmer data. Second, the norm relation gives polynomials for the systems. Third, on a line through $0$ the polynomials have points of small value (sections 5 and 6). Fourth, roots of unity replace the points (section 7).

The chapter reports what the declarations state and how the proofs go. Lean accepts them, if the reported checks hold.
