---
title: Galois conjugates of the lift
lean:
  - New/OneLift/HeckeValues/CharacterLift.lean
decls:
  - New.schurJet_rename_perm
  - New.onHom_mul_scalarFin_inv
  - New.stdLineHom
  - New.LValueData.map_pairWeilFinite_blockDatum
  - New.LValueData.map_trivialLift
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Galois conjugates of the lift

The values of $\varphi_X$ are complex numbers. This section shows how an automorphism $\sigma$ of $\mathbb{C}$ acts on them, when there are no twist places and the rank is even. Up to a few explicit factors, the conjugate of a coordinate of $\varphi_X$ is a coordinate of the lift $\varphi_Y$ of the conjugate character, with the infinite places permuted. The factors are a power of a number $t$ with $|t| = \Omega^{-1/2}$, a nonzero constant $l$, a value of a character and a ratio of multipliers of the Weil representation. The chapter [Hecke values of character lifts](/chapter/hecke-values/) uses this law to bound the size of the algebraic parts.

In this section $P$ is a set of parameters, $s \in \mathbb{N}$, $E = P.E\,s$ is the CM field of the tower over the imaginary quadratic field $K = K\,P$, and $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$. The tool is a jet conjugation (`IsJetConjugation`) from [theta kernels and gauges](/chapter/theta-kernels-gauges/) of Volume 9: a $\sigma$-semilinear map $L$ on the Schwartz space of a standard space, which scales finite translations by an adele $b$, and whose jets at scale $t$ are the $\sigma$-conjugates of the jets at scale `P.jetScale s`. The existence theorem `exists_isJetConjugation` gives $t$, $b$ and $L$ with $|t|^2 = 1/\Omega$, $\Omega = $ `P.bigOmega s`.

### Three lemmas

**Lemma (Renaming the places of a jet).** Let $\kappa$ be a weight indexed by a finite set $\Phi$ that fits the ranks $1$ and $N$, let $e$ be a permutation of $\Phi$, and let $F$ be a power series in the variables $z_{\tau, a, u}$. Then

$$S_\kappa\big(F \circ (e^{-1} \times \mathrm{id})\big) = \text{the matrix } S_{\kappa\circ e^{-1}}(F) \text{ with rows and columns permuted by } e.$$

Lean: `New.schurJet_rename_perm` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Compare the entries at $(i, j)$. Each entry is the jet of the series along an entry of the Schur matrix, and the Schur matrix is a product over $\tau \in \Phi$ (`schur_apply_eq_prod`). Reindex the product along $e^{-1}$ (`Equiv.prod_comp`). The jet along a polynomial commutes with an injective renaming of the variables (`jet_rename`). $\square$

**Lemma (Scalars).** For $g \in U(1)(\mathbb{A}_f)$, $h \in G_f$ and a unitary finite adele $z$, the image of $((1, g z^{-1}), (1, h))$ in the group of $\mathrm{Hom}(W, V)$ is the image of $((1, g), (1, h))$ times the scalar $z$.

Lean: `New.onHom_mul_scalarFin_inv` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* $U(1) \times U(N)$ acts on columns by $x \mapsto h x g^{-1}$, so $g z^{-1}$ acts as the scalar $z$ on the columns. The map `G.onHom` is a homomorphism. $\square$

**Definition (Hom of the line).** `stdLineHom E n` is $\mathrm{Hom}(W, V)$ for the standard line $W$ and the standard space $V$ of rank $N$. Its signs are all $1$.

Lean: `New.stdLineHom` (New/OneLift/HeckeValues/CharacterLift.lean).

### The conjugate of a kernel datum

**Proposition (Jet conjugation of the block datum).** Let $L$ be a $\sigma$-semilinear map on the Schwartz space of `stdLineHom` that scales translations by $b$. Let $X$ be lift data with no twist places. Assume that there are $l \in \mathbb{C}$ and a unitary finite adele $z$ such that, for every Schwartz-Bruhat function $\Psi$ at the places of $X$,

$$L\big(\mathrm{op}(\Psi)\,v_0\big) = l\cdot\omega(1, z)\,\mathrm{op}(\sigma\circ\Psi)\,v_0,$$

where $\mathrm{op}(\Psi)$ is the Schrodinger operator of $\Psi$ and $v_0$ is the vacuum. Let $N = 2m$. Let $Y$ be lift data with the places of $X$ whose character satisfies $\mu_Y(u) = \sigma(\mu_X(u))$ at the finite points. Then for all $g$, $h$,

$$L\big(\omega_X(g, h) f_X\big) = l\cdot\nu_{V,Y}(\det z^{-1})\cdot\frac{\sigma\Delta}{\Delta}(h')\cdot\omega_Y\big((1, gz^{-1}), (1, h)\big) f_Y,$$

with $f_X$, $f_Y$ the block data, $\omega_X$, $\omega_Y$ the twisted Weil actions of the two pairs, $h'$ the finite component of the image of $(1, 1, h)$, and $\sigma\Delta/\Delta$ = `multiplierRatio σ` the ratio of the conjugate multiplier to the multiplier.

Lean: `New.LValueData.map_pairWeilFinite_blockDatum` (New/OneLift/HeckeValues/CharacterLift.lean).

*Proof.* Step 1 (the data). The block data are $f_X = \mathrm{op}(\Psi_X)v_0$ and $f_Y = \mathrm{op}(\Psi_Y)v_0$ for the residue functions $\Psi_X$, $\Psi_Y$. With no twist places both are the same function, with values $0$ and $1$ (the indicator of the columns that reduce to $e_{i_0}$ at the chosen places). So $\sigma\circ\Psi_X = \Psi_Y$, and the hypothesis gives $L f_X = l\,\omega(1, z) f_Y$.

Step 2 (moving $L$ past $\omega$). The twisted action of a pair is a character $\chi$ of the pair times $\omega\circ$`G.onHom`. Write the image of $(g, h)$ as $(1, g')(1, h')$. Since $L$ scales translations by $b$, it moves past $\omega(1, g')$ and $\omega(1, h')$ with the factors $\sigma\Delta/\Delta$ at $g'$ and at $h'$. By the lemma on scalars, $\omega(1, g')\,\omega(1, z)$ is the action of $(1, gz^{-1})$.

Step 3 (the scalars). The character $\nu_W$ is trivial, so $\chi_X = \nu_{V,X}(u)^{-1}$ with $u = \det g$, and $\chi_Y = (\nu_{V,Y}(u)\,\nu_{V,Y}(\det z^{-1}))^{-1}$. The ratio at $g'$ is $(\sigma\Delta/\Delta(g^{-1})^2)^m$, and its square law (`multiplierRatio_sq`) gives the ratio $\sigma\upsilon/\upsilon$ at $u$. Since $\nu_V = \mu\,\upsilon^m$ and $\mu_Y = \sigma\circ\mu_X$ at finite points, $\sigma(\nu_{V,X}(u)) = \nu_{V,Y}(u)\cdot\sigma\Delta/\Delta(g')$. The ratio is nonzero. So $\sigma(\chi_X)\cdot\sigma\Delta/\Delta(g') = \nu_{V,Y}(\det z^{-1})\,\chi_Y$. Collect the factors. $\square$

### The Galois law

**Theorem (Conjugates of the lift).** Let $S$ be level places with no twist places and $\sigma \in \mathrm{Gal}(\mathbb{C}/K)$. There are $t, l \in \mathbb{C}$ and a unitary adele $u$ with $|t| = \Omega^{-1/2}$ and $l \neq 0$ such that the following holds. Let $X$ be lift data on $S$ with $N = 2m$, let $e = $ `placePerm s σ` be the permutation of the infinite places by $\sigma$, and let $\mu$ be a character of weight $-(\ell_{e^{-1}\tau} + N/2)$ with tame part $\psi$ trivial off the places, such that $\mu(v) = \sigma(\mu_X(v))$ at the finite points. Let $Y$ be the data on $S$ with character $\mu$ and row lengths $\tau \mapsto \ell_{e^{-1}\tau}$, and put $D = \sum_\tau \ell_\tau$. Then for every $h$ and every index $i$,

$$\sigma\big(\mathrm{jetScale}^D\,\varphi_X(h)_i\big) = t^D\cdot l\,\nu_{V,Y}(u)\cdot\frac{\sigma\Delta}{\Delta}(h')\cdot\varphi_Y(h)_{i\circ e^{-1}}.$$

Lean: `New.LValueData.map_trivialLift` (New/OneLift/HeckeValues/CharacterLift.lean).

The constants $t$, $l$ and $u$ depend on $S$ and $\sigma$ only, not on $X$.

*Proof.* Step 1 (the constants). Take $t$, $b$, $L$ from `exists_isJetConjugation` for `stdLineHom`. The places of $S$ are disjoint from their conjugates, so `exists_map_schrodingerOp` gives $l \neq 0$ and $z$ with the hypothesis of the proposition. Put $u = \det z^{-1}$. From $|t|^2 = 1/\Omega$ follows $|t| = \Omega^{-1/2}$.

Step 2 (reduction to the terms). By definition $\varphi_X$ is the class sum of $\theta_X(g)$ over $U(1)(E)\backslash U(1)(\mathbb{A}_f)/K_M$. By the translation lemma of Section 3, $\varphi_Y$ is the class sum of $\theta_Y(gz^{-1})$ over the same classes; $X$ and $Y$ have the same places, hence the same chosen level. An automorphism of $\mathbb{C}$ commutes with a finite sum, and the weights $1/\#\mathrm{Aut}$ are rational. So it suffices to prove, for each $g$,

$$\sigma(\mathrm{jetScale})^D\,\sigma\big(\theta_X(g)(h)_i\big) = c\cdot\theta_Y(gz^{-1})(h)_{i\circ e^{-1}}, \qquad c = t^D\, l\,\nu_{V,Y}(u)\,\frac{\sigma\Delta}{\Delta}(h').$$

Step 3 (the term). Let $f = \omega_X(g, h) f_X$. By the scale lemma of Section 3, the left side is $\sigma$ of the $i$-th row sum of $S_{\kappa_X}(\mathrm{jet}_{\mathrm{jetScale}} f)$. The jets of $L f$ at scale $t$ are the $\sigma$-conjugates of the jets of $f$, with the infinite places renamed along $e$. By the lemma on renaming, this turns $\kappa_X$ into $\kappa_X\circ e^{-1} = \kappa_Y$ and the index $i$ into $i\circ e^{-1}$. So the left side is the $(i\circ e^{-1})$-th row sum of $S_{\kappa_Y}(\mathrm{jet}_t\, L f)$. By the proposition, $L f$ is the scalar $l\,\nu_{V,Y}(u)\,\sigma\Delta/\Delta(h')$ times $\omega_Y((1, gz^{-1}), (1, h)) f_Y$. By the scale lemma again, the jets at scale $t$ of this datum have row sums $t^D\,\theta_Y(gz^{-1})(h)$, since $Y$ has the same total row length $D$. $\square$

**Remark (Formalization).** The constants $t$, $l$, $u$ come from existence statements (`exists_isJetConjugation`, `exists_map_schrodingerOp`), so they are chosen and are not explicit. The theorem gives only $|t|$ and $l \neq 0$. The factor $\sigma\Delta/\Delta(h')$ is a value of the multiplier ratio. This section does not bound it.
