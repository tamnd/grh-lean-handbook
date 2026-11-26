---
title: Definite lifts and the Galois law
lean:
  - Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean
  - Lib/Weil/CompactLift/ThetaKernelDefs.lean
  - Lib/Weil/CompactLift/DefiniteThetaLift.lean
  - Lib/Weil/DualPair/WeilAction.lean
  - Lib/Weil/DualPair/GaloisLaw.lean
  - Lib/Weil/TameGaussSum.lean
decls:
  - New.AlgForm
  - New.IsLiftWeight
  - New.Kernel
  - New.Kernel.lift
  - New.Kernel.lift_equivariant
  - New.thetaKernel
  - New.IsHCParam.paramsCorrespond_iff
  - New.exists_lift_ofAlgForm_eq_smul
  - New.Space.IsThetaLift
  - New.isThetaLift_thetaKernel
  - New.multiplierRatio
  - New.Space.ScalesTranslations
  - New.Space.ScalesTranslations.isUnit
  - New.Space.ScalesTranslations.map_omega
  - New.Space.ScalesTranslations.exists_map_schrodingerOp
  - New.Exchange.exists_local_gauss_sum
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Definite lifts and the Galois law

This section treats three topics. The first is the theta lift between two definite unitary groups. There the real groups are compact, and the lift is a finite class sum. The second is a Galois law for the finite part of the Weil representation. The third is a local Gauss sum.

### Algebraic forms

Let $I_n$ be the standard definite space with $n$ coordinates, all signs $+1$ and the standard lattice. Its real group is compact, so an automorphic form on it is determined by finite data. A weight $(\kappa, e)$ gives at each real place $\tau$ a Young diagram and an integer $e_\tau$. Here $\kappa_\tau(h)$ is the number of columns of height $h$. The weight gives a finite dimensional representation $\rho_{\kappa, e}$ of the rational points on a space $W_n(\kappa)$.

**Definition (Algebraic form).** An algebraic form of weight $(\kappa, e)$ is a function $\varphi$ on the finite points $G_f$ of $I_n$ with values in $W_n(\kappa)$, such that $\varphi(\gamma g) = \rho_{\kappa, e}(\gamma)\varphi(g)$ for all rational points $\gamma$, and such that $\varphi$ is right invariant under an open subgroup.

Lean: `New.AlgForm` (Lib/Adelic/AutomorphicForms/SmoothAlgebraicForms.lean).

These are the algebraic modular forms of Gross (Israel J. Math. 113 (1999) 61-93). A form $\varphi$ gives a function $F_\varphi$ on the adelic group: $F_\varphi(g) = \langle v^+, \rho(g_\infty^{-1})\varphi(g_f) \rangle$, where $v^+$ is a highest vector for a parameter $l$ of the weight. For a level $K$, the integral over $\Gamma \backslash G_f$ is a finite sum over the double cosets, with the measure that gives $K$ volume $1$.

### Lifting weights

**Definition (Lift weight).** Let $n < n'$. The weight $(\kappa, e)$ in rank $n$ goes up to rank $n'$ along the exponent $e_b$ if three conditions hold. No column of $\kappa_\tau$ has a height strictly between $n$ and $n'$. The rank grows, $n < n'$. At each place, $e_\tau = e_{b,\tau} + \kappa_\tau(n)$.

Lean: `New.IsLiftWeight` (Lib/Weil/CompactLift/ThetaKernelDefs.lean).

The last condition reflects that in rank $n$ the columns of height $n$ give a power of the determinant. The same diagram $\kappa$ then makes sense in rank $n'$, with a new exponent $e_a$. For the classical correspondence of highest weights in the Fock model, see Kashiwara and Vergne (Invent. Math. 44 (1978) 1-47).

**Proposition (Parameters of a lift weight).** Let $(\kappa, e_c)$ go up from rank $n$ to rank $n'$ along $e_b$, and let $l$ be a parameter of $(\kappa, e_c)$, that is, twice its Harish-Chandra parameter in some order. Then $l$ and $l'$ correspond for the definite signs and characters of weights $e_a$ and $e_b$, in the sense of the block rule of Section 4, if and only if $l'$ is a parameter of $(\kappa, e_a)$.

Lean: `New.IsHCParam.paramsCorrespond_iff` (Lib/Weil/CompactLift/DefiniteThetaLift.lean).

So the edges of Section 4 exist between the two definite groups for exactly the weights of the Kashiwara and Vergne correspondence.

### Abstract kernels and their lifts

**Definition (Kernel of algebraic forms).** Let $K$ be a level and let $X$ be a complex vector space. A kernel from weight $(\kappa, e)$ in rank $n$ to weight $(\kappa, e_a)$ in rank $n'$, with data in $X$, consists of a representation $\omega$ of $G_f \times G'_f$ on $X$ and a linear map $J$ from $X$ to the linear maps $W_n(\kappa) \to W_{n'}(\kappa)$. Two conditions hold. First, for rational points $\gamma, \delta$ and all $f \in X$ and $v$,
$$J(\omega(\gamma, \delta)f)(\rho_{\kappa, e}(\gamma)v) = \rho_{\kappa, e_a}(\delta)\, J(f)(v).$$
Second, every $f$ has an open stabilizer in $G_f \times G'_f$.

Lean: `New.Kernel` (Lib/Weil/CompactLift/ThetaKernelDefs.lean).

**Definition (Algebraic lift).** For a kernel $(\omega, J)$, a datum $f$ and an algebraic form $\varphi$ of weight $(\kappa, e)$, the lift is the function
$$\mathcal{L}_f \varphi(h) = \int_{\Gamma \backslash G_f} J(\omega(g, h)f)(\varphi(g))\, dg,$$
where the integral is the finite class sum for the measure with $\operatorname{vol}(K) = 1$. It is an algebraic form of weight $(\kappa, e_a)$, and it is bilinear in $f$ and $\varphi$.

Lean: `New.Kernel.lift` (Lib/Weil/CompactLift/ThetaKernelDefs.lean).

The integrand is left invariant under the rational points by the first condition, and it is smooth by the second. The equivariance in $h$ follows from the first condition at $(1, \delta)$.

**Proposition (Equivariance).** For $a \in G_f$ and $b \in G'_f$, the lift with datum $\omega(a, b)f$ of the right translate of $\varphi$ by $a$ is the right translate by $b$ of $\mathcal{L}_f\varphi$.

Lean: `New.Kernel.lift_equivariant` (Lib/Weil/CompactLift/ThetaKernelDefs.lean).

*Proof.* Substitute $g \mapsto g a$ in the class integral. The integral is invariant under right translation, since the measure is a Haar measure. $\square$

### The kernel of jets

The kernel that matters comes from the Weil representation of $\operatorname{Hom}(I_n, I_{n'})$. For a finite datum $f$, the theta function $z \mapsto \theta(f)(z)$ in the Fock model is entire in the $n' \times n$ matrices $z_\tau$. Let $c \neq 0$ be a scale. The jet series of $f$ is the Taylor series of $z \mapsto \theta(f)(cz)$ at $0$. Pair it with the Schur polynomial matrix $S_\kappa(z)$, whose rows are indexed by a basis of $W_{n'}(\kappa)$ and whose columns by a basis of $W_n(\kappa)$. The entry at $(i', i)$ of the matrix of jets is $P_{i' i}(\partial)$ applied to the series at $0$, where $P_{i' i}$ is the corresponding entry of $S_\kappa$.

**Definition (Kernel of jets).** Let $(\kappa, e)$ go up from rank $n$ to rank $n'$ along $e_b$, let $c \in \mathbb{C}$, and let $a, b$ be characters of weights $e_a$ and $e_b$. The kernel of jets has data in the finite part of the data on $\operatorname{Hom}(I_n, I_{n'})$, the finite Weil representation $\omega_{a,b}$ as its action, and the matrix of jets with scale $c$ as its map $J$.

Lean: `New.thetaKernel` (Lib/Weil/CompactLift/ThetaKernelDefs.lean).

The first condition of a kernel holds because the theta functional is invariant under rational points, and the Schur polynomials intertwine the action of $\mathrm{GL}_n \times \mathrm{GL}_{n'}$ on polynomials with the representations of weight $\kappa$.

### The harmonic lift is an algebraic lift

**Theorem (Definite lift).** Let $l$ and $l'$ be parameters of $(\kappa, e_c)$ and $(\kappa, e_a)$, let $(\kappa, e_c)$ go up from rank $n$ to rank $n'$ along $e_b$, and let $c \neq 0$. There is a number $\beta$ with the following property. For all characters $a, b$ of weights $e_a, e_b$, every level $K$, every finite datum $f$ and every algebraic form $\varphi$ of weight $(\kappa, e_c)$,
$$\mathcal{L}_{\Phi \otimes f}\, F_\varphi = \frac{\beta}{[K_0 : K \cap K_0]}\, F_{\varphi'}, \qquad \varphi' = \mathcal{L}^{\mathrm{jet}}_f \varphi.$$
Here $\Phi$ is the joint harmonic of $l$ and $l'$, the lift on the left is the analytic lift of Section 3, $K_0$ is the standard level, and $\mathcal{L}^{\mathrm{jet}}$ is the algebraic lift by the kernel of jets at level $K$.

Lean: `New.exists_lift_ofAlgForm_eq_smul` (Lib/Weil/CompactLift/DefiniteThetaLift.lean).

The proof writes the joint harmonic as a multiple of the Fock polynomial $\langle A, S_\kappa(z)\xi \rangle$ of the two highest vectors. The theta function of that polynomial tensored with $f$ is then a coefficient of the matrix of jets. The integral over the compact real group reduces to a class sum, and the change of measure from $K_0$ to $K$ gives the index.

**Remark (Formalization).** The number $\beta$ is not computed, and it is never shown to be nonzero. The theorem is therefore consistent with $\beta = 0$, and then it gives no information on the lift. Where the argument needs a nonzero lift, it must get it from another statement. The index $[K_0 : K \cap K_0]$ is a natural number, and it is $0$ when the index is infinite. Then the factor is $\beta / 0 = 0$ by the convention of the library. For an open $K$ and a compact $K_0$ the index is finite.

### Theta lifts in coefficients

The definite lift also has a description in coefficients. For a linear form $t$ on $W_n(\kappa)$ and an algebraic form $\varphi$, the coefficient of $\varphi$ at $t$ is the function $g \mapsto t(\rho(g_\infty^{-1})\varphi(g_f))$ on the adelic group.

**Definition (Theta lift in coefficients).** A family $k_o$ of maps, indexed by $o$, from finite data and algebraic forms of weight $(\kappa, e)$ to algebraic forms of weight $(\kappa, e')$ computes theta lifts if the following holds. For every polynomial $P$ on the matrices $z_\tau$ and every linear form $t$ on $W_n(\kappa)$ there is a linear form $t'$ on $W_{n'}(\kappa)$ such that for all $o$, $f$, $\varphi$ and $h$,
$$\int_{[I_n]} \theta(\omega_{a_o}(g, h)(P \otimes f))\, \varphi_t(g)\, dg = (k_o(f, \varphi))_{t'}(h).$$

Lean: `New.Space.IsThetaLift` (Lib/Weil/DualPair/WeilAction.lean).

**Theorem (Kernels of jets compute theta lifts).** Let $n$ and $n'$ be positive, let $(\kappa, e)$ go up from rank $n$ to rank $n'$ along $e_b$, let $c \neq 0$ and let $K$ be a level. For a family of characters $a_o$ of weights $e_a$ and $e_b$ at the two ranks, the algebraic lifts by the kernels of jets compute theta lifts.

Lean: `New.isThetaLift_thetaKernel` (Lib/Weil/CompactLift/DefiniteThetaLift.lean).

The proof reduces to the highest coefficient. The translates of the highest coefficient span all linear forms, and the claim is linear in $t$. For a translate, the lift with datum $P$ is a convolution over the real points of the lift with the harmonic datum, by the edge property of Section 4. The theorem on the definite lift then applies.

**Remark (Formalization).** Classically, the existence of $t'$ is a consequence of Howe's $(\mathrm{GL}_{n'}, \mathrm{GL}_n)$ duality on polynomials on matrices (Howe, J. Amer. Math. Soc. 2 (1989) 535-552). The formal statement gives only the existence of $t'$ for each $P$ and $t$. It does not state the multiplicity one decomposition of the polynomials, and it does not use it. The form $t'$ can be $0$, for example when $P$ has no component of type $\kappa$, so the statement does not say that any lift is nonzero.

### The Galois law

Let $V$ be a space, and let $\sigma$ be a ring endomorphism of $\mathbb{C}$. Shimura proved that the automorphisms of $\mathbb{C}$ act on theta functions with complex multiplication through explicit adelic operations (Shimura, Duke Math. J. 43 (1976) 673-696). The statement here is a form of that law for the finite part of the Weil representation. The finite part is the span of the translates of the vacuum under the finite Heisenberg operators.

**Definition (Scaling of translations).** Let $L$ be a $\sigma$-semilinear map on the data of $V$, and let $b$ be a finite adele. Then $L$ scales translations by $b$ if three conditions hold. First, $\sigma(\psi(z)) = \psi(b \bar{b} z)$ for the self-dual additive character $\psi$ and all finite adeles $z$. Second, $L$ maps the finite part to itself. Third, $L(\varrho(x) f) = \varrho(b x) L(f)$ for $f$ in the finite part and every finite vector $x$, where $\varrho$ is the Heisenberg translation.

Lean: `New.Space.ScalesTranslations` (Lib/Weil/DualPair/GaloisLaw.lean).

**Lemma (Units).** If $L$ scales translations by $b$, then $b$ is a unit of the finite adeles.

Lean: `New.Space.ScalesTranslations.isUnit` (Lib/Weil/DualPair/GaloisLaw.lean).

Let $\Delta$ be the multiplier of the finite Weil representation of [the Weil representation from a vacuum](/chapter/weil-representation/). It is a function on the finite points with $|\Delta(g)|^2$ a natural number.

**Definition (Multiplier ratio).** For a finite point $g$, the multiplier ratio is $\sigma(\Delta(g)) / \Delta(g)$.

Lean: `New.multiplierRatio` (Lib/Weil/DualPair/GaloisLaw.lean).

**Theorem (Galois law).** Let $L$ scale translations by $b$. For every finite point $g$ and every $f$ in the finite part,
$$L(\omega(1, g)f) = \frac{\sigma(\Delta(g))}{\Delta(g)}\, \omega(1, g)L(f).$$

Lean: `New.Space.ScalesTranslations.map_omega` (Lib/Weil/DualPair/GaloisLaw.lean).

*Proof sketch.* Write $b = u a$ with $u$ a unitary adele and $a$ an integral unit. The scalar $u$ acts by a central element, so it commutes with $\omega(1, g)$, and it is enough to treat $\omega(1, u)^{-1} L$, which scales translations by $a$. For a unit $a$, the translations by the lattice fix the vacuum, so they also fix its image under $L$, and $L$ sends the vacuum to a multiple $c$ of itself. The vector $\omega(1, g)\mathrm{vac}$ is a finite sum of Heisenberg translates of the vacuum over the cosets of $\Lambda \cap g^{-1}\Lambda$ in the lattice $\Lambda$, with a factor that involves $\Delta(g)$. The map $L$ applies $\sigma$ to that factor, and multiplication by $a$ permutes the cosets. This gives the law for the vacuum. Both sides of the law turn the translation by $x$ into the translation by $a g x$, and the translates of the vacuum span the finite part. $\square$

**Theorem (Vacuum and Schrödinger data).** Let $L$ scale translations by $b$, and let $R$ be a set of finite places that is disjoint from its conjugate. There are a number $c$ and a unitary adele $u$ such that $L(\mathrm{vac}) = c\, \omega(1, u)\mathrm{vac}$ and $L(\Psi \otimes \mathrm{vac}) = c\, \omega(1, u)((\sigma \circ \Psi) \otimes \mathrm{vac})$ for every Schwartz-Bruhat function $\Psi$ above $R$.

Lean: `New.Space.ScalesTranslations.exists_map_schrodingerOp` (Lib/Weil/DualPair/GaloisLaw.lean).

**Remark (Formalization).** Scaling of translations is a hypothesis structure. The library does not construct a map $L$ in this file. The maps that the argument uses are built from Taylor series of theta functions in the proof of Theorem A, in the structure of jet conjugations (New/UpperBound/Kernels/JetConjugatesAndBounds.lean, field at line 85, proof at line 204). The proof of Theorem C takes the hypothesis as an argument at New/OneLift/HeckeValues/CharacterLift.lean line 616. The number $c$ in the second theorem is not shown to be nonzero here. The file cites Shimura 1976 for the classical law and J. Trias, arXiv 2601.16141, for the rationality of the Weil representation. The second source is a preprint, and it has not been refereed. The file also opens with `unseal finitePart` at line 48 with no `in`, so the definition of the finite part is unsealed for the whole rest of the file and not only for one proof.

### A local Gauss sum

Let $p$ be a prime and $\chi$ a primitive character modulo $p$. The classical Gauss sum $g(\chi) = \sum_{x \bmod p} \chi(x) e^{2\pi i x/p}$ has $|g(\chi)|^2 = p$. The statement here is the local form of this fact for a finite product of local fields, with the measure normalized so that the integers have volume $1$.

**Proposition (Local Gauss sum).** Let $F$ be a finite product of non-archimedean local fields, with integers $\mathcal{O}$ of volume $1$, a uniformizer $\varpi$ and residue ring $R = \mathcal{O}/\varpi$. Let $\chi$ be a tame character, so that $\chi^{-1}$ on the units of $\mathcal{O}$ is the pullback of a primitive character of $R$, and let $\psi$ be a continuous additive character with conductor $\mathcal{O}$. Let $\chi^{\flat}$ be $\chi^{-1}$ on the units of $\mathcal{O}$ and $0$ elsewhere. There is $\gamma \in \mathbb{C}$ with $|\gamma|^2 = 1/|R|$ such that for every $t \in F$,
$$\int_{\mathcal{O}} \chi^{\flat}(x)\psi(t x)\, dx = \begin{cases} \gamma\, \chi(\varpi t) & \text{if } \varpi t \text{ is a unit of } \mathcal{O}, \\ 0 & \text{otherwise}. \end{cases}$$

Lean: `New.Exchange.exists_local_gauss_sum` (Lib/Weil/TameGaussSum.lean).

*Proof sketch.* The integrand is invariant under $x \mapsto x + \varpi y$ when $t \in \varpi^{-1}\mathcal{O}$, and the integral splits into $|R|$ cosets of volume $1/|R|$ each. For $t = \varpi^{-1}u$ with $u$ a unit, the integral is $|R|^{-1}$ times a Gauss sum $G$ of a primitive character of $R$, multiplied by $\chi(u)$. Then $|\gamma|^2 = |R|^{-2}|G|^2 = |R|^{-2}|R| = 1/|R|$. If $\varpi t$ is not integral, the character $x \mapsto \psi(tx)$ is nontrivial on $\varpi\mathcal{O}$, and the integral over each coset vanishes. If $\varpi t$ is integral but not a unit, the sum of the primitive character over a coset of a proper ideal vanishes. $\square$

With the counting measure on $R$ instead, $|\gamma|^2 = 1/|R|$ becomes the classical $|G|^2 = |R|$.

**Remark (Formalization).** The value of $\gamma$ is not computed. Only its modulus is stated. The function $\chi^{\flat}$ is defined by a division in which $1/0 = 0$, so it is $0$ off the units. That convention gives the case distinction on the right side.
