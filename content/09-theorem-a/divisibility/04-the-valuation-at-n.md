---
title: The valuation at N
lean:
  - New/UpperBound/Divisibility/ValuationAtLevel.lean
decls:
  - New.Data.norm_detCharAt_diagN_le
  - New.Data.exists_mem_inducedPlace_one_le_norm
  - New.Data.projOn_translateDatum_mem_standardData
  - New.Data.schrodingerOpAt_directDatum_mem_raises
  - New.Data.liftCharAtN
  - New.Data.lift_schrodingerOpAt_comp
  - New.Data.schrodingerOpAtN
  - New.Data.liftAtN
  - New.Data.liftAtN_apply
  - New.Data.upCommutationFactor
  - New.Data.liftLaw_liftAtN
  - New.Data.gluedFactor
  - New.Data.norm_gluedFactor_le
  - New.Data.liftInPairs_gluedDoubleLiftDatum
  - New.Data.doubleLiftChain_gluedDoubleLiftDatum_eq_smul_chain
  - New.Data.omega_schrodingerOpAtN_directDatum
  - New.Data.schrodingerOpAtN_directDatum_mem_raises
  - New.Data.gaugeLe_compositeLift_at_N
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The valuation at N

This section proves the bound for the composite lift at $p = N$: on ramified forms of $\mathcal A'$ the composite lift has $N$-adic gauge at most $N^{2mfb}$. The plan has three steps. First, the lifts read in the bases of the lattices $L_j$ obey the two lift laws of [lift laws modulo N](/chapter/upper-bound-objects/#lift-laws-modulo-n). So the theorem that all lifts become direct applies, and the glued chain equals a scalar $c$ times the chain of direct lifts after $\mathrm{Up}^{m/2}$. Second, $|\iota_N c| \le N^{mfb}$. Third, each direct lift raises gauges from $\delta_j$ to $\delta_{j+1}$ by at most $N^{fb}$. The bound for chains and the restriction to $Y_m$ then give $N^{mfb}\cdot N^{mfb}$.

### Characters at the diagonal points

The theta lift from $X_j$ to $X_{j+1}$ carries the character $\chi^{(i)} = \mathrm{chainChar}(\vartheta, i)$ of lift $i$, base changed to $E$. For a size $r$, the character $\chi_r(g) = \chi^{(i)}(\det g)\,|\det g|^{-r/2}$ of $\mathrm{GL}_n(E_{\Sigma_N})$ is the factor by which the Weil action moves through the datum.

**Definition.** $\chi^{(i)}_r(g) = \chi^{(i)}(\det g)\,|\det g|^{-r/2}$ on $\mathrm{GL}_n(E_{\Sigma_N})$.

Lean: `New.Data.liftCharAtN` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

**Lemma (Characters at diagonal matrices).** Let $i \le 2m$, $r \ge 0$, and let $g = \mathrm{diag}_S(N)$ of size $n_j + 1$. Then
$$|\iota_N\,\chi^{(i)}_r(g)| \le \prod_{\tau\in\Phi} \begin{cases} N^{2b} & \text{if } \bar w_\tau \in S,\\ 1 & \text{otherwise.}\end{cases}$$

Lean: `New.Data.norm_detCharAt_diagN_le` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* At a matrix $\mathrm{diag}_S(N)$ the value $|\iota_N\chi^{(i)}_r|$ decreases as $r$ grows (`New.IsSplitLevel.norm_detCharAt_diagN_anti`; the local determinant has norm $N^{-1}$ or $1$, and the square root of its inverse has $N$-adic size at least $1$ and occurs with the exponent $-r$). So it suffices to take $r = 0$. For $r = 0$, the character has weight $\mathrm{liftWeight}(i)$, so $|\iota_N\chi^{(i)}(\det g)| = \prod_\tau \|(\det g)_\tau\|^{\mathrm{liftWeight}(i,\tau)}$, where $(\det g)_\tau$ is the determinant read through $\iota_N\circ\tau$. As $g$ is unitary, $(\det g)_\tau$ is the inverse of the determinant of the image of $g$, which is $N$ or $1$ by the lemma on the image of a diagonal point (Section 2). So the factor at $\tau$ is $N^{\mathrm{liftWeight}(i,\tau)} \le N^{2b}$ if $\bar w_\tau \in S$ and $1$ otherwise. The bound $\mathrm{liftWeight}(i,\tau) \le 2b$ for $i \le 2m$ is in [the data and their sizes](/chapter/data-and-sizes/). $\square$

**Lemma (The lift moves through the datum).** Let $f$ be a function of matrices modulo $N$, and let $\Psi_f$ be $f$ on integral matrices and $0$ elsewhere. For $g \in \mathrm{GL}_{X_j}(E_{\Sigma_N})$, $k \in \mathrm{GL}_{X_{j+1}}(E_{\Sigma_N})$, a datum $v$ and a form $\varphi$,
$$\theta_{T \mapsto \Psi_f(k^{-1}Tg)}(\varphi) = \frac{\chi_{n_{j+1}}(g)}{\chi_{n_j}(k)}\; k\cdot\theta_{\Psi_f}\big(g^{-1}\cdot\varphi\big),$$
where $\theta_\Psi$ is the lift by the datum $\Psi$ put on $v$ at $\Sigma_N$, $\chi_r = \chi^{(j+1)}_r$, and $g$, $k$ act by right translation through $\epsilon$.

Lean: `New.Data.lift_schrodingerOpAt_comp` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* The Weil action of $(\epsilon(g), \epsilon(k))$ on a Schrödinger datum changes the function $T \mapsto \Psi(T)$ to $T \mapsto \Psi(k^{-1}Tg)$ and multiplies it by the character ratio ([the Weil representation](/chapter/weil-representation/)). The lift is equivariant: $\theta_{\omega(g,k)v}(\varphi) = k\cdot\theta_v(g^{-1}\varphi)$ ([theta kernels and gauges](/chapter/theta-kernels-gauges/)). Combine the two. $\square$

### The lifts in the bases of $L_j$

**Definition (Lifts at $N$).**

1. $\mathrm{S}^N_j(\Psi) = \omega(\delta_j, \delta_{j+1})\circ\mathrm{S}(\Psi)$, where $\mathrm{S}(\Psi)$ puts the function $\Psi$ on a datum at $\Sigma_N$.
2. $L^{(j)}_v(\Psi)(\varphi) = \theta_{\mathrm{S}^N_j(\Psi)v}(\varphi)$, linear in $\Psi$.

Lean: `New.Data.schrodingerOpAtN`, `New.Data.liftAtN` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

**Lemma.** $L^{(j)}_v(\Psi)(\varphi) = \delta_{j+1}\cdot\theta_{\mathrm{S}(\Psi)v}(\delta_j^{-1}\cdot\varphi)$.

Lean: `New.Data.liftAtN_apply` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Equivariance of the lift. $\square$

So $L^{(j)}$ is the lift with $\varphi$ and its image read in the bases of $L_j$ and $L_{j+1}$. This is the form in which the representations $\rho_j$ of Section 2 act.

**Definition.** $\gamma_j = \chi_{n_{j+1}}(\mathrm{diag}_{\Sigma_N}(N)\text{ on } X_j)\,/\,\chi_{n_j}(\mathrm{diag}_{\Sigma_N}(N)\text{ on } X_{j+1})$, with $\chi_r = \chi^{(j+1)}_r$.

Lean: `New.Data.upCommutationFactor` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

**Theorem (The lift laws hold).** For every $j$ and every datum $v$, the lift $\Psi \mapsto L^{(j)}_v(\Psi)$ from $\rho_j$ to $\rho_{j+1}$ obeys the lift law with factor $\gamma_j$:

1. for integral invertible $a$, $b$ at $\Sigma_N$ and every function $f$ of matrices modulo $N$, $\rho_{j+1}(b)\,L^{(j)}_v(\Psi_{f(\bar b\,\cdot\,\bar a)})(\rho_j(a)\varphi) = L^{(j)}_v(\Psi_f)(\varphi)$;
2. $\rho_{j+1}(D)\,L^{(j)}_v(\mathrm{lastRow})(\varphi) = \gamma_j\,L^{(j)}_v(\mathrm{direct})(\rho_j(D)\varphi)$, with $D = \mathrm{diag}(1,\dots,1,N)^{-1}$.

Lean: `New.Data.liftLaw_liftAtN` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Part 1. By the lemma, $L^{(j)}_v(\Psi) = \delta_{j+1}\circ\theta_{\mathrm{S}(\Psi)v}\circ\delta_j^{-1}$, and $\rho_j(a)$ is right translation by $\delta_j\epsilon(a)\delta_j^{-1}$. So the left side is $\delta_{j+1}\epsilon(b)\cdot\theta_{\Psi'}(\epsilon(a)\cdot\delta_j^{-1}\varphi)$ with $\Psi'(T) = \Psi_f(bTa)$. As $a$, $b$ are integral, $\Psi_f(bTa) = \Psi_{f(\bar b\,\cdot\,\bar a)}(T)$. Apply the lemma on moving through the datum with $g = a$, $k = b^{-1}$. It gives $\theta_{\Psi'}(\psi) = (\chi(a)/\chi(b^{-1}))\,\epsilon(b)^{-1}\cdot\theta_{\Psi_f}(\epsilon(a)^{-1}\psi)$. The characters $\chi^{(j+1)}$ are unramified at the places above $N$, because $N$ is prime to the conductor of the twist ([the objects of the upper bound](/chapter/upper-bound-objects/)). An unramified character of the determinant is $1$ on integral invertible matrices, and $|\det a| = 1$. So the factor is $1$, and the translations cancel. Part 2. The indicator of last row $e_\ast^T$ satisfies $\mathrm{lastRow}(T) = \mathrm{direct}(D'TD'')$ for the diagonal matrices $D'$, $D''$ that conjugate the last row into the last column ([lift laws modulo N](/chapter/upper-bound-objects/#lift-laws-modulo-n)). Apply the lemma on moving through the datum with these diagonal matrices. The factor is the ratio of the characters at $\mathrm{diag}_{\Sigma_N}(N)$, which is $\gamma_j$. $\square$

### The glued pairs

The glued datum of the pair $X_{2i}\to X_{2i+1}\to X_{2i+2}$ is the projection of the data on the vacuum at the places above $N$, glued as in [the objects of the upper bound](/chapter/upper-bound-objects/). Its expansion is a sum over vectors $y$ modulo $N$ at $\Sigma_N$ of a datum $\mathrm{lastCol}_y$ on the first lift and a datum $\mathrm{char}_y$ on the second. Here $\mathrm{lastCol}_y$ is the indicator of integral matrices with last column $y$ modulo $N$, and $\mathrm{char}_y$ is $\psi_N$ of the last row paired with $y$.

**Definition.** $d_i = \chi^{(2i+2)}_{n_{2i+1}}(\mathrm{diag}_{\Sigma_N\setminus\Pi_N}(N) \text{ on } X_{2i+2})\cdot\chi^{(2i+1)}_{n_{2i+1}}(\mathrm{diag}_{\Pi_N}(N) \text{ on } X_{2i})$.

Lean: `New.Data.gluedFactor` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

**Lemma.** For $i \le \varrho$, $|\iota_N d_i| \le N^{2fb}$.

Lean: `New.Data.norm_gluedFactor_le` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Apply the lemma on characters at diagonal matrices to both factors; $2i+2 \le 2m$. The sets $\Sigma_N\setminus\Pi_N$ and $\Pi_N$ are disjoint with union $\Sigma_N$. So for each $\tau$ exactly one of the two products has the factor $N^{2b}$, and the product is $N^{2bf}$. $\square$

**Proposition (A glued pair in the bases of $L_j$).** For data $v_j$ and every $i$, the double lift by the glued datum of the projections $P_{\Pi_N}v_{2i}$, $P_{\Pi_N}v_{2i+1}$ is
$$d_i\;\rho_{2i+2}(D)\circ\sum_y L^{(2i+1)}_{v_{2i+1}}(\mathrm{char}_y)\circ L^{(2i)}_{v_{2i}}(\mathrm{lastCol}_y).$$

Lean: `New.Data.liftInPairs_gluedDoubleLiftDatum` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Expand the glued datum as a sum over $y$ ([lift laws modulo N](/chapter/upper-bound-objects/#lift-laws-modulo-n), the glued datum as a sum). In each term, the data of the two lifts contain the matrices $\mathrm{diag}_{\Pi_N}(N)$ on the right of the first and $\mathrm{diag}_{\Sigma_N\setminus\Pi_N}(N)$ on the left of the second. Move each out with the lemma on moving through the datum, at the cost of one character value. The first lift then ends with right translation by $\delta_{2i+1}^{-1}$, and the second starts with $\delta_{2i+1}$, so they cancel. The diagonal matrix of all of $\Sigma_N$ on $X_{2i+2}$ is $\mathrm{diag}_{\Sigma_N\setminus\Pi_N}(N)$ times that of $\delta_{2i+2}$, which gives $\rho_{2i+2}(D)$. $\square$

**Theorem (All lifts become direct at $N$).** There is $c \in \mathbb C$ with $|\iota_N c| \le N^{mfb}$ such that for all data $v_j$ and every ramified source form $\varphi$,
$$G_\varrho\circ\dots\circ G_0(\varphi) = c\cdot L^{(m-1)}_{v_{m-1}}(\mathrm{direct})\circ\dots\circ L^{(0)}_{v_0}(\mathrm{direct})\,(\mathrm{Up}^{\varrho+1}\varphi),$$
where $G_i$ is the double lift by the glued datum of the projections $P_{\Pi_N}v_{2i}$, $P_{\Pi_N}v_{2i+1}$.

Lean: `New.Data.doubleLiftChain_gluedDoubleLiftDatum_eq_smul_chain` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Take $c = \prod_{i\le\varrho} d_i\cdot\#\mathrm{Prim}(X_{2i+1})\cdot\prod_{l<2i+2}\gamma_l$, where $\#\mathrm{Prim}$ is the number of primitive vectors modulo $N$. By the proposition, each $G_i$ is the glued lift of [lift laws modulo N](/chapter/upper-bound-objects/#lift-laws-modulo-n) times $d_i$. By the theorem on lift laws, each $L^{(j)}$ obeys the lift law with factor $\gamma_j$. A ramified source form is a ramified vector of $\rho_0$ (Section 2). So the theorem that all lifts become direct gives the identity with this $c$.

For the bound: $|\iota_N d_i| \le N^{2fb}$. A natural number has $|\iota_N(\cdot)| \le 1$. Each $\gamma_l$ has $|\iota_N\gamma_l| \le 1$, by the same monotonicity in the size $r$, since $n_l \le n_{l+1}$. So $|\iota_N c| \le N^{2fb(\varrho+1)} = N^{mfb}$, as $m = 2(\varrho+1)$. $\square$

### Direct lifts lose little

**Lemma (A good integer of $K$).** There is $\delta \in \mathcal O_K$ with $|\iota_N(\bar\delta\,d)| \ge 1$ that lies in every induced prime $w_\sigma$, $\sigma \in \Phi$.

Lean: `New.Data.exists_mem_inducedPlace_one_le_norm` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Let $\mathfrak p$ be the prime of $K$ below the induced primes. Its residue field has $N$ elements, so the generator $\beta$ of $\mathcal O_K$ is congruent to an integer $c$ modulo $\mathfrak p$. Put $\delta = \beta - c$. Then $\delta \in \mathfrak p$, which lies in every $w_\sigma$. The conjugate $\bar\delta$ reduces to $\bar\beta - \beta$ modulo $\mathfrak p$, whose square is $-d$. Since $N \nmid d$, neither $\bar\delta$ nor $d$ lies in $\mathfrak p$. So $|\iota_N(\bar\delta d)| = 1$. $\square$

**Lemma.** For every translation tuple $x$, every $j$ and every $\delta \in \mathcal O_K$, the projection of the translated vacuum $v_{x,j}$ on the vacuum at the places above $N$ is a standard datum for $\delta$ ([the integral vacuum](/chapter/integral-vacuum/)).

Lean: `New.Data.projOn_translateDatum_mem_standardData` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* The projection of a Heisenberg translate of the vacuum is the translate itself if the translation is integral at all places above $N$, and $0$ otherwise. An integral translation times $\delta$ is integral. $\square$

**Theorem (Direct lifts lose little).** For $j < m$ and every $x$, the direct datum on $v_{x,j}$ at $\Sigma_N$ raises gauges from $1$ to $1$ by at most $N^{fb}$. The datum $\mathrm{S}^N_j(\mathrm{direct})v_{x,j}$ raises gauges from $\delta_j$ to $\delta_{j+1}$ by at most $N^{fb}$.

Lean: `New.Data.schrodingerOpAt_directDatum_mem_raises` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

Lean: `New.Data.schrodingerOpAtN_directDatum_mem_raises` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Let $\Theta$ be the first datum. It is the datum of a function modulo a modulus $\mathfrak m$ with places $\Sigma_N$, namely the test of the last column. Let $c = \mathrm N(N)^{n_{j+1}n_j} = N^{2f n_{j+1}n_j}$. By Fourier expansion modulo $\mathfrak m$, $c\,\Theta$ is an integral combination of Heisenberg translates of the projected vacuum by points $z$ with $\delta z$ integral above $N$, for $\delta$ from the lemma on a good integer ([the integral vacuum](/chapter/integral-vacuum/)). By the last lemma, each term is standard for $\delta$. So $c\,\Theta$ is standard for $\delta$. By the theorem on standard data ([kernels that raise gauges](/chapter/theta-kernels-gauges/)), $c\,\Theta \in \mathrm{raises}(1, 1, (|\iota_N\bar\pi_M|/|\iota_N(\bar\delta d)|)^{\cdot})$, and the base of the power is at most $1$. Hence $c\,\Theta\in\mathrm{raises}(1,1,1)$, and $\Theta = c^{-1}(c\,\Theta) \in \mathrm{raises}(1, 1, N^{2fn_{j+1}n_j})$. Since $n_j \le n_{j+1} \le n_m$ and $2n_m^2 \le b$ ([the data and their sizes](/chapter/data-and-sizes/)), the exponent is at most $fb$. The second claim follows from the first by the lemma on translates: $\omega(\delta_j, \delta_{j+1})$ moves the base points from $(1, 1)$ to $(\delta_j, \delta_{j+1})$. $\square$

**Lemma.** For $a \in K_j$, $b \in K_{j+1}$ and every datum $v$, $\omega(a, b)\,\mathrm{S}^N_j(\mathrm{direct})v = \mathrm{S}^N_j(\mathrm{direct})\,\omega(a,b)v$.

Lean: `New.Data.omega_schrodingerOpAtN_directDatum` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Move $\delta_j$, $\delta_{j+1}$ into the function; the same factor appears on both sides. The integral pair $(a, b)$ passes through the Schrödinger operator and acts on the function by $S \mapsto b'^{-1}Sa'$, where $a'$, $b'$ are the components of $\delta^{-1}a\delta$, $\delta^{-1}b\delta$ at $\Sigma_N$. These are mirabolic (Section 2), and the direct datum is invariant under mirabolic matrices on both sides. $\square$

### The bound at $N$

**Theorem (The prime $N$, valuation).** Let $\vartheta$ be a twist and $\Psi$ a chain datum for $\vartheta$. Let $\varphi$ be a ramified source form in $\mathcal A'$. Then $\mathrm{GaugeLe}(1, N^{2mfb}, B_{\vartheta,\Psi}\varphi)$, for the $N$-adic gauge.

Lean: `New.Data.gaugeLe_compositeLift_at_N` (New/UpperBound/Divisibility/ValuationAtLevel.lean).

*Proof.* Put $\psi = \mathrm{Up}^{\varrho+1}\varphi$. As $\varphi \in \mathcal A'$, $\psi$ is a source form with $\mathrm{GaugeLe}(\delta_0, 1, \psi)$. Let $c$ be the scalar of the theorem that all lifts become direct.

*Step 1: the composite lift.* For $x \in \mathrm{supp}\,\Psi$ the tuple $x$ is admissible, so $P_{\Pi_N}v_{x,j} = v_{x,j}$ ([expanding the gluing](/decl/New.Data.vacuumProjFinPart_translateDatum/)). Apply the theorem with $v_j = v_{x,j}$: the chain of the glued vacuum of $x$ sends $\varphi$ to $c$ times the chain of the direct data $\mathrm{S}^N_j(\mathrm{direct})v_{x,j}$ at $\psi$. Sum over $x$ with the weights $\Psi(x)$. So $B_{\vartheta,\Psi}\varphi = \mathrm{res}\,(c\cdot F)$, where $F$ is the chain combination of $\Psi$ with these direct data, applied to $\psi$.

*Step 2: the chain.* Apply [the gauge bound for chains](/decl/New.Data.IsWeakChainDatum.gaugeLe_chain/) to the weak chain datum underlying $\Psi$, with $t_j = \mathrm{S}^N_j(\mathrm{direct})$, base points $d_j = \delta_j$ and $r_j = fb$. Its hypotheses are: $N$ is prime to the level of $\vartheta$ (twists have level prime to $N$); condition 1 is the last lemma; condition 2 is the theorem on direct lifts; condition 3 is $\mathrm{GaugeLe}(\delta_0,1,\psi)$. So $\mathrm{GaugeLe}(\delta_m, N^{mfb}, F)$.

*Step 3: the restriction.* By the lemma on the image of a diagonal point, $\delta_m$ read at $\tau$ is $\mathrm{diag}(1,\dots,1,N)$ if $\bar w_\tau \in \Pi_N$ and $1$ otherwise. This is the hypothesis of [the restriction with a diagonal base point](/decl/New.Data.GaugeLe.restrictToY_of_diag/). The gauge of $cF$ at $g\delta_m$ is $|\iota_N c|$ times that of $F$, at most $N^{mfb}N^{mfb}$. So $\mathrm{GaugeLe}(1, N^{2mfb}, \mathrm{res}(cF))$. $\square$

**Remark (Formalization).** The theorem uses that $\varphi$ is ramified only through the lift laws. The module $\mathcal A'$ asks that $\mathrm{Up}^{\varrho+1}\varphi$ be a source form, which the gauge bound for chains needs. The scalar $c$ is obtained by an existential; its value is the product in the proof. Nothing asks $c \ne 0$. If $c = 0$, the composite lift vanishes on these forms and the bound is trivial. The characters $\chi_r$ take values in the units $\mathbb C^\times$, so the ratios $\gamma_j$ are defined without junk values.
