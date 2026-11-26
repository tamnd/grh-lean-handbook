---
title: Chains of lifts and free levels
lean:
  - New/UpperBound/Objects/LiftChains.lean
decls:
  - New.chain
  - New.chain_equivariant
  - New.doubleLiftChain
  - New.exists_linearMap_chain_eq_apply_pure
  - New.IsJointlyInvariant
  - New.IsJointlyInvariant.sum_chain_mem_nsmul
  - New.Data.chosenEquiv
  - New.Data.chosenGroupOrder
  - New.Data.principalLevel_le_chosenLevel
  - New.Data.card_classAut_dvd_chosenGroupOrder
  - New.Data.log_chosenGroupOrder_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Chains of lifts and free levels

The composite lift of Section 7 is a chain of $m$ theta lifts. The valuation argument of [the chain valuation](/chapter/chain-valuation/) needs two facts about such chains. The first is equivariance. The second is integrality: a combination of chains that is invariant under the levels is a plain sum over double cosets, with no denominators. The second fact needs free levels, that is, levels whose stabilisers in the rational group are trivial. This section states both facts for a general tower, and then proves that the levels at the chosen places are free.

### A model case: one lift

Take one lift, $m = 1$. A theta kernel $k_0$ with datum $\Phi_0$ sends a form $\varphi$ on $G_0 = \mathrm{U}(X_0)(\mathbb{A}_f)$ to the form on $G_1$ whose value at $g'$ is a sum over the class set $\mathrm{U}(X_0)(\mathbb{Q}) \backslash G_0 / K_0$. The class of $g$ enters with the weight $1/|\Gamma_g|$, where $\Gamma_g = \mathrm{U}(X_0)(\mathbb{Q}) \cap g K_0 g^{-1}$ is the stabiliser of $gK_0$. If every $\Gamma_g$ is trivial, every weight is $1$. Then the lift is a sum of $h$ terms, one for each class, with $h$ the class number. If each term lies in a set $A$, the sum lies in the $h$-fold sum set $h \cdot A$. For a chain of $m$ lifts the same holds with one class for each stage.

### Chains of theta lifts

Fix a tower of index sets $n_j$, of levels $K_j \subseteq G_j = \mathrm{U}(n_j)(\mathbb{A}_f)$, and of theta kernels $k_j$ from stage $j$ to stage $j + 1$. The kernel $k_j$ has a space of data $S_j$, an action $\omega$ of $G_j \times G_{j+1}$ on $S_j$, a lift $(k_j).\mathrm{lift}$ and a jet map. These are the kernels of [theta kernels, theta lifts and the seesaw](/chapter/theta-lifts-seesaw/). The forms of stage $j$ are algebraic forms with values in the Weyl module of weight $(\kappa, e_j)$, as in [integral Weyl modules and branching](/chapter/weyl-modules/).

**Definition (Chain of lifts).** For data $\Phi_j \in S_j$, the chain $\mathrm{chain}(\Phi)_j$ is the composite of the first $j$ lifts, $(k_{j-1}).\mathrm{lift}(\Phi_{j-1}) \circ \dots \circ (k_0).\mathrm{lift}(\Phi_0)$. It is a linear map from forms of stage $0$ to forms of stage $j$.

Lean: `New.chain` (New/UpperBound/Objects/LiftChains.lean).

**Definition (Chain of double lifts).** For data $\Phi_i \in S_{2i} \otimes S_{2i+1}$, the chain of double lifts applies, for $i < p$, the pair of lifts from stage $2i$ to stage $2i + 2$ with the tensor datum $\Phi_i$. It is a linear map from forms of stage $0$ to forms of stage $2p$.

Lean: `New.doubleLiftChain` (New/UpperBound/Objects/LiftChains.lean).

A pair of lifts is linear in each datum, so it extends to the tensor product $S_{2i} \otimes S_{2i+1}$. This is why the composite lift of Section 7 can use glued data that are not pure tensors.

**Lemma.** Let $\varphi$ be fixed by $K_0$, and let $a_j \in K_j$ for every $j$. Move each datum $\Phi_i$ by $\omega(a_i, a_{i+1})$. Then the chain with the moved data, applied to $\varphi$, is the right translate by $a_j$ of the chain with the old data, applied to $\varphi$.

Lean: `New.chain_equivariant` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* One lift is equivariant: lifting with the datum $\omega(a, a')\Phi$ gives the translate by $a'$ of the lift of the translate by $a$. This is the equivariance of a theta kernel. Apply it $j$ times. At the first step, $\varphi$ is fixed by $a_0$, so the translate by $a_0$ is $\varphi$ itself. At each later step, the translate by $a_i$ produced by the previous lift is the input that the next lift needs. $\square$

**Lemma.** Fix $\varphi$ and a point $g$ of stage $j$. There is a linear map $\beta$ from the tensor product $S_{j-1} \otimes \dots \otimes S_0$ to the Weyl module of stage $j$ such that, for all data $\Phi$, the value at $g$ of the chain with data $\Phi$ applied to $\varphi$ is $\beta(\Phi_{j-1} \otimes \dots \otimes \Phi_0)$.

Lean: `New.exists_linearMap_chain_eq_apply_pure` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* Each lift is linear in its datum, and evaluation at $g$ is linear. A map that is linear in each of $j$ arguments factors through the tensor product. $\square$

### Joint invariance

The composite lift is a combination $\sum_{x \in s} L_x(\mathrm{chain}(\Phi_x)_m \varphi)$, with linear maps $L_x$ from the Weyl module of stage $m$ to a space $M$. The levels act on such a combination only through the tensor $\sum_x L_x \otimes \Phi_{x,m-1} \otimes \dots \otimes \Phi_{x,0}$. Since the chain is linear in the pure tensor of the data, invariance of that tensor can be tested against all linear maps $\beta$.

**Definition (Jointly invariant).** The family $(L_x, \Phi_x)_{x \in s}$ is jointly invariant at stage $m$ if, for every tuple $a$ with $a_j \in K_j$ and $a_j = 1$ for $j \ge m$, and for every linear map $\beta$ from $S_{m-1} \otimes \dots \otimes S_0$ to the Weyl module of stage $m$,
$$\sum_{x \in s} L_x\big(\beta(\omega(a_{m-1}, a_m)\Phi_{x,m-1} \otimes \dots \otimes \omega(a_0, a_1)\Phi_{x,0})\big) = \sum_{x \in s} L_x\big(\beta(\Phi_{x,m-1} \otimes \dots \otimes \Phi_{x,0})\big).$$

Lean: `New.IsJointlyInvariant` (New/UpperBound/Objects/LiftChains.lean).

**Proposition.** Let the family be jointly invariant at stage $m$. Let the levels $K_j$, $j < m$, be free: every stabiliser $\mathrm{U}(n_j)(\mathbb{Q}) \cap g K_j g^{-1}$ is trivial. Let $\varphi$ be fixed by $K_0$. Let $P_j$ be a property of a point and a vector of stage $j$. Suppose $P_0(g, \varphi(g))$ holds for all $g$, and that the jet map of every moved datum $\omega(g, g')\Phi_{x,j}$ sends a vector with $P_j$ at $g$ to a vector with $P_{j+1}$ at $g'$. Let $A \subseteq M$ be a set such that, for every $\beta$, if all vectors $v_x = \beta(\Phi_{x,m-1} \otimes \dots \otimes \Phi_{x,0})$ have $P_m$ at $p$, then $\sum_x L_x(v_x) \in A$. Then
$$\sum_{x \in s} L_x\big((\mathrm{chain}(\Phi_x)_m \varphi)(p)\big) \in h \cdot A, \qquad h = \prod_{j < m} \big|\mathrm{U}(n_j)(\mathbb{Q}) \backslash G_j / K_j\big|.$$

Lean: `New.IsJointlyInvariant.sum_chain_mem_nsmul` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* First the value is unfolded. Each lift is a sum over the classes of its stage, weighted by the inverse orders of the stabilisers. The levels are free, so all weights are $1$. Unfolding the $m$ lifts gives a sum over tuples $c$ of classes, one for each $j < m$, of the kernel products. The kernel product at a tuple of points $q_0, \dots, q_m$ is the composite of the jet maps of the moved data $\omega(q_j, q_{j+1})\Phi_{x,j}$, applied to $\varphi(q_0)$. Joint invariance is used here: the choice of a representative of each class changes the moved data by elements of the levels, and joint invariance shows that the combination over $x$ does not change. So the value is the sum over $c$ of $\sum_x L_x(\text{kernel product at } c)$, with $q_m = p$.

Next each term is placed in $A$. Fix the tuple $c$ and its points $q$. The kernel product is linear in the pure tensor of the data, through one linear map $\beta$, the composite of the maps $\Phi \mapsto \mathrm{jet}(\omega(q_j, q_{j+1})\Phi)$. By induction on $j$, with the base case and the step case in the hypotheses, the kernel product for each $x$ has $P_m$ at $p$. So the hypothesis on $A$ applies, and the term lies in $A$. There are $h$ tuples, so the sum lies in $h \cdot A$. $\square$

The first step of the proof is a result of its own, `New.IsJointlyInvariant.sum_chain_eq_sum_kernelProduct`: the value is the sum over the $h$ tuples of classes of the kernel products. [The chain valuation](/chapter/chain-valuation/) uses this unfolding, and bounds each kernel product with the ultrametric gauge at $p$. The proposition itself, with a set $A$, is used for the last path in [grids, paths and turns](/chapter/grids-paths-turns/).

### Chosen places and free levels

The levels of Section 7 are small at the chosen places, the prime divisors of $\pi_M$. There are $f$ chosen places above each of $p_0$ and $p_1$, of norm $p_i$, and no two are conjugate.

**Definition (Chosen bijection).** For $i \in \{0, 1\}$, `chosenEquiv` is a bijection from the infinite places $\Phi$ of $E$ to the chosen places above $p_i$.

Lean: `New.Data.chosenEquiv` (New/UpperBound/Objects/LiftChains.lean).

**Definition (Chosen group order).** The chosen group order is the order of $\prod_{w} \mathrm{GL}_{rt}(\mathbb{F}_w)$, over the chosen places $w$ above $p_0$ and $p_1$.

Lean: `New.Data.chosenGroupOrder` (New/UpperBound/Objects/LiftChains.lean).

The chosen level on an index set $n$ is the group of integral points that reduce to $1$ at every chosen place. In rank at most $2 n_m$, every subgroup of the chosen level is free. This is [the freeness lemma](/decl/New.Data.classAut_eq_bot_of_le_chosenLevel/) of the outline; it rests on a unitary form of Minkowski's lemma, with $p_i > (8 n_m)^2$ from the size conditions of [data and sizes](/chapter/data-and-sizes/).

**Lemma.** If $\pi_M$ divides the integer $a$ of $E$, the principal congruence subgroup of level $a$ lies in the chosen level.

Lean: `New.Data.principalLevel_le_chosenLevel` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* An element of the principal level is integral and is $1$ modulo $a$. Every chosen place divides $\pi_M$, hence $a$, so the element reduces to $1$ there. $\square$

**Proposition.** Let $n$ have at most $2 n_m$ elements, let $K$ lie in the stabiliser of the standard lattice, and let $g$ be finite adelic. The order of the stabiliser $\mathrm{U}(n)(\mathbb{Q}) \cap g K g^{-1}$ divides the chosen group order.

Lean: `New.Data.card_classAut_dvd_chosenGroupOrder` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* Conjugate by $g^{-1}$ into the stabiliser of the standard lattice, and reduce at the chosen places. This gives a homomorphism from the stabiliser to $\prod_w \mathrm{GL}_n(\mathbb{F}_w)$. Its kernel lies in the stabiliser for the chosen level, which is trivial by the freeness lemma. So the homomorphism is injective. The size conditions give $2 n_m \le rt$, and $g \mapsto \mathrm{diag}(g, 1)$ embeds $\mathrm{GL}_n$ in $\mathrm{GL}_{rt}$. So the order of $\prod_w \mathrm{GL}_n(\mathbb{F}_w)$ divides the chosen group order, by Lagrange. $\square$

**Lemma.** The logarithm of the chosen group order is at most $x^{32}$.

Lean: `New.Data.log_chosenGroupOrder_le` (New/UpperBound/Objects/LiftChains.lean).

*Proof.* The residue field at a chosen place above $p_i$ has $p_i$ elements, and there are $f$ such places. A group $\mathrm{GL}_l(\mathbb{F}_q)$ has at most $q^{l^2}$ elements. So the chosen group order is at most $M^{(rt)^2 f}$, with $M = p_0 p_1$, and its logarithm is at most $(rt)^2 f \log M$. The size conditions bound this by $x^{32}$. $\square$

**Remark (Formalization).** The bijection `chosenEquiv` is taken by `Nonempty.some` from an existence proof, so no particular bijection is fixed. The class representatives in the proof of the proposition are taken by `Quotient.out`; joint invariance is exactly what makes the result independent of them. The chosen group order is a `Nat.card`; Lean records that it is nonzero, as it is the order of a finite group. The proposition on sums uses a general tower with a level hypothesis `IsLevel` on each $K_j$; it does not use the data $D$ at all.
