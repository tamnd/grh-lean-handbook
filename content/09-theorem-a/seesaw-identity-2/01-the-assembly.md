---
title: The assembly of the seesaw
lean:
  - New/UpperBound/Seesaw/SeesawIdentity.lean
decls:
  - New.Data.seesaw_identity
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The assembly of the seesaw

This chapter completes the proof of the seesaw identity, the second input of [Theorem A and its plan](/chapter/theorem-a-plan/). [Part 1](/chapter/seesaw-identity-1/) unfolded the pairing of the lower chain with a form on $Y_{k+1}$, one lift at a time. It evaluated the result of each pair of lifts by the finite map $\mathrm{ev}_D$. This chapter shows that these evaluations are admissible combinations of glued translates of the vacuum, and it assembles them into a chain datum $\Psi$.

### The statement

Recall the identity from [the three inputs](/chapter/theorem-a-plan/). Let $D$ be the data, $t$ a linear form on the values of forms on $X_0$ and $g$ an archimedean point of $U(Y_0)$. Let $\mathcal P = \mathcal P_{g,t}$ be the Poincaré map of [the objects of the upper bound](/chapter/upper-bound-objects/).

**Theorem (Seesaw identity).** There is a unit $c \in \mathbb C^\times$ such that every twist $\vartheta$ has a chain datum $\Psi$ with

$$\iota_\vartheta(\mathcal P\varphi) = c \cdot B_{\vartheta,\Psi}(\varphi)$$

for all ramified source forms $\varphi$ on $X_0$.

Lean: `New.Data.seesaw_identity` (New/UpperBound/Seesaw/SeesawIdentity.lean).

Here $\iota_\vartheta$ is the lower chain of $m = 2\varrho + 2$ lifts with the twist $\vartheta$ ([rows and the lower chain](/chapter/upper-bound-objects/)). The map $B_{\vartheta,\Psi}$ is the composite lift: the chain of double lifts along $X_0 \to \cdots \to X_m$ with the glued tensor of $\Psi$ as data, followed by the restriction from $X_m$ to $Y_m$ ([columns and the composite lift](/chapter/upper-bound-objects/)). That $\Psi$ is a chain datum means four things. Its support consists of tuples of translations that vanish at the places prime to $Mq$ and are integral away from $q$ after multiplication by $\bar\varpi$, where $\varpi = $ `D.piM`. Its values are integral away from $q$. If $\vartheta.Q = \emptyset$, the absolute sum of its values under every automorphism of $\mathbb C$ is at most $M^{3fmn_m^2}$. Its glued tensor is jointly invariant. Here $q$ is the product of the norms of the places of $\vartheta.Q$, $M = p_0p_1$ is the principal level, $f$ is the number of infinite places of $E$ and $n_m$ is the rank of $X_m$.

The proof is in Section 6. It has five steps.

1. *Unfold.* The pairing of the lower chain with a form on $Y_m$ is a constant times a cut sum of periods $\Xi_m$ (Section 6, from the tools of part 1).
2. *Evaluate.* The top period $\Xi_m$ is a constant times the pairing with the restriction of a chain of double lifts whose data are the evaluated data of the pairs. So $\iota_\vartheta(\mathcal P\varphi)$ is $c_0$ times the composite lift of the tensor $\varphi_\xi$, the cut sum of the evaluated tensors (Section 6).
3. *Expand.* Each evaluated datum is an admissible combination of glued translates of the vacuum, with denominator $R^4$, where $R = M^{fn_m^2}$. This needs the neighbour lattices of Sections 2 and 3, the evaluation of Section 4 and the choice of the scaling in Section 5.
4. *Rescale.* The tensor $\varphi_\xi$ is then an admissible combination with denominator $R^{2m}$ and size $R^{2\varrho+2}$. Multiply it by $u = \mathrm{normUnit}(c_0 C/R^{2m})$ to clear the denominator.
5. *Support.* Replace each translation by one that vanishes away from $Mq$ and has the same datum ([the chain valuation](/chapter/chain-valuation/)).

The constant of the identity is $c = u^{-1}$. It is $c_0C/R^{2m}$ when $c_0C \neq 0$ and $1$ when $c_0C = 0$. In the second case both sides of the identity are $0$. Section 6 explains this in full.

### A model case: a neighbour of $\mathbb Z[i]$

The new tool of this chapter is the neighbour lattice. A neighbour of a lattice $L$ at a prime $N$ is a second unimodular lattice $L'$ with $L \cap L'$ of index $N$ in both. The model case shows the three facts that the chapter uses: $L'$ is the image of $L$ under a unitary element, the quotient $L'/(L \cap L')$ lives at one place, and it has a simple set of representatives.

Let $E = \mathbb Q(i)$, $L = \mathbb Z[i]$ with the form $\langle z, w\rangle = \bar z w$, and $N = 5 = \pi\bar\pi$ with $\pi = 2 + i$. Put

$$u = \frac{\pi}{\bar\pi} = \frac{(2+i)^2}{5} = \frac{3 + 4i}{5}.$$

Then $u\bar u = 1$, so multiplication by $u$ is a unitary map of $E$. Let $L' = uL$.

**Example (The neighbour of $\mathbb Z[i]$ at $5$).**

1. $L'$ is unimodular, and $L \cap L' = \pi L$.
2. $L'/(L \cap L')$ has order $5$, and the classes of $ku$ for $k = 0, \ldots, 4$ represent it.
3. Every $z \in L'$ differs from exactly one $ku$, $0 \le k \le 4$, by an element of $L$.

*Proof.* (1) $L'$ is the image of the self-dual lattice $L$ under a unitary map, so it is self-dual. An element $z \in L$ lies in $L'$ exactly when $z/u = z\bar\pi/\pi$ lies in $L$. Since $\pi$ and $\bar\pi$ are coprime primes of $\mathbb Z[i]$, this holds exactly when $\pi \mid z$. (2) The index of $\pi L$ in $L$ is $|\pi|^2 = 5$. Multiplication by $u$ carries $L$ onto $L'$ and $\bar\pi L$ onto $u\bar\pi L = \pi L$, so $L'/(L\cap L') \cong L/\bar\pi L$, which also has order $5$. The class of $1$ generates $L/\bar\pi L$, since $\bar\pi \nmid k$ for $0 < k < 5$. So $ku$, $k = 0, \ldots, 4$, represent $L'/\pi L$. (3) Two representatives $ku$ and $k'u$ differ by an element of $L$ exactly when $(k - k')u \in L \cap L' = \pi L$, that is, when $5 \mid k - k'$. With (2) this gives existence and uniqueness. $\square$

Locally the picture is this. At the place $w$ of $\pi$ the element $u$ is a uniformizer, so $L'_w = \pi L_w$ is smaller than $L_w$. At the place $\bar w$ it is the inverse of a uniformizer, so $L'_{\bar w} = \bar\pi^{-1}L_{\bar w}$ is larger. The quotient $L'/(L\cap L')$ lives at $\bar w$. The representatives can be taken as $y/\bar\pi$ at $\bar w$ for residues $y$ modulo $5$.

The neighbour lattice of Section 2 has the same shape. The unitary $\gamma$ scales one unit vector $\rho$ by $\pi$ at the places of $P$ and by $\bar\pi^{-1}$ at their conjugates. It fixes the orthogonal complement of $\rho$. The representatives modulo integral points are the matrices `neighbourTranslation`, which are supported at the conjugate places, with entries $\eta\bar y/N$ and $-\bar y/N$. Away from $N$ the rows are scaled by the factors $\kappa$ of Section 5, and this adds a second finite quotient.

### Why neighbours appear

In part 1 the evaluation $\mathrm{ev}_D$ of a pair takes the finite zero term along the splitting of $\mathrm{Hom}(V', V^-\oplus V'')$. By [the theorem on translates of the vacuum](/decl/New.Seesaw.exists_zeroTermFin_vacElem_eq_sum/), the zero term of the vacuum is a nonzero multiple of a sum of translates of the vacuum of the definite part, over representatives of the zero term lattice $L'_D$ modulo its integral points. So the evaluation is known once $L'_D$ is known. Section 4 proves that $L'_D$ is the neighbour lattice. The glued lattice of [standard lattices](/chapter/seesaw-identity-1/) joins the last basis vector of the definite part to the middle of the string with a pole $\pi^{-1}$. This is what turns the standard lattice into a neighbour at $N$.

### The plan of the chapter

Section 2 builds the neighbour lattice and its representatives. Section 3 computes the sum of the translates of the vacuum over them on the two edges, through the gluing. Section 4 identifies the zero term lattice of a pair with the neighbour lattice and proves that the evaluation is admissible. Section 5 applies this to the pairs of the tower and gives the good datum: the tensor of the evaluated data is an admissible combination of glued vacua. Section 6 does the assembly and proves the seesaw identity, with the constant. Section 7 has exercises and notes.
