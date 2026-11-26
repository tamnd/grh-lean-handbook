---
title: The chapter and its place
lean:
  - New/Spanning/Multiplicities/HeckeEigensystems.lean
  - New/Spanning/Multiplicities/EqualMultiplicities.lean
  - New/Spanning/MainTerm/BadTypes.lean
decls:
  - New.Data.targetDim_eq_finrank_goodForms_spaceW
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The chapter and its place

This chapter is the second layer of the proof of Theorem B, the dimension layer of [the four layers](/chapter/theorem-b-plan/#the-four-layers-of-the-proof). It proves two results. The first says that the good forms on the indefinite space $Y_0$ and on each space $W_j$ have the same dimension $d_T$. The second says that the bad types of the finite group $\bar G$ carry only a small share of its regular representation. The first result moves the count of the target from $Y_0$, where no direct count is available, to the definite space $W_m$, where the forms are functions on a finite class set. The second result says that the projection $e_0$ onto the good forms removes little. [The last chapter of the volume](/chapter/proof-of-theorem-b/) uses the first result for the bound $d_T \leq \#\bar G \cdot \deg \cdot \mathrm{mass}_r$, and the second for the near isometry (NI).

### A model case

The model is a classical comparison of Eichler. Let $p$ be a prime, let $B$ be the quaternion algebra over $\mathbb{Q}$ that is ramified exactly at $p$ and $\infty$, and let $\mathcal{O}$ be a maximal order of $B$. The group $B^\times_\infty$ is compact modulo its centre. So an automorphic form on $B^\times$ of weight $2$ and level $\hat{\mathcal{O}}^\times$ is a function on the finite set of classes of left ideals of $\mathcal{O}$, and the space of such forms has dimension $h$, the number of classes. The Hecke operators act on this space by the Brandt matrices. The comparison says that, for every $n$ prime to $p$, the trace of the Brandt matrix of $n$ equals the trace of $T_n$ on the space $M_2(\Gamma_0(p))$ of modular forms of weight $2$. With $n = 1$ this gives $h = \dim S_2(\Gamma_0(p)) + 1$, where the $1$ is the Eisenstein series. The theorem of Jacquet and Langlands makes the comparison a statement about automorphic representations: a cuspidal representation of $\mathrm{GL}_2$ that is a discrete series at $p$ and at $\infty$ corresponds to a representation of $B^\times$ with the same Hecke eigenvalues away from $p$, and conversely.

The source uses the same idea for unitary groups. The spaces $Y_0$ and $W_1, \dots, W_m$ are hermitian spaces of rank $r$ over the CM field $E$. They have the same finite adelic group $G_f$, the same level, the same parameter at the infinite places, and differ only in their signs at the real places. The space $W_m$ is definite. The comparison of traces of [the chapter on the simple trace formula](/chapter/trace-formula/) plays the part of Eichler's trace formula. Two simplifications occur. The test function is cuspidal at one split place, so no Eisenstein term appears and the spectral side is the trace on cusp forms. The parameter has a large gap, so only forms of one discrete series type at each real place enter.

### The setting

The chapter works with the data $D$ of [the data and their sizes](/chapter/data-and-sizes/). The following objects are fixed.

1. The rank $r = \#\mathtt{RowIndex}$ of $Y_0$ and of every $W_j$, with $r \geq 2$. The field $E$ has $f$ infinite places, and $f$ is even.
2. The two level primes $p_0, p_1$, with $b^{10} \leq p_i \leq b^{11}$. Above $p_i$ the data choose a set of places of $E$, one from each pair of conjugate places. A *chosen place* is a pair $x = (i, w)$ with $w$ chosen above $p_i$. The residue field $\mathbb{F}_x$ at $x$ has $p_i$ elements.
3. The finite group $\bar G = \prod_x \mathrm{GL}_r(\mathbb{F}_x)$, the product over all chosen places. In Lean it is `New.Data.chosenGL`.
4. The *principal level* $J_M$: the elements of the maximal compact subgroup $K_0$ of $G_f$ whose reduction is $1$ at every chosen place. In Lean it is `New.Data.chosenLevel`. The integral lifts of the elements of $\bar G$ normalise $J_M$.
5. For a hermitian space $V$ of rank $r$ with signs $s$, the *forms of principal level* $\mathcal{A}_M(V)$: the forms on $V$ of the discrete series type $e_{l,s}$ of the doubled parameter $l = $ `paramW`, fixed by $J_M$. In Lean it is `New.Data.principalForms`. The group $\bar G$ acts on it through integral lifts, by `New.Data.principalRep`.
6. The central idempotent $e_0 = \sum_{c} e_c$ of $\mathbb{C}[\bar G]$, a sum over the good families $c$ of labels. The *good forms* $\mathcal{G}(V) = e_0\,\mathcal{A}_M(V)$. In Lean these are `New.Data.e₀` and `New.Data.goodForms`. The *target* is $\mathcal{G}(Y_0)$ and $d_T = \dim \mathcal{G}(Y_0)$, `New.Data.targetDim`.

The forms of principal level form a finite-dimensional space, by the finite dimension theorem of [automorphic forms](/chapter/automorphic-forms/); in Lean this is an instance in New/UpperBound/Objects/Rows.lean. The labels and the idempotents $e_c$ come from Green's characters of $\mathrm{GL}_r(\mathbb{F}_q)$ with squarefree labels, of [finite general linear groups](/chapter/finite-gln/#greens-characters-with-squarefree-labels). The section on equal traces recalls the definition of a good family.

The parameter $l$ is a family of integer vectors $l_v \in \mathbb{Z}^r$ over the infinite places $v$. It has *gap* $h$ for the signs $s$ if, at every $v$, the entries of $l_v$ are distinct, each $l_{v,i} + r - 1$ is even, and $|l_{v,i} - l_{v,j}| \geq 2h$ whenever $s_i \neq s_j$. The data give $l$ the gap $h = \Delta$ (`D.gap`) for the signs of $Y_0$ and of every $W_j$. These are instances in Lean, so they never appear as hypotheses at the points of use.

### The main result

**Theorem (Equal dimensions).** For each lift index $j$, $1 \leq j \leq m$,

$$d_T = \dim_{\mathbb{C}} \mathcal{G}(W_j).$$

Lean: `New.Data.targetDim_eq_finrank_goodForms_spaceW` (New/Spanning/Multiplicities/EqualMultiplicities.lean).

The proof is one line once the comparison of traces for Hecke operators on good forms is known: the identity has the same trace on $\mathcal{G}(Y_0)$ and on $\mathcal{G}(W_j)$, and the trace of the identity is the dimension. The work is in the comparison, and it is the subject of the next three sections.

### The plan of the proof

The proof has four steps.

1. *Hecke operators away from the level.* There is one algebra $\mathcal{H}$ of operators that acts on $\mathcal{A}_M(V)$ for all hermitian spaces $V$ of rank $r$ at once. An element of $\mathcal{H}$ is given by one element $a$ of the group algebra of $G^M$, the elements of $G_f$ that are $1$ at the chosen places. The algebra commutes with $\bar G$, so it acts on the good forms. This is [the section on Hecke operators off the level](/chapter/equal-multiplicities/#hecke-operators-away-from-the-level).
2. *Eigensystems.* The forms of principal level split into the parts of the joint eigensystems of the operators $T_{w,i}$ at split places $w$ away from the level. For each eigensystem $q$ and each finite set $F$ of others, one element of $\mathcal{H}$ is $1$ on the $q$-part and $0$ on the parts of $F$, on every space at once. This is [the section on eigensystems](/chapter/equal-multiplicities/#eigensystems-and-projectors).
3. *Equal traces.* The trace of $T \in \mathcal{H}$ on $\mathcal{G}(V)$ is the sum over good families $c$ of the traces of $T e_c$ on $\mathcal{A}_M(V)$. Each good family has a primitive label at some chosen place $x$. This makes the test function of $T e_c$ cuspidal at $x$, and the comparison of traces of [the trace formula chapter](/chapter/trace-formula/#the-comparison-of-traces) applies. Equal traces of all powers give equal characteristic polynomials. The projectors of step 2 give equal multiplicities of every eigensystem. This is [the section on equal traces](/chapter/equal-multiplicities/#equal-traces-and-equal-multiplicities).
4. *The Rallis operator.* The series of Rallis' inner product formula acts on $\mathcal{A}_M(V)$ as an element of $\mathcal{H}$. So it preserves the good forms and has the same determinant on $\mathcal{G}(V)$ and on $\mathcal{G}(V')$ whenever $l$ has gap $\Delta$ for the signs of $V$ and of $V'$. Theorem C uses this. This is [the section on the Rallis operator](/chapter/equal-multiplicities/#the-rallis-operator-as-a-hecke-operator).

The second result of the chapter is independent of the first. It is a count over finite fields: monic polynomials of degree $r$ over $\mathbb{F}_q$ that are not allowed, or not primitive, are few, and Green's degree formula bounds the share of each type from below. A union bound and Bernoulli's inequality then bound the share of the bad types. This is [the section on bad types](/chapter/equal-multiplicities/#bad-types-are-rare).

### What the chapter uses

The chapter uses the following results of earlier volumes, each stated where it is used.

- The comparison of traces for a test function cuspidal at a split place, from [the simple trace formula](/chapter/trace-formula/).
- Cuspidality of the test functions built from Green's idempotents with an irreducible label, from [test functions and cuspidality](/chapter/trace-formula/#test-functions-and-cuspidality).
- The Hecke operators $T_{w,i}$ at split places, their commutativity and normality, and the spectral theorem for them, from [Iwahori and Satake](/chapter/iwahori-satake/#split-places-and-the-transfer-of-hecke-polynomials).
- Green's characters with squarefree labels and the bounds for their degrees, from [finite general linear groups](/chapter/finite-gln/#greens-characters-with-squarefree-labels).
- The operator of Rallis' inner product formula on forms of principal level, from [the inner product formula](/chapter/rallis-inner-product/#the-inner-product-formula). Its Lean definition is in New/Determinant/Norms/AdjointThetaLift.lean, which belongs to Volume 11.

The chapter uses no result of a later chapter of this volume in its mathematics. The file New/Spanning/MainTerm/BadTypes.lean imports New/Spanning/RemainingTerms/Size.lean, which this volume places in [the chapter on the remaining terms](/chapter/remaining-terms/). The section on bad types comments on this import.
