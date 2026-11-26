---
title: Relations and cocycles
lean:
  - Lib/General/Algebra/FittingIdealsAndLengths.lean
decls:
  - New.relEval
  - New.obeying
  - New.relationsOn
  - New.cocycleRelations
  - New.mem_obeying_cocycleRelations
  - New.length_obeying_relationsOn_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Relations and cocycles

This section gives the language in which the source writes conditions on cocycles, and its first length bound. A condition on a function $c \colon \Gamma \to B^n$ is a finite linear relation $\sum_\gamma f(\gamma) c(\gamma) = 0$ with matrix coefficients. The cocycle identity is a family of such relations. So are the linear relations that a lattice of cocycles over $O$ satisfies. The main result says: the functions with values in an $O$-module $B$ that obey all relations of a lattice $Z$ of rank $r$ form a module of length at most $r$ times the length of $B$. This is the bound behind the upper bounds for Selmer groups in [the tied Selmer groups](/chapter/tied-selmer-groups/).

### Relations

Fix a commutative ring $O$, a set $\Gamma$, a finite set $n$ of indices, and an $O$-module $B$. Write $M_n(O)$ for the ring of $n \times n$ matrices over $O$. It acts on $B^n$ by the usual product of a matrix with a column.

**Definition (Evaluation of relations).** A *relation* is a finitely supported function $f \colon \Gamma \to M_n(O)$. For a function $c \colon \Gamma \to B^n$ put
$$\operatorname{ev}_B(f)(c) = \sum_{\gamma \in \Gamma} f(\gamma)\, c(\gamma) \in B^n .$$
The map $c \mapsto \operatorname{ev}_B(f)(c)$ is $O$-linear, and the map $f \mapsto \operatorname{ev}_B(f)$ is linear over $M_n(O)$.

Lean: `New.relEval` (Lib/General/Algebra/FittingIdealsAndLengths.lean). The formula is `New.relEval_apply`.

**Definition (Functions that obey relations).** For a set $R$ of relations, $\operatorname{Obey}(R, B)$ is the $O$-submodule of functions $c \colon \Gamma \to B^n$ with $\operatorname{ev}_B(f)(c) = 0$ for all $f \in R$.

Lean: `New.obeying` (Lib/General/Algebra/FittingIdealsAndLengths.lean). Membership is `New.mem_obeying`.

**Definition (The relations of a module).** For an $O$-submodule $Z$ of the functions $\Gamma \to O^n$, $\operatorname{Rel}(Z)$ is the set of relations $f$ with $\operatorname{ev}_O(f)(z) = 0$ for all $z \in Z$.

Lean: `New.relationsOn` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

So $\operatorname{Obey}(\operatorname{Rel}(Z), B)$ is the module of $B$-valued functions that satisfy every linear relation with coefficients in $O$ that holds on $Z$. It contains the reductions of the elements of $Z$. If $z \in Z$ and $b \in B$, then $\gamma \mapsto z(\gamma) b$ obeys every relation of $Z$, because $\sum_\gamma f(\gamma) z(\gamma) b = 0$. For $B = O/a$, the source records that the reduction of each $z \in Z$ modulo $a$ obeys the relations of $Z$ (`New.mkQ_mem_obeying_relationsOn`). A second lemma, `New.comp_mem_obeying_iff`, says when the image of $c$ under a linear map $B \to B'$ obeys $R$.

### Cocycles

Let $\Gamma$ be a set with a multiplication, for example a group, and let $\rho \colon \Gamma \to M_n(O)$ be any function. A *cocycle* for $\rho$ with values in $B^n$ is a function $c \colon \Gamma \to B^n$ with $c(gh) = c(g) + \rho(g)\, c(h)$ for all $g$, $h$. When $\Gamma$ is a group and $\rho$ is a representation, these are the inhomogeneous $1$-cocycles of $\Gamma$ with values in $B^n$ (Serre, *Galois Cohomology*, Chapter I, Section 5.1). The cocycle identity is a family of relations.

**Definition (Cocycle relations).** For $g, h \in \Gamma$ let $f_{g,h}$ be the relation with value $1$ at $gh$, $-1$ at $g$ and $-\rho(g)$ at $h$, added where two of these points coincide:
$$f_{g,h} = \delta_{gh} \cdot 1 - \delta_g \cdot 1 - \delta_h \cdot \rho(g).$$
The set of cocycle relations of $\rho$ is $\{ f_{g,h} : g, h \in \Gamma \}$.

Lean: `New.cocycleRelations` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

**Lemma.** A function $c \colon \Gamma \to B^n$ obeys the cocycle relations of $\rho$ if and only if $c(gh) = c(g) + \rho(g)\, c(h)$ for all $g, h \in \Gamma$.

Lean: `New.mem_obeying_cocycleRelations` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

*Proof.* By definition, $\operatorname{ev}_B(f_{g,h})(c) = c(gh) - c(g) - \rho(g) c(h)$. $\square$

The lemma is used in four files: `New/Congruences/LocalLoss/Basic.lean`, `New/Congruences/FirstOrder/FittingBlock.lean`, `New/Congruences/FirstOrder/TraceRelations.lean` and `Lib/ClassField/GaloisCohomology/TameSelmerCocycles.lean`.

Now let $Z$ be a module of $O$-valued cocycles for $\rho$. Each cocycle relation is a relation of $Z$. So
$$\operatorname{Obey}(\operatorname{Rel}(Z), B) \subseteq \operatorname{Obey}(\text{cocycle relations of } \rho, B),$$
and the functions that obey the relations of $Z$ are cocycles with values in $B^n$. They are the cocycles that satisfy, in addition, every linear relation that the lattice $Z$ satisfies. In Ribet's method the lattice $Z$ is made from a family of representations, and the extra relations carry the information of the family. Volume 12 calls the result a module of Ribet cocycles; see [the Ribet elements](/chapter/ribet-elements/).

### The bound by rank and length

**Theorem.** Let $O$ be a discrete valuation ring, $n$ a nonempty finite set, $B$ an $O$-module, and $Z$ an $O$-submodule of the functions $\Gamma \to O^n$ that is finitely generated. Then
$$\operatorname{length}_O \operatorname{Obey}(\operatorname{Rel}(Z), B) \leq \operatorname{rank}_O(Z) \cdot \operatorname{length}_O(B).$$

Lean: `New.length_obeying_relationsOn_le` (Lib/General/Algebra/FittingIdealsAndLengths.lean).

The idea is that a function $c$ which obeys the relations of $Z$ is determined by a linear map out of the module of relations modulo the relations of $Z$. That module is a submodule of the dual of $Z$, so it is free of rank at most $\operatorname{rank} Z$.

*Proof.* Fix an index $i \in n$. Let $\mathcal{F}$ be the module of all relations. For $f \in \mathcal{F}$ let $\varphi(f) \in \operatorname{Hom}_O(Z, O)$ be the form $z \mapsto \operatorname{ev}_O(f)(z)_i$, the coordinate $i$ of $\sum_\gamma f(\gamma) z(\gamma)$.

Let $c$ obey the relations of $Z$, and let $\psi_c(f) = \operatorname{ev}_B(f)(c)_i \in B$. Then $\psi_c$ vanishes on $\ker \varphi$. Indeed, let $\varphi(f) = 0$, and let $E_{ii}$ be the matrix unit at $(i, i)$. The relation $E_{ii} f$ keeps row $i$ of each $f(\gamma)$ and sets the other rows to $0$. It is a relation of $Z$, because coordinate $i$ of $\sum_\gamma f(\gamma) z(\gamma)$ is $\varphi(f)(z) = 0$. So $\operatorname{ev}_B(E_{ii} f)(c) = 0$, and its coordinate $i$ is $\psi_c(f)$. So $\psi_c$ factors through $\mathcal{F} / \ker \varphi$.

The map $c \mapsto \psi_c$ is injective. The relation $\delta_g \cdot E_{ij}$, with the matrix unit $E_{ij}$ at the point $g$, gives $\psi_c(\delta_g E_{ij}) = c(g)_j$. So $\psi_c$ determines all coordinates of $c$.

Hence $\operatorname{Obey}(\operatorname{Rel}(Z), B)$ embeds in $\operatorname{Hom}_O(\mathcal{F}/\ker\varphi, B)$. The module $\mathcal{F}/\ker\varphi$ is isomorphic to the image of $\varphi$, a submodule of $\operatorname{Hom}_O(Z, O)$. Over a principal ideal domain the dual of a finitely generated module is free of rank $\operatorname{rank} Z$, and a submodule of a free module of finite rank is free of no larger rank. So $\mathcal{F}/\ker\varphi \cong O^s$ with $s \leq \operatorname{rank} Z$, and $\operatorname{Hom}_O(O^s, B) \cong B^s$ has length $s \cdot \operatorname{length}(B)$. $\square$

The hypothesis that $n$ is nonempty serves only to fix the index $i$. For empty $n$ the module of functions $\Gamma \to B^n$ is $0$, so the bound also holds. The rank in the source is `Module.finrank`, which for a finitely generated torsion free module over a discrete valuation ring is the rank of the free module.

**Example.** Let $\Gamma$ have one point and $n = 1$. A function is an element of $B$, and a relation is an element $f \in O$. Let $Z = \varpi^k O$. A relation of $Z$ has $f \varpi^k = 0$, so $f = 0$. So every $b \in B$ obeys the relations of $Z$, and the module has length $\operatorname{length}(B) = 1 \cdot \operatorname{length}(B)$. The bound is sharp. For $Z = 0$, every $f$ is a relation, and only $0$ obeys them all. The bound gives $0$.

**Example.** Let $Z$ be free of rank $r$ with basis $z_1, \dots, z_r$, and let $B = O/\varpi^M$. The map $(b_k) \mapsto \sum_k z_k b_k$ sends $B^r$ into $\operatorname{Obey}(\operatorname{Rel}(Z), B)$. If the $z_k$ stay independent modulo $\varpi$ at some finite set of points, this map is injective, and the theorem says that it is onto. So a cocycle modulo $\varpi^M$ that satisfies all relations of the lattice $Z$ is the reduction of an element of $Z \otimes O/\varpi^M$. In general the theorem gives only the inequality of lengths.

**Remark (Formalization).** The classical fact behind the theorem is that $\operatorname{Hom}_O(\operatorname{Hom}_O(Z, O), B) \cong Z \otimes_O B$ for a free module $Z$ of finite rank. The source never forms the tensor product. It describes the module by relations and bounds only its length. The theorem uses no topology on $\Gamma$ and no continuity of $\rho$ or of the cocycles. Continuity enters in Volume 12 through the choice of the lattice $Z$, not here.
