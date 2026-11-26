---
title: Grunwald's theorem and CM steps
lean:
  - Lib/ClassField/Grunwald.lean
  - Lib/GaloisRep/BaseChange/CommutingHeckeFamilies.lean
decls:
  - New.grunwald
  - New.QZChar.symmetrise
  - New.QZChar.abelianLift_symmetrise
  - New.QZChar.ideleChar
  - New.QZChar.stepField
  - New.QZChar.not_dvd_differentIdeal_stepField
  - New.IsStep
  - New.isStep_stepField
  - New.GaloisRep.IsStepOfLocalChar
  - New.GaloisRep.apply_eq_one_of_natCast_mem_asIdeal
  - New.GaloisRep.exists_isStepOfLocalChar
  - New.GaloisRep.exists_step_of_local_char
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Grunwald's theorem and CM steps

The global counts of the last two sections bound cohomology. This section and the next one are about existence. Grunwald's theorem gives a global character with prescribed local components at finitely many places. The source uses it to build CM extensions of prime degree, called *steps*, with a prescribed tame character at a split place. This section gives the classical theorem with Wang's correction, then the source's version in prime exponent, then the steps.

### The textbook form of Grunwald-Wang

Let $K$ be a number field, $n \geq 1$, $S$ a finite set of places of $K$, and for each $v \in S$ let $\chi_v$ be a continuous character of $K_v^\times$ of order dividing $n$. The question is whether there is a character $\chi$ of the idele class group $\mathbb{A}_K^\times/K^\times$ of order dividing $n$ whose restriction to $K_v^\times$ is $\chi_v$ for every $v \in S$.

**Remark (The Grunwald-Wang theorem).** Such a $\chi$ exists unless one is in the "special case". The special case can occur only if $8 \mid n$, and it depends on the field $K(\mu_{2^t})$ for the $2$-part $2^t$ of $n$ and on the places of $S$ above $2$. In particular, for $n = p$ prime, $\chi$ always exists. See E. Artin and J. Tate, *Class Field Theory* (Benjamin, 1968), Chapter X, and Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, Chapter IX, §2.

Grunwald stated the theorem in 1933 without the special case. Wang found the error in 1948. The standard example is $16$, which is an $8$-th power in $\mathbb{Q}_p$ for every odd prime $p$ but is not an $8$-th power in $\mathbb{Q}$ or in $\mathbb{Q}_2$. The reason is the factorization

$$x^8 - 16 = (x^2 - 2)(x^2 + 2)(x^2 - 2x + 2)(x^2 + 2x + 2).$$

For odd $p$, one of $2$, $-2$ and $-1$ is a square modulo $p$, so one of the four factors has a root in $\mathbb{Q}_p$. The last two factors have discriminant $-4$. An effective form of the theorem, with a bound for the conductor of $\chi$, is in S. Wang, "Grunwald-Wang theorem, an effective version", arXiv:1401.0389 (2014). The source cites both references.


### The source's version

**Theorem (Grunwald in prime exponent).** Let $E$ be totally complex, $p$ prime, $S$ a finite set of finite places, and $\psi$ a character of the finite ideles of $E$ with values in $\mathbb{Q}/\mathbb{Z}$, with open kernel and with $\psi^p = 1$. The character $\psi$ need not be trivial on $E^\times$. Then there is a continuous character $\chi$ of $\mathrm{Gal}(\Omega/E)$ with $p\chi = 0$ such that $\chi(\mathrm{Art}(x_u)) = \psi(x_u)$ for every idele $x_u$ with a single component $x$ at a place $u$, in these two cases: (a) $u \in S$, for all $x$, and (b) the norm of $u$ is not a prime number, for all units $x$.

Lean: `New.grunwald` (Lib/ClassField/Grunwald.lean).

Part (a) is the classical theorem in prime exponent. Part (b) is an extra. Since the kernel of $\psi$ is open, $\psi$ is trivial on the local units at almost all places, so (b) says that $\chi$ is unramified at almost all places of degree greater than one.

*Proof.* The source's proof follows the classical one. It enlarges $S$ to a finite set $T$ such that the principal ideles and the ideles that are units outside $T$ generate all finite ideles. By Dirichlet's unit theorem, the $T$-units are finitely generated, so there are finitely many classes of $T$-units modulo $p$-th powers. For each class $q$ that $\psi$ does not kill, Chebotarev gives a place $w_q$ of prime norm at which $q$ is not a local $p$-th power. Let $U$ be the open group of ideles that are units outside $T$ and $p$-th powers at every $w_q$. Then $\psi$ kills the principal ideles in $U$, and a lemma from the existence theorem (`exists_nsmul_eq_zero_abelianLift_artinMap_eq_of_apply_principalIdele_eq_one`, private in the same file) gives $\chi$. $\square$

The source works with finite ideles only. Over a totally complex field this loses nothing, because a character of finite order is trivial on the connected group $(\mathbb{C}^\times)^{r_2}$ at the infinite places. Over a field with real places, a character of order $2$ can be nontrivial at a real place, and the finite ideles do not see this. The source does not state the theorem for such fields.

### Symmetrised characters

From here on $E$ is a CM field, with complex conjugation $c$. For $g \in \mathrm{Gal}(\Omega/E)$ write $g^c = c g c$.

**Definition (Symmetrisation).** For a character $\chi : \mathrm{Gal}(\Omega/E) \to \mathbb{Q}/\mathbb{Z}$, `symmetrise χ` is the character $g \mapsto \chi(g) + \chi(g^c)$.

Lean: `New.QZChar.symmetrise` (Lib/ClassField/Grunwald.lean).

**Lemma.** On the Artin symbol of an idele $a$, `symmetrise χ` takes the value $\chi(\mathrm{Art}(a)) \cdot \chi(\mathrm{Art}(\bar a))$, in multiplicative notation.

Lean: `New.QZChar.abelianLift_symmetrise` (Lib/ClassField/Grunwald.lean).

**Definition (Idele character).** `ideleChar χ` is the character $\exp(2\pi i \, \chi \circ \mathrm{Art})$ of the finite ideles of $E$.

Lean: `New.QZChar.ideleChar` (Lib/ClassField/Grunwald.lean).

**Definition (Step field).** `stepField χ` is the fixed field in $\Omega$ of the kernel of `symmetrise χ`.

Lean: `New.QZChar.stepField` (Lib/ClassField/Grunwald.lean).

Instances in the same file show that `stepField χ` is a CM field, that a CM type of $E$ extends to it (`New.CMTypeOver`), and that it contains a primitive $5040$-th root of unity if $E$ does. The field is CM because the kernel of `symmetrise χ` is stable under $g \mapsto g^c$.

**Lemma (Unramified places).** Let $u$ be a finite place of `stepField χ`. If `symmetrise χ` kills the inertia groups at the places of $\Omega$ over the place of $E$ below $u$, then $u$ does not divide the relative different of `stepField χ` over $E$.

Lean: `New.QZChar.not_dvd_differentIdeal_stepField` (Lib/ClassField/Grunwald.lean).

### Steps

**Definition (Step).** For CM fields $E \subseteq E'$ and a character $\mu$ of the finite ideles of $E$, `IsStep E' μ` says the following. $E$ contains a primitive $5040$-th root of unity. $E'/E$ is Galois of prime degree. $\mu$ has open kernel and is trivial on $E^\times$. For each idele $z$, $\mu(z \bar z) = 1$ exactly when $z$ is a principal idele times a norm from the finite ideles of $E'$. Some integer of $E'$ has trace $1$ down to $E$.

Lean: `New.IsStep` (Lib/GaloisRep/BaseChange/CommutingHeckeFamilies.lean).

The chapter [CM fields, towers and places](/chapter/cm-fields/) treats the condition on roots of unity and the towers of CM fields. The norm condition is the class field theory of the cyclic extension $E'/E$, read through $z \mapsto z \bar z$.

**Theorem (The step field is a step).** Let $E$ be a CM field with a primitive $5040$-th root of unity, and let $p$ be prime. Suppose that (a) $p\chi = 0$, (b) `symmetrise χ` is not zero, and (c) `symmetrise χ` kills the inertia groups at the places above $p$. Then `stepField χ` has degree $p$ over $E$, and it is a step for `ideleChar χ`.

Lean: `New.isStep_stepField` (Lib/ClassField/Grunwald.lean).

The degree is the order of the image of `symmetrise χ`. This image is a nontrivial subgroup of the $p$-torsion of $\mathbb{Q}/\mathbb{Z}$, so it has order $p$. Hypothesis (c) gives the trace condition. If all traces of integers lay in a prime $u$ of $E$, then $u$ would contain $\mathrm{tr}(1) = p$. A prime above $u$ would then be unramified by (c), but it would divide the different. This contradiction is the private lemma `range_intTrace_stepField_eq_top`.

### Steps with a prescribed local character

The source needs steps in which a given split place $w$ of $E$ has a single place above it, with a given tame character.

**Lemma (Tame characters above $p$).** Let $\chi$ be a character of $E_w^\times$ with $\chi^p = 1$ that kills the $(q-1)$-th powers of units, where $q$ is the norm of $w$. If $w$ lies above $p$, then $\chi$ is trivial on the units of $E_w$.

Lean: `New.GaloisRep.apply_eq_one_of_natCast_mem_asIdeal` (Lib/ClassField/Grunwald.lean).

*Proof.* Since $p \mid q$, the numbers $p$ and $q - 1$ are coprime. For a unit $x$, $\chi(x)^p = 1$ and $\chi(x)^{q-1} = \chi(x^{q-1}) = 1$, so $\chi(x) = 1$. $\square$

**Definition (Step of a local character).** For a place $A$ of $\Omega$ over a finite place $w$ of $E$, a character $\chi$ of $E_w^\times$, a prime $p$, a Galois character $\nu$ and a place $u$ of `stepField ν`, the predicate `IsStepOfLocalChar A χ p ν u` has these fields. `stepField ν` has Weil data. It is a step for `ideleChar ν`, of degree $p$. The place $u$ is split, it lies below $A$, and it is the only place above $w$. Under the local Artin map at $w$, $\nu$ is trivial and `symmetrise ν` is $\chi$.

Lean: `New.GaloisRep.IsStepOfLocalChar` (Lib/ClassField/Grunwald.lean).

**Theorem (Grunwald for CM steps).** Let $E$ be a CM field with Weil data. Let $w$ be a split finite place of $E$, that is, $\bar w \neq w$, below the place $A$ of $\Omega$. Let $\chi \neq 1$ be a character of $E_w^\times$ with $\chi^p = 1$ for a prime $p$, that kills the $(q-1)$-th powers of units. Then there are $\nu$ and $u$ with `IsStepOfLocalChar A χ p ν u`.

Lean: `New.GaloisRep.exists_isStepOfLocalChar` (Lib/ClassField/Grunwald.lean).

Lean: `New.GaloisRep.exists_step_of_local_char` (Lib/ClassField/Grunwald.lean).

The second name is the same statement, with $\chi \neq 1$ given by a point $x_0$ with $\chi(x_0) \neq 1$.

*Proof.* Apply `New.grunwald` to $\psi(b) = \chi(\bar b_w)$, with $S = \{w, \bar w\} \cup \{u : u \mid p\}$. The resulting $\nu$ has $p\nu = 0$ and is trivial at $w$, so `symmetrise ν` is $\chi$ at $w$. At a place $u = \bar u$, the norm is not prime, because $E$ contains a primitive $5040$-th root of unity (`New.isSplit_of_q_prime`, Lib/General/NumberTheory/FrobeniusOrbits.lean). So (b) of `grunwald` shows that $\nu$ kills the local units there. At the places above $p$ it kills them by (a) and the last lemma. Since $\chi \neq 1$, `isStep_stepField` gives a step of degree $p$ in which only one place lies above $w$, and that place is split. By `not_dvd_differentIdeal_stepField` and `nonempty_weilData_of_not_dvd_differentIdeal` (next section), `stepField ν` has Weil data. $\square$

The users are in `Lib/GaloisRep/LocalGlobal/IwahoriCompatibility.lean` and `Lib/GaloisRep/LocalGlobal/LabelCompatibility.lean`.

**Remark (Formalization).** The source claims proofs of all statements of this section. Grunwald's theorem is proved only in prime exponent and only over totally complex fields, so the special case of Wang never arises. The proof is the classical one, from Dirichlet's unit theorem, Chebotarev and the existence theorem of class field theory; those inputs are in the chapter [Class field theory on finite ideles](/chapter/class-field-theory/). No statement of this section takes a duality statement or a reciprocity law as a hypothesis. The hypotheses with content are the existence of a primitive $5040$-th root of unity in $E$ and the Weil data on $E$. The Weil data come from the splitting characters of the next section, and that is where a hypothesis on the roots of unity of $E$ enters. If the reported checks hold, Lean accepts these statements with the hypotheses as stated.
