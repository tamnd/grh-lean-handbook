---
title: Local duality and the Greenberg-Wiles count in the argument
lean:
  - Lib/ClassField/LocalDuality/DualityInequality.lean
  - Lib/ClassField/LocalDuality/CrystallineDuality.lean
  - Lib/ClassField/GreenbergWiles/Relations.lean
  - Lib/ClassField/Grunwald.lean
  - Lib/ClassField/Global/CMSplittingCharacters.lean
decls:
  - New.card_mul_card_le_of_orthogonal
  - New.RelationSetting.exists_card_cocycles_le
  - New.grunwald
  - New.nonempty_splittingChar
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Local duality and the Greenberg-Wiles count in the argument

This chapter treats four results of the folder `Lib/ClassField` of the source. They are local duality for Galois modules over local fields, the formula of Greenberg and Wiles for Selmer groups, the theorem of Grunwald in prime exponent, and the existence of splitting characters on CM fields. The first two are counts of cohomology groups. The last two are existence results for characters with given local behaviour. The source uses all four in the part of the proof that bounds Selmer groups and builds CM extensions of prime degree.

The chapter is a background chapter. For each topic it first states the classical theorem, with a citation. Then it states exactly what the source proves, and it says which parts are hypotheses. Then it gives a remark on the formalization. The reader who knows Galois cohomology can read the source parts only. The reader who does not can read the classical parts first and use the books in the last section.

### What the source proves, in one paragraph

The source does not prove local Tate duality in the textbook form. It proves an inequality: if a group $X$ of 1-cocycles with values in the Cartier dual $M^\vee$ and a group $W$ of 1-cocycles with values in $M$ are orthogonal under the cup product, then $\#X \cdot \#W \leq \#M^{2+d}$, where $\#(\mathcal{O}/l) = l^d$. It also proves a divisibility for orthogonal groups, but with a hypothesis that a maximal orthogonal pair exists over an open subgroup. It does not prove the Greenberg-Wiles formula. It proves one inequality, with a module of "relations" in the place of the dual Selmer group, over a totally complex field. It proves Grunwald's theorem only in prime exponent and only over totally complex fields. It proves that a splitting character exists under a hypothesis on the roots of unity of the field.

### The four results

The source states the local inequality as follows.

**Theorem (Local duality as an inequality).** Let $k$ be a local field in the sense of `New.IsLocalGalois`, with valuation ring $\mathcal{O}$, and let $\#(\mathcal{O}/l) = l^d$ for a prime $l$. Let $M$ be a finite discrete $\Gamma$-module killed by $l^r$, on which $\Gamma$ acts through a pro-$l$ quotient. If $X \subseteq Z^1(M^\vee)$ and $W \subseteq Z^1(M)$ are orthogonal under the cup product, then $\#X \cdot \#W \leq \#M^{2+d}$.

Lean: `New.card_mul_card_le_of_orthogonal` (Lib/ClassField/LocalDuality/DualityInequality.lean).

The global count is the following one.

**Theorem (A case of the Greenberg-Wiles formula, one inequality).** Let $K$ be a totally complex number field, and let $M$ be a finite Galois module killed by $\ell^r$ with $r \neq 0$, with local conditions $A_v$ on a finite set $S$ of primes. Suppose that some $\sigma$ has cyclotomic character $1$, is central modulo the open subgroup $U$ of the setting, and fixes no nonzero element of $M$. Then for some finite set $T \supseteq S$, $\#Z(\emptyset) \cdot \#M^{\#S + r_2} \leq \#\mathrm{Rel}(T) \cdot \#M \cdot \prod_{v \in S} \#A_v$.

Lean: `New.RelationSetting.exists_card_cocycles_le` (Lib/ClassField/GreenbergWiles/Relations.lean).

Here $Z(\emptyset)$ is a group of Selmer cocycles, not of classes, and $\mathrm{Rel}(T)$ is the module of relations. Section [Relations in place of the dual Selmer group](/chapter/local-duality/#relations-in-place-of-the-dual-selmer-group) explains both.

**Theorem (Grunwald in prime exponent).** Let $E$ be totally complex, $p$ prime, $S$ a finite set of finite places, and $\psi$ a character of the finite ideles of $E$ with open kernel and $\psi^p = 1$. Then a Galois character $\chi$ with $p\chi = 0$ agrees with $\psi$ through the Artin map at the places of $S$, and on the local units at the places whose norm is not prime.

Lean: `New.grunwald` (Lib/ClassField/Grunwald.lean).

**Theorem (Splitting characters).** Let $E$ be a CM field with a CM type $\Phi$ that contains a primitive root of unity of order $5040$. Suppose that every root of unity $y$ of $E$ is $\delta/\bar\delta$ for a unit $\delta$ of $\mathcal{O}_E$ with $\prod_w \Phi_w(\delta) = 1$. Then $E$ has a splitting character.

Lean: `New.nonempty_splittingChar` (Lib/ClassField/Global/CMSplittingCharacters.lean).

### Where the chapter sits

The chapter [CM fields, towers and places](/chapter/cm-fields/) gives the CM fields, the CM types, the places and the condition that $\mu_{5040} \subset E$. The chapter [Class field theory on finite ideles](/chapter/class-field-theory/) gives the cochains, the Brauer group $\mathrm{Br}(k) = \mathbb{Q}/\mathbb{Z}$, reciprocity, the existence theorem and Chebotarev. This chapter uses all of these. The proof of the local inequality uses the invariant map of the local Brauer group. The proof of the global inequality uses Chebotarev to find auxiliary split primes. The proof of Grunwald's theorem uses Chebotarev and the existence theorem.

The users of the results are in the part of the source that bounds Selmer groups. `New.RelationSetting.exists_card_cocycles_le` is used in `New/Congruences/Selmer/Count.lean`. The variant `New.RelationSetting.exists_pow_le_card_reductions` is used in `New/Congruences/FirstOrder/KummerMaps.lean`, over the maximal real subfield of a CM field. The divisibility of local duality is used for potentially crystalline lattices in the same file as its proof. The splitting character gives the Weil data of the field of the main construction through the instance `New.instWeilDataE` in `New/Derivatives/Field/WeilData.lean`.

### The sections

1. This section.
2. [Galois cohomology of local fields](/chapter/local-duality/#galois-cohomology-of-local-fields): the setting `New.IsLocalGalois`, continuous cocycles, Kummer theory and the count of Kummer cocycles.
3. [Local Tate duality as an inequality](/chapter/local-duality/#local-tate-duality-as-an-inequality): Tate duality and the Euler characteristic formula, then the inequality and the divisibility of the source, with the hypothesis on a maximal pair.
4. [Duality for crystalline cocycles](/chapter/local-duality/#duality-for-crystalline-cocycles): the Bloch-Kato orthogonality, then the source's count for potentially crystalline lattices.
5. [Selmer groups and the Greenberg-Wiles formula](/chapter/local-duality/#selmer-groups-and-the-greenberg-wiles-formula): the classical formula, then the Selmer cocycles, the trivialised cocycles and power residue reciprocity of the source.
6. [Relations in place of the dual Selmer group](/chapter/local-duality/#relations-in-place-of-the-dual-selmer-group): the setting, the relations, and the two global counts.
7. [Grunwald's theorem and CM steps](/chapter/local-duality/#grunwalds-theorem-and-cm-steps): the Grunwald-Wang theorem, then the source's version and the steps of prime degree.
8. [Splitting characters and Weil data](/chapter/local-duality/#splitting-characters-and-weil-data): Weil's characters, then the source's existence result and its lift to extensions.
9. Exercises, and notes and references.

### Conventions

The source writes $\Omega$ for an algebraically closed field of characteristic $0$ and $\Gamma$ for a profinite group that acts on it. A local field is not complete in the source. It is a field $k$ whose valuation ring $\mathcal{O} = A \cap k$ is a discrete valuation ring with finite residue field, where $A$ is a valuation subring of $\Omega$. The text writes $Z^1(M)$ for the continuous 1-cocycles $\Gamma \to M$, $B^1(M)$ for the 1-coboundaries and $H^1(M) = Z^1(M)/B^1(M)$. Many statements of the source are about $Z^1$, not about $H^1$. The text says which one each time. It writes $\#X$ for the number of elements of a set $X$, which is `Nat.card X` in Lean. If $X$ is infinite, then `Nat.card X` is $0$. So a statement $0 < \#X$ in the source says that $X$ is finite and not empty.

**Remark (Formalization).** The source claims a proof of each of the four results above. The hypotheses with content are of three kinds. The first is the maximal orthogonal pair in `New.DiscreteModule.local_duality_card_dvd`. The second is the reciprocity law at split primes, which is a field of the predicate `New.RelationSetting.IsRelation` and so is part of the definition of a relation. The third is the condition on roots of unity in `New.nonempty_splittingChar`. The text never says that these results are correct. It says what the source claims, and what Lean accepts if the reported checks hold.
