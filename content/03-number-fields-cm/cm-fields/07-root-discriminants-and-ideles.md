---
title: Root discriminants, the different and finite ideles
lean:
  - New/Reduction/Data/AdmissibleData.lean
  - New/Derivatives/Field/PrimeDecomposition.lean
  - Lib/ClassField/Places/Ideles.lean
decls:
  - New.one_le_rootDiscr
  - New.Parameters.relDifferentGen
  - New.Parameters.sqrtNegDInE
  - New.Parameters.relDifferentGen_dvd_q₁
  - New.Parameters.sqrtNegDInE_dvd_d
  - New.Parameters.differentIdeal_eq_span_relDifferentGen
  - New.Parameters.map_differentIdeal_eq_span_sqrtNegDInE
  - New.Parameters.differentIdeal_eq_span_relDifferentGen_mul
  - New.Parameters.conductor_mem_differentIdeal
  - New.principalIdele
  - New.idelesUnitOff
  - New.isCompact_idelesUnitOff_empty
  - New.IsTotallyPositive
  - New.exists_idele_classGroup_hom
  - New.pow_classNumber_mem_principal_sup
  - New.exists_superset_sup_idelesUnitOff_eq_top
  - New.finiteIndex_idele_subgroup_of_isOpen
  - New.eventually_unramified
status: drafted
drafted_by: writer@claude-opus-5-5
---

## Root discriminants, the different and finite ideles

The main theorem of the argument contains the number $\Omega = e^{C S} \cdot 2\pi / \mathrm{rd}_E$, with $\mathrm{rd}_E$ the root discriminant of $E$, as [the field E](/chapter/fields-places-twists/) states. This section gives the bound on $\mathrm{rd}_E$ that the argument uses and the computation of the different of $E$ behind it. It then gives the finite ideles of a number field, which carry the Hecke characters and the class field theory of [class field theory](/chapter/class-field-theory/).

### The classical theory of discriminants

Let $F$ be a number field of degree $n$ with discriminant $d_F$. The root discriminant of $F$ is $\mathrm{rd}_F = |d_F|^{1/n}$. Since $d_F$ is a nonzero integer, $\mathrm{rd}_F \ge 1$.

The different $\mathfrak{D}_F$ is the inverse of the dual of $\mathcal{O}_F$ under the trace form. It is an integral ideal, its norm is $|d_F|$, and it is multiplicative in towers: $\mathfrak{D}_{L/\mathbb{Q}} = \mathfrak{D}_{L/F} \mathfrak{D}_{F/\mathbb{Q}}$. If $\mathcal{O}_L = \mathcal{O}_F[\alpha]$ and $g$ is the minimal polynomial of $\alpha$, then $\mathfrak{D}_{L/F} = (g'(\alpha))$ (Neukirch, Ch. III, §2).

If an integer $c \ge 1$ lies in $\mathfrak{D}_F$, then $(c) \subset \mathfrak{D}_F$, so $N\mathfrak{D}_F$ divides $N(c) = c^n$, and $|d_F| \le c^n$. So
$$1 \le \mathrm{rd}_F \le c.$$

For $E = K(\zeta_{q_1})$, the ring of integers is $\mathcal{O}_K[\zeta_{q_1}]$, since $K$ and $\mathbb{Q}(\zeta_{q_1})$ have coprime discriminants. So $\mathfrak{D}_{E/K} = (\Phi'_{q_1}(\zeta_{q_1}))$, and $\Phi'_{q_1}(\zeta_{q_1})$ divides $q_1$, since $X^{q_1} - 1 = \Phi_{q_1} \cdot h$ gives $q_1 \zeta^{q_1 - 1} = \Phi'_{q_1}(\zeta) h(\zeta)$. The different of $K = \mathbb{Q}(i\sqrt d)$ is $(\sqrt{-d})$, and $\sqrt{-d}$ divides $d$. So $q_1 d \in \mathfrak{D}_E$ and $1 \le \mathrm{rd}_E \le q_1 d$.

### The source form

**Definition (Root discriminant).** For a number field $F$ of degree $n$, $\mathrm{rd}_F = |d_F|^{1/n}$ as a real number.

Mathlib: `NumberField.rootDiscr`.

**Lemma.** For every number field $F$, $1 \le \mathrm{rd}_F$.

Lean: `New.one_le_rootDiscr` (New/Reduction/Data/AdmissibleData.lean).

*Proof.* The discriminant is a nonzero integer, so $|d_F| \ge 1$, and a positive power of a real number $\ge 1$ is $\ge 1$. $\square$

The upper bound $\mathrm{rd}_F \le c$ for an integer $c \ne 0$ in the different is `New.rootDiscr_mem_Icc`, in [the field E](/chapter/fields-places-twists/). Its proof is the one above: Mathlib's `NumberField.absNorm_differentIdeal` (Mathlib) gives $N\mathfrak{D}_F = |d_F|$.

**Definition (Generators of the differents).** For the field $E = E_s$ of the parameters, let $\delta_{E/K} = \Phi'_{q_1}(\zeta) \in \mathcal{O}_E$, where $\zeta \in \mathcal{O}_E$ is the chosen primitive $q_1$-th root of unity, and let $\sqrt{-d} \in \mathcal{O}_E$ be the image of the square root of $-d$ in $\mathcal{O}_K$.

Lean: `New.Parameters.relDifferentGen`, `New.Parameters.sqrtNegDInE` (New/Derivatives/Field/PrimeDecomposition.lean).

**Theorem.** For the field $E$ of the parameters:

1. $\delta_{E/K}$ divides $q_1$ and $\sqrt{-d}$ divides $d$ in $\mathcal{O}_E$;
2. the different of $\mathcal{O}_E$ over $\mathcal{O}_K$ is $(\delta_{E/K})$;
3. the different of $K$, extended to $\mathcal{O}_E$, is $(\sqrt{-d})$;
4. the different of $E$ over $\mathbb{Z}$ is $(\delta_{E/K} \sqrt{-d})$;
5. $q_1 d$ lies in the different of $E$.

Lean: `New.Parameters.relDifferentGen_dvd_q₁`, `New.Parameters.sqrtNegDInE_dvd_d`, `New.Parameters.differentIdeal_eq_span_relDifferentGen`, `New.Parameters.map_differentIdeal_eq_span_sqrtNegDInE`, `New.Parameters.differentIdeal_eq_span_relDifferentGen_mul`, `New.Parameters.conductor_mem_differentIdeal` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Statement 1 is the computation above for $\delta_{E/K}$, and $\sqrt{-d} \cdot (-\sqrt{-d}) = d$. Statement 3 is the different of $K$ from Section 2, mapped to $\mathcal{O}_E$. For 2, the source shows that $\delta_{E/K}$ generates the different of $\mathbb{Q}(\zeta) \subset E$ over $\mathbb{Z}$ and is prime to $\sqrt{-d}$, since $\gcd(q_1, d) = 1$, and then compares the two factorisations of the different of $E$. Statement 4 is the tower formula with 2 and 3. Statement 5 follows from 1 and 4. $\square$

**Corollary.** $1 \le \mathrm{rd}_E \le q_1 d$.

Lean: `New.rootDiscr_mem_Icc` (New/Reduction/Data/AdmissibleData.lean).

**Remark (Formalization).** The argument uses only the bound of the corollary, and only through $\log \mathrm{rd}_E \le \log(q_1 d)$ in the choice of the constants. It does not need the exact value of $d_E$. The real power $|d_F|^{1/n}$ in Mathlib is `Real.rpow`, and it has no junk value here since $|d_F| \ge 1 > 0$. The bound $\mathrm{rd}_E \le q_1 d$ is weak, since $\mathrm{rd}$ of $\mathbb{Q}(\zeta_n)$ is $n / \prod_{p \mid n} p^{1/(p-1)}$, but it is enough for the argument.

### Finite ideles

Classically, the idele group $\mathbb{I}_F$ is the restricted product of the $F_v^\times$ over all places $v$, with respect to the unit groups $\mathcal{O}_v^\times$ (Neukirch, Ch. VI, §1). The source uses the finite ideles $\mathbb{A}_{F,f}^\times$, the units of the finite adele ring. For a totally complex field the infinite component is $(\mathbb{C}^\times)^{r_2}$, which is connected, so the finite ideles carry all the arithmetic of the open subgroups of finite index.

**Definition (Principal ideles and units off S).** The principal idele of $x \in F^\times$ is its image in $\mathbb{A}_{F,f}^\times$. For a set $S$ of finite places, $U^S$ is the group of finite ideles whose components at all places outside $S$ are units.

Lean: `New.principalIdele`, `New.idelesUnitOff` (Lib/ClassField/Places/Ideles.lean).

**Definition (Totally positive).** An element $x \in F$ is totally positive if $\varphi(x) > 0$ for every ring homomorphism $\varphi : F \to \mathbb{R}$.

Lean: `New.IsTotallyPositive` (Lib/ClassField/Places/Ideles.lean).

**Remark (Formalization).** For a totally complex field, there is no ring homomorphism $F \to \mathbb{R}$, so every element, including $0$, is totally positive. All fields of the argument are CM, so the hypothesis "totally positive" is empty for them, and a statement with it holds for all of $F^\times$.

**Theorem.** Let $F$ be a number field.

1. $U^\emptyset$ is compact.
2. There is a homomorphism $c : \mathbb{A}_{F,f}^\times \to \mathrm{Cl}(F)$ with kernel $F^\times U^\emptyset$.
3. For every finite idele $a$, $a^{h_F} \in F^\times U^\emptyset$, with $h_F$ the class number.
4. Every finite set $R$ of finite places is contained in a finite set $S$ with $\mathbb{A}_{F,f}^\times = F^\times U^S$.
5. An open subgroup $H$ of $\mathbb{A}_{F,f}^\times$ that contains the principal ideles of all totally positive $x \in F^\times$ has finite index.
6. A homomorphism from $\mathbb{A}_{F,f}^\times$ to a commutative group with open kernel is trivial on $\mathcal{O}_v^\times$ for all but finitely many $v$.

Lean: `New.isCompact_idelesUnitOff_empty`, `New.exists_idele_classGroup_hom`, `New.pow_classNumber_mem_principal_sup`, `New.exists_superset_sup_idelesUnitOff_eq_top`, `New.finiteIndex_idele_subgroup_of_isOpen`, `New.eventually_unramified` (Lib/ClassField/Places/Ideles.lean).

*Proof.* For 1, $U^\emptyset$ is the unit group of $\prod_v \mathcal{O}_v$, which is compact. For 2, send an idele to the class of its divisor $\prod_v \mathfrak{p}_v^{v(a_v)}$. The divisor is principal if and only if the idele is a principal idele times a unit idele. Statement 3 follows from 2, since the order of an element of a finite group divides its order. For 4, choose ideals that generate the class group and take their primes in $S$. For 5, the preimage of $H$ in $F^\times$ contains the kernel of the signs at the real embeddings, so it has finite index there. Then $H \cap U^\emptyset$ is open in a compact group, so it has finite index in $U^\emptyset$, and $F^\times U^\emptyset$ has finite index $h_F$ by 2. For 6, the open kernel contains a basic open subgroup, which contains $\mathcal{O}_v^\times$ for all $v$ outside a finite set. $\square$

**Remark (Formalization).** Statement 5 is the finiteness of ray class groups in the form the argument uses. For a CM field, the hypothesis on totally positive elements becomes "$H$ contains all principal ideles". In 2, the source gives $c$ by an existence statement, so the homomorphism is chosen. The source states the class group bound through `classNumber` (Mathlib), the cardinality of a finite type, which is positive. In the source, statement 5 gives the finite index of the kernels of characters in the Hecke character files (Lib/ClassField/HeckeCharacter/Basic.lean) and in the existence theorem of class field theory (Lib/ClassField/Global/ExistenceTheorem.lean), and statement 6 gives that such a character is unramified at almost all places.

### What the argument uses of discriminants and ideles

From this section, the argument uses three facts: the bound $1 \le \mathrm{rd}_E \le q_1 d$ in the constants of the main theorem, the finiteness statements 5 and 6 for the finite ideles of $E$ and of the fields in the base change steps, and the class group map 2 for the construction of characters with given local components.
