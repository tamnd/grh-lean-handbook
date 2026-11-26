---
title: The different and its imaginary generator
lean:
  - New/Derivatives/Field/PrimeDecomposition.lean
  - Lib/General/NumberTheory/EmbeddingsAndDifferent.lean
  - Lib/Adelic/Adeles/Basic.lean
decls:
  - New.Parameters.eval_derivative_cyclotomic_dvd_q₁
  - New.Parameters.map_differentIdeal_adjoin_eq_span
  - New.Parameters.span_derivative_cyclotomic_dvd_differentIdeal
  - New.Parameters.differentIdeal_eq_span_and_adjoin_eq_top
  - New.Parameters.relDifferent_spec
  - New.Parameters.relDifferentGen_eq_prod_sub
  - New.Parameters.exists_unit_mul_zetaInt_sub_real
  - New.Parameters.exists_unit_mul_relDifferentGen_real
  - New.Parameters.differentGenPhase
  - New.Parameters.star_differentGenPhase_mul_self
  - New.Parameters.star_differentGenPhase_mul_relDifferentGen
  - New.Parameters.isUnit_differentGenPhase
  - New.Parameters.deltaE
  - New.Parameters.star_deltaE
  - New.Parameters.differentIdeal_eq_span_deltaE
  - New.Parameters.prod_deltaE_eq_rootDiscr_pow
  - New.Parameters.norm_Φ_differentGenPhase
  - New.Parameters.infinitePlace_apply_deltaE
  - New.Parameters.placePerm
  - New.Parameters.apply_Phi_eq_Phi_placePerm
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The different and its imaginary generator

This section computes the different of $E$ and gives it a generator $\varpi$ with $\bar\varpi = -\varpi$. The product of the absolute values of $\varpi$ at the infinite places is $\mathrm{rd}_E^f$. Section 6 bounds each factor, and so bounds $\mathrm{rd}_E$.

### A square root of $-1$

The order $q_1$ is a multiple of $18480 \cdot 3 = 55440 = 11 \cdot 5040$, since $3$ divides $\mathrm{towerDeg}(s)$. So the power $\zeta^{q_1/5040}$ is a primitive root of unity of order $5040$, and $E$ satisfies the class `HasPrimitiveRoot5040` of [fields, places and twists](/chapter/fields-places-twists/). The source gives this as an unnamed instance in New/Derivatives/Field/PrimeDecomposition.lean, line 138. In this chapter the root of order $5040$ has one use: its power of order $4$ is an element $i \in \mathcal{O}_E$ with $i^2 = -1$ and $\bar i = -i$ (Lean: `New.HasPrimitiveRoot5040.exists_mul_self_eq_neg_one`). Of course $i = \zeta^{q_1/4}$ also works, and the proof of the lemma on roots of unity in Section 5 takes this element.

### The different of $E/K$

Let $z \in \mathcal{O}_E$ be any primitive root of unity of order $q_1$, and write $\Phi_{q_1}$ for the cyclotomic polynomial of order $q_1$.

**Lemma.** $\Phi_{q_1}'(z)$ divides $q_1$ in $\mathcal{O}_E$.

Lean: `New.Parameters.eval_derivative_cyclotomic_dvd_q₁` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Write $X^{q_1} - 1 = \Phi_{q_1}(X) Q(X)$ with $Q \in \mathcal{O}_E[X]$. Take the derivative and evaluate at $z$. Since $\Phi_{q_1}(z) = 0$, this gives $q_1 z^{q_1 - 1} = \Phi_{q_1}'(z) Q(z)$. Multiply by $z$ and use $z^{q_1} = 1$: $q_1 = \Phi_{q_1}'(z) \cdot Q(z) z$. $\square$

**Lemma (Euler).** The different of $\mathbb{Q}(z)$ over $\mathbb{Q}$, extended to $\mathcal{O}_E$, is the principal ideal $(\Phi_{q_1}'(z))$.

Lean: `New.Parameters.map_differentIdeal_adjoin_eq_span` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* The ring of integers of the cyclotomic field $\mathbb{Q}(z)$ is $\mathbb{Z}[z]$, and the minimal polynomial of $z$ over $\mathbb{Z}$ is $\Phi_{q_1}$. For a monogenic order $\mathbb{Z}[z]$, the conductor times the different is $(\mu'(z))$, where $\mu$ is the minimal polynomial. Here the conductor is the unit ideal. So the different of $\mathbb{Q}(z)$ is $(\Phi_{q_1}'(z))$. Extend to $\mathcal{O}_E$. $\square$

**Lemma.** The ideal $(\Phi_{q_1}'(z))$ divides the different $\mathfrak{D}_{E/K}$.

Lean: `New.Parameters.span_derivative_cyclotomic_dvd_differentIdeal` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* The field $E$ is the compositum of $K$ and $\mathbb{Q}(z)$. The different of $K$ extended to $\mathcal{O}_E$ is $(\sqrt{-d})$ ([CM fields](/chapter/cm-fields/)), and $\sqrt{-d}$ divides $d$. By the last lemma the different of $\mathbb{Q}(z)$ extended to $\mathcal{O}_E$ is $(\Phi_{q_1}'(z))$, and $\Phi_{q_1}'(z)$ divides $q_1$. As $q_1$ and $d$ are coprime, the two extended differents are coprime. For a compositum of two subfields with coprime extended differents, the extended different of one subfield divides the relative different of $E$ over the other. So $(\Phi_{q_1}'(z))$ divides $\mathfrak{D}_{E/K}$. $\square$

**Theorem.** Let $z \in \mathcal{O}_E$ be a primitive root of unity of order $q_1$. Then:

1. $\Phi_{q_1}'(z)$ divides $q_1$;
2. $\mathfrak{D}_{E/K} = (\Phi_{q_1}'(z))$;
3. $\mathcal{O}_E = \mathcal{O}_K[z]$.

Lean: `New.Parameters.relDifferent_spec`, `New.Parameters.differentIdeal_eq_span_and_adjoin_eq_top` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Part 1 is the first lemma. For parts 2 and 3, the element $z$ generates $E$ over $K$, it is a root of the monic polynomial $\Phi_{q_1} \in \mathcal{O}_K[X]$, and $(\Phi_{q_1}'(z))$ divides $\mathfrak{D}_{E/K}$ by the last lemma. The conductor $\mathfrak{f}$ of $\mathcal{O}_K[z]$ satisfies $\mathfrak{f} \mathfrak{D}_{E/K} = (\Phi_{q_1}'(z))$ (the same formula as in the lemma of Euler, now over $\mathcal{O}_K$). Since $(\Phi_{q_1}'(z))$ divides $\mathfrak{D}_{E/K}$, $\mathfrak{f}$ is the unit ideal. So $\mathfrak{D}_{E/K} = (\Phi_{q_1}'(z))$ and $\mathcal{O}_K[z] = \mathcal{O}_E$. The general statement is `New.differentIdeal_eq_span_of_dvd` (Lib/General/NumberTheory/EmbeddingsAndDifferent.lean). $\square$

For $z = \zeta$ we write $\delta_{E/K} = \Phi_{q_1}'(\zeta)$, as in [CM fields](/chapter/cm-fields/). That chapter states the consequences: $\delta_{E/K} \mid q_1$, $\mathfrak{D}_{E/K} = (\delta_{E/K})$, $\mathfrak{D}_{E/\mathbb{Q}} = (\delta_{E/K}\sqrt{-d})$ by the tower formula, and $q_1 d \in \mathfrak{D}_{E/\mathbb{Q}}$.

### A real multiple of $\delta_{E/K}$

**Lemma.** $\delta_{E/K} = \prod_a (\zeta - a)$, where $a$ runs over the primitive roots of unity of order $q_1$ in $\mathcal{O}_E$ other than $\zeta$.

Lean: `New.Parameters.relDifferentGen_eq_prod_sub` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* $\Phi_{q_1}(X) = \prod_b (X - b)$ over all primitive roots $b$, since $E$ contains all of them. Take the derivative by the product rule and evaluate at $\zeta$. Every term except one has the factor $\zeta - \zeta = 0$. $\square$

**Lemma.** Let $a$ be a primitive root of unity of order $q_1$ in $\mathcal{O}_E$. Some $u \in \mathcal{O}_E$ with $\bar u u = 1$ makes $u(\zeta - a)$ real, that is, fixed by complex conjugation.

Lean: `New.Parameters.exists_unit_mul_zetaInt_sub_real` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Write $a = \zeta^l$ with $l$ prime to $q_1$. Since $q_1$ is even, $l$ is odd, $l = 2e + 1$. Let $i$ be the square root of $-1$ above and put $u = i \bar\zeta^{e+1}$. Then $\bar u u = (-i)(i)\zeta^{e+1}\bar\zeta^{e+1} = 1$, since $\bar\zeta \zeta = 1$. Also
$$u(\zeta - \zeta^{2e+1}) = i\left(\bar\zeta^{e} - \zeta^{e}\right).$$
The factor $\bar\zeta^e - \zeta^e$ is purely imaginary and $i$ is purely imaginary, so the product is real. $\square$

**Lemma.** Some $c \in \mathcal{O}_E$ with $\bar c c = 1$ makes $c\,\delta_{E/K}$ real.

Lean: `New.Parameters.exists_unit_mul_relDifferentGen_real` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Take $c = \prod_a u_a$ with $u_a$ from the last lemma, one for each factor $\zeta - a$ of $\delta_{E/K}$. Then $\bar c c = \prod_a \bar u_a u_a = 1$ and $c\,\delta_{E/K} = \prod_a u_a(\zeta - a)$ is a product of real elements. $\square$

**Definition (The phase).** The phase $c$ is an element of $\mathcal{O}_E$ chosen among those of the last lemma. It satisfies $\bar c c = 1$, $\overline{c\,\delta_{E/K}} = c\,\delta_{E/K}$, and $c$ is a unit.

Lean: `New.Parameters.differentGenPhase`, `New.Parameters.star_differentGenPhase_mul_self`, `New.Parameters.star_differentGenPhase_mul_relDifferentGen`, `New.Parameters.isUnit_differentGenPhase` (New/Derivatives/Field/PrimeDecomposition.lean).

**Remark (Formalization).** Lean defines the phase by `choose` from the existence lemma, so it has no formula. The choice changes $c$ only by a sign. Let $c$ and $c'$ both have the two properties. Then $u = c' \bar c$ satisfies $u = c'/c = (c'\delta_{E/K})/(c\,\delta_{E/K})$, so $u$ is real. Each $\Phi_v(u)$ is then a real number of absolute value $1$, so $\Phi_v(u^2) = 1$ for all $v$, and also at the conjugate embeddings. So $u^2 = 1$ and $u = \pm 1$. The statements of this chapter use $c$ only through the two properties and through $|\Phi_v(c)| = 1$, so they hold for both signs.

### The imaginary generator $\varpi$

**Definition (The imaginary generator).** $\varpi = c\,\delta_{E/K}\sqrt{-d} \in \mathcal{O}_E$.

Lean: `New.Parameters.deltaE` (New/Derivatives/Field/PrimeDecomposition.lean).

The source comments write $\varpi$ for this element, and the Lean name is `deltaE`. The book keeps $\varpi$.

**Theorem.** $\bar\varpi = -\varpi$, and $\varpi$ generates the different of $E$ over $\mathbb{Q}$: $\mathfrak{D}_{E/\mathbb{Q}} = (\varpi)$.

Lean: `New.Parameters.star_deltaE`, `New.Parameters.differentIdeal_eq_span_deltaE` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* The factor $c\,\delta_{E/K}$ is real and $\overline{\sqrt{-d}} = -\sqrt{-d}$, so $\bar\varpi = -\varpi$. The different of $E$ over $\mathbb{Q}$ is $(\delta_{E/K}\sqrt{-d})$ by [CM fields](/chapter/cm-fields/), and $c$ is a unit, so $(\varpi) = (\delta_{E/K}\sqrt{-d})$. $\square$

**Lemma.** For every infinite place $v$, $|\Phi_v(c)| = 1$ and $|\varpi|_v = |\delta_{E/K}|_v \sqrt{d}$.

Lean: `New.Parameters.norm_Φ_differentGenPhase`, `New.Parameters.infinitePlace_apply_deltaE` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Complex conjugation on $E$ corresponds to complex conjugation on $\mathbb{C}$ under each $\Phi_v$, since $E$ is a CM field. So $\bar c c = 1$ gives $|\Phi_v(c)|^2 = 1$. The absolute value at $v$ is $|x|_v = |\Phi_v(x)|$, and $|\Phi_v(\sqrt{-d})| = \sqrt{d}$. Take absolute values in $\varpi = c\,\delta_{E/K}\sqrt{-d}$. $\square$

**Theorem.** $\prod_{v \in \Phi} |\varpi|_v = \mathrm{rd}_E^{\,f}$.

Lean: `New.Parameters.prod_deltaE_eq_rootDiscr_pow` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* Both sides are positive, so we compare their squares. The square of the left side is the product of $|\tau(\varpi)|$ over all $2f$ embeddings $\tau$ of $E$, which is $|N_{E/\mathbb{Q}}(\varpi)|$. This is the absolute norm of the ideal $(\varpi) = \mathfrak{D}_{E/\mathbb{Q}}$. The absolute norm of the different is $|d_E|$. As $E$ has degree $2f$, $|d_E| = \mathrm{rd}_E^{2f} = (\mathrm{rd}_E^f)^2$ (Lean: `New.abs_discr_eq_rootDiscr_pow`). $\square$

So $\log \mathrm{rd}_E$ is the mean of the numbers $\log|\varpi|_v$. Section 6 shows that these numbers are all close to $\log(\mathrm{towerDeg}(s)\sqrt{d})$, and so $\log \mathrm{rd}_E$ is close to each of them.

**Example.** In the model of Section 1, with $q_1 = 12$ and $d = 23$, we found $\delta_{E/K} = 2\zeta(2\zeta^2 - 1)$. Here $i = \zeta^3$, and $c = \zeta^2 = i\bar\zeta$ has $\bar c c = 1$ and $c\,\delta_{E/K} = 2\zeta^3(2\zeta^2 - 1)$. Under the embedding with $\zeta = e^{2\pi i/12}$ this is $2i \cdot i\sqrt{3} = -2\sqrt{3}$, which is real. So $\varpi$ maps to $-2\sqrt{3} \cdot i\sqrt{23} = -2i\sqrt{69}$. Then $|\varpi|_v = 2\sqrt{69}$ at all four places, and $\prod_v |\varpi|_v = 2^4 \cdot 69^2 = \mathrm{rd}_E^4$, as the theorem says. By the remark, every admissible phase is $\pm\zeta^2$.

### Automorphisms of $\mathbb{C}$ and the places

The later chapters apply automorphisms $\sigma$ of $\mathbb{C}$ over $K$ to the values $\Phi_v(x)$. Such a $\sigma$ permutes the embeddings $\Phi_v$, and the permutation is a translation in the group $\Phi$.

**Definition (The permutation of the places).** For $\sigma \in \mathrm{Aut}(\mathbb{C}/K)$, let $v_\sigma$ be the place of the embedding $\sigma \circ \Phi_1$. The permutation $\pi_\sigma$ of $\Phi$ is $v \mapsto v_\sigma v$.

Lean: `New.Parameters.placePerm` (New/Derivatives/Field/PrimeDecomposition.lean).

**Lemma.** For $\sigma \in \mathrm{Aut}(\mathbb{C}/K)$, $v \in \Phi$ and $x \in E$, $\sigma(\Phi_v(x)) = \Phi_{\pi_\sigma(v)}(x)$.

Lean: `New.Parameters.apply_Phi_eq_Phi_placePerm` (New/Derivatives/Field/PrimeDecomposition.lean).

*Proof.* The map $\sigma \circ \Phi_1$ is an embedding of $E$ over $K$. Two embeddings over $K$ that induce the same place are equal, since the conjugate of an embedding over $K$ is not over $K$ (Lean: `New.Parameters.algHom_eq_of_mk_eq`). So $\sigma \circ \Phi_1 = \Phi_{v_\sigma}$. With $\Phi_{v'v} = \Phi_{v'} \circ \sigma_v$ (Lean: `New.Parameters.phi_mul`),
$$\sigma(\Phi_v(x)) = \sigma(\Phi_1(\sigma_v x)) = \Phi_{v_\sigma}(\sigma_v x) = \Phi_{v_\sigma v}(x). \qquad \square$$

So for every $x \in E$ the family $(|\sigma(\Phi_v x)|)_v$ is the family $(|x|_v)_v$ in another order. In particular $\prod_v |\sigma(\Phi_v x)| = \prod_v |x|_v$. [The integral vacuum](/chapter/integral-vacuum/) uses this lemma for the conjugates of the vacuum.

**Remark (Formalization).** The source writes `Φ v` both for the embedding at $v$ (a ring homomorphism $E \to \mathbb{C}$) and, as `P.Φ s`, for the type of places. The book writes $\Phi_v$ for the first and $\Phi$ for the second. The value $v(x)$ in Lean is the absolute value $|x|_v = |\Phi_v(x)|$; the book writes $|x|_v$.
