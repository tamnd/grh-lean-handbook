---
title: The level structure of the Bessel data
lean:
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/Unfolding/BesselLevelStructure.lean
  - New/Spanning/Unfolding/Terms.lean
decls:
  - New.Filling.selfDualChar
  - New.Filling.selfDualChar_eq_one_of_mem
  - New.Filling.unipotentChar
  - New.Filling.Agrees
  - New.Filling.mem_termsOver_reduction_iff
  - New.besselU_dense
  - New.Filling.exists_besselU_approx
  - New.Filling.unipotentChar_eq_of_mem_principalLevel
  - New.Filling.exists_rat_approx_unipotentChar_eq
  - New.Filling.mem_reducedImage_besselU_iff_exists_termsOver
  - New.Filling.prod_wave_simpleRootSum_adelicToInf
  - New.Filling.prod_wave_simpleRootSum_ratToInf
  - New.Filling.prod_wave_eq_star_unipotentChar
  - New.Filling.eq_and_mem_classUnipotent_of_besselS
  - New.Filling.exists_besselS_mem_termsOver
  - New.Filling.frameImage_inv_mul_eq_iff
  - New.Filling.mem_besselS_of_frameImage_eq_one
  - New.Filling.termsOver.inv_mul_mem_reducedImage
  - New.Filling.termsOver.eq_and_mem_classUnipotent₀
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The level structure of the Bessel data

The unfolded sum has one block for each $(c, s, c')$. The identity terms of a block are its terms in the Bessel subgroup $R_0$. This section shows three things. The rational points of $\mathsf{U}$ reach every reduction that the integral points of $\mathsf{U}(\mathbb{A}_f)$ reach. The character of $\mathsf{U}$ at infinity is the conjugate of a character at the finite places. A term in $R_0$ over a block of reduction $1$ lies in $\mathsf{U}_c(M)$. With these facts the identity terms give the diagonal contribution of [the chapter on the moments](/chapter/moments/).

### The character of the unipotent group

For an isometry $s$ in $R_0$, let $\sigma(s)$ be the sum of the entries just above the diagonal of the block of $s$ on the frame, that is $\sigma(s) = \sum_{a < \varrho} s_{\mathfrak{f}_a\mathfrak{f}_{a+1}}$. This is [the function](/decl/New.simpleRootSum/) of [the chapter on Bessel subgroups](/chapter/bessel-bruhat/). It is additive on $R_0$ ([Lemma](/decl/New.simpleRootSum_mul/)), and it vanishes on $H$ ([Lemma](/decl/New.simpleRootSum_eq_zero_of_mem_besselH/)). Let $\varpi$ be the chosen generator of the different of $E$, with $\bar\varpi = -\varpi$, and let $\psi_f$ be the finite part of the standard additive character of $\mathbb{A}_E/E$.

**Definition (The self-dual character).** The character $\psi^\natural$ of $\mathbb{A}_f$ is $\psi^\natural(x) = \psi_f(-x/\varpi)$.

Lean: `New.Filling.selfDualChar` (New/Spanning/Unfolding/Setup.lean).

**Lemma (The self-dual character is trivial on integers).** If $x \in \hat{\mathcal{O}}_E$, then $\psi^\natural(x) = 1$.

Lean: `New.Filling.selfDualChar_eq_one_of_mem` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* The character $\psi_f$ is trivial on $y$ exactly when $y$ lies in the inverse different, locally at each place. Since $\varpi$ generates the different, $-x/\varpi$ lies in the inverse different for every integral $x$. $\square$

**Definition (The unipotent character).** For $u \in G(\mathbb{A}_f)$, $\chi(u) = \psi^\natural(M^{-1}\sigma(u))$. An element $s \in \bar G$ *agrees* if $\chi(u) = \chi(u')$ for all $u, u' \in K \cap \mathsf{U}(\mathbb{A}_f)$ whose reductions satisfy $\bar{u}s = s\bar{u}'$.

Lean: `New.Filling.unipotentChar` (New/Spanning/Unfolding/Setup.lean). Lean: `New.Filling.Agrees` (New/Spanning/Unfolding/Setup.lean).

**Remark (Formalization).** The source defines $\chi$ on all of $G(\mathbb{A}_f)$, with the formula for $\sigma$ applied to any matrix. It is a character only on $R_0(\mathbb{A}_f)$, and the chapter uses it only there.

The character $\chi$ depends only on $u$ modulo $K(M)$ and modulo conjugation by $H$. This is the next lemma.

**Lemma (The character is constant on level classes).** Let $u, v \in \mathsf{U}(\mathbb{A}_f)$, let $g \in U(X_0)(\mathbb{A}_f)$ and let $h$ be its image in $G(\mathbb{A}_f)$. If $u^{-1}h^{-1}vh \in K(M)$, then $\chi(v) = \chi(u)$.

Lean: `New.Filling.unipotentChar_eq_of_mem_principalLevel` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* Put $k = u^{-1}h^{-1}vh$. The elements $u, v, h$ lie in $R_0(\mathbb{A}_f)$, so $k$ does too. From $vh = hu k$ and the additivity of $\sigma$ on $R_0$ we get $\sigma(v) + \sigma(h) = \sigma(h) + \sigma(u) + \sigma(k)$, so $\sigma(v) = \sigma(u) + \sigma(k)$. Since $k \in K(M)$, the matrix $k - 1$ has entries in $M\hat{\mathcal{O}}_E$. The entries that $\sigma$ adds lie off the diagonal, so $M^{-1}\sigma(k)$ is integral. By the previous lemma $\psi^\natural(M^{-1}\sigma(k)) = 1$, and so $\chi(v) = \chi(u)\psi^\natural(M^{-1}\sigma(k)) = \chi(u)$. $\square$

### Strong approximation for the unipotent group

**Lemma (Terms with a given reduction).** Let $k \in K$, let $c, d$ be classes and let $\gamma$ be rational. Then $\gamma$ is a term over $(c, \bar{k}, d)$ if and only if $k^{-1}\gamma_{c,d} \in K(M)$.

Lean: `New.Filling.mem_termsOver_reduction_iff` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* If $\gamma_{c,d} = k'$ with $k' \in K$ and $\bar{k}' = \bar{k}$, then $k^{-1}k'$ lies in $K$ and reduces to $1$. Conversely, if $k^{-1}\gamma_{c,d} = k'' \in K(M)$, then $\gamma_{c,d} = kk''$ lies in $K$ and reduces to $\bar{k}$. $\square$

**Theorem (Density of the rational unipotent points).** Let $T$ be a nondegenerate hermitian form over $E$ and let $T'$ be its image over $\mathbb{A}_f$. Then $\mathsf{U}(\mathbb{A}_f)$ for $T'$ lies in the closure of the image of $\mathsf{U}(E)$ for $T$.

Lean: `New.besselU_dense` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* The group $\mathsf{U}$ is built floor by floor from unipotent groups $U_l$. Each $U_l$ is parametrized by a Heisenberg group, that is, by pairs $(x, y)$ of vectors with a skew condition on $y$ ([the chapter on Bessel subgroups](/chapter/bessel-bruhat/)). The parametrization is continuous and commutes with the inclusion $E \to \mathbb{A}_f$. The field $E$ is dense in $\mathbb{A}_f$, and the skew elements of $E$ are dense in the skew elements of $\mathbb{A}_f$. So the rational points of each $U_l$ are dense in its adelic points. A product of elements of the closures lies in the closure, so every element of $\mathsf{U}(\mathbb{A}_f)$ does. $\square$

This is strong approximation for the unipotent group $\mathsf{U}$.

**Lemma (Approximation by rational unipotent points).** Let $x \in \mathsf{U}(\mathbb{A}_f)$ and $y \in G(\mathbb{A}_f)$. There is a rational $u \in \mathsf{U}$ with $y^{-1}x^{-1}uy \in K(M)$.

Lean: `New.Filling.exists_besselU_approx` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* The set $V$ of the $z$ with $y^{-1}x^{-1}zy \in K(M)$ is open, since $K(M)$ is open. It contains $x$. By the density theorem, $V$ meets the image of $\mathsf{U}(E)$. A point $u$ of the intersection is the required element. $\square$

**Lemma (Rational approximation with the same character).** Let $S$ be admissible, let $c$ be a class and let $u \in \mathsf{U}(\mathbb{A}_f)$. There is a rational $u_0 \in \mathsf{U}$ with $u^{-1}(u_0)_{c,c} \in K(M)$ and $\chi(u_0) = \chi(u)$.

Lean: `New.Filling.exists_rat_approx_unipotentChar_eq` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* The representative $h_c$ lies in $R_0(\mathbb{A}_f)$, and $R_0$ normalizes $\mathsf{U}$ ([Lemma](/decl/New.besselS_le_normalizer_besselU/)). So $h_cuh_c^{-1} \in \mathsf{U}(\mathbb{A}_f)$. Apply the previous lemma with $x = h_cuh_c^{-1}$ and $y = h_c$. It gives a rational $u_0 \in \mathsf{U}$ with $h_c^{-1}h_cu^{-1}h_c^{-1}u_0h_c = u^{-1}(u_0)_{c,c} \in K(M)$. The lemma on level classes, with $g$ the element that defines $h_c$, gives $\chi(u_0) = \chi(u)$. $\square$

**Theorem (Rational points reach every unipotent reduction).** Let $S$ be admissible, let $c$ be a class and let $s \in \bar{G}$. Then $s$ lies in the reduced image of $\mathsf{U}(\mathbb{A}_f)$ if and only if some rational $\gamma \in \mathsf{U}$ is a term over $(c, s, c)$.

Lean: `New.Filling.mem_reducedImage_besselU_iff_exists_termsOver` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* Let $s = \bar{k}$ with $k \in K \cap \mathsf{U}(\mathbb{A}_f)$. The previous lemma gives a rational $\gamma \in \mathsf{U}$ with $k^{-1}\gamma_{c,c} \in K(M)$, and the lemma on terms with a given reduction makes $\gamma$ a term over $(c, s, c)$. Conversely, let $\gamma \in \mathsf{U}$ be a term over $(c, s, c)$. Then $\gamma_{c,c} = h_c^{-1}\gamma h_c$ lies in $K$ and in $\mathsf{U}(\mathbb{A}_f)$, since $h_c$ normalizes $\mathsf{U}$. Its reduction is $s$. $\square$

### The character at infinity

The archimedean Bessel functions transform under $\mathsf{U}$ by the character $\prod_v w(\sigma(\gamma_v))$, where $w(x) = \exp(x - \bar{x})$ and $\gamma_v$ is the rescaled image of $\gamma$ at $v$. This is the content of the definition of a Bessel system in [the chapter on Bessel functions at a real place](/chapter/bessel-real-place/). The next two results compare this character with $\chi$.

**Lemma (The character of a rational point).** For every rational $\gamma$, $\prod_v w(\sigma(\gamma_v)) = \overline{\chi(\gamma)}$, where $\chi(\gamma)$ means $\chi$ of the finite adelic image of $\gamma$.

Lean: `New.Filling.prod_wave_simpleRootSum_ratToInf` (New/Spanning/Unfolding/BesselLevelStructure.lean). Lean: `New.Filling.prod_wave_simpleRootSum_adelicToInf` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* Let $\psi$ be the standard character of $\mathbb{A}_E/E$. For an adelic point $x$ of $G$, put $\zeta_x = -(M\varpi)^{-1}\sigma(x) \in \mathbb{A}_E$. The finite factor of $\psi(\zeta_x)$ is $\psi_f(-\sigma(x_f)/(M\varpi)) = \chi(x_f)$. The archimedean factor is the product of the numbers $w(\sigma(x_v))$. This step uses the scales $\kappa_v^{\varrho - a}/\sqrt{N}$ of the frame vectors at $v$, with $\kappa_v = M\Phi_v(\varpi)/(2\pi i)$, and the fact that $\varpi$ is purely imaginary. So $$\prod_v w(\sigma(x_v)) = \psi(\zeta_x)/\chi(x_f).$$

Now let $x$ be the image of the rational $\gamma$. Then $\zeta_x$ is rational, so $\psi(\zeta_x) = 1$. Since $|\chi(\gamma)| = 1$, the quotient $1/\chi(\gamma)$ is $\overline{\chi(\gamma)}$. $\square$

**Theorem (The unipotent transformation law).** Let $\gamma \in \mathsf{U}$ be rational, let $k \in K \cap \mathsf{U}(\mathbb{A}_f)$, and let $\gamma$ be a term over $(c, \bar{k}, c)$. Then $\prod_v w(\sigma(\gamma_v)) = \overline{\chi(k)}$.

Lean: `New.Filling.prod_wave_eq_star_unipotentChar` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* By the previous lemma the left side is $\overline{\chi(\gamma)}$. The lemma on terms with a given reduction gives $k^{-1}h_c^{-1}\gamma h_c \in K(M)$. The lemma on level classes, with $u = k$, $v = \gamma$ and $h = h_c$, gives $\chi(\gamma) = \chi(k)$. $\square$

So inside one block of reduction $s$, the archimedean phase of a unipotent term depends only on $s$. If $s$ does not agree, two terms over the same block can carry different phases, and their contributions cancel in [the chapter on the moments](/chapter/moments/).

### Terms in the Bessel subgroup

**Lemma (Identity terms are unipotent).** Let $S$ be admissible, let $c, d$ be classes and let $\gamma \in R_0$ be rational. If $\gamma_{c,d} \in K(M)$, then $c = d$ and $\gamma \in \mathsf{U}_c(M)$.

Lean: `New.Filling.eq_and_mem_classUnipotent_of_besselS` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* Write $\gamma = u\eta$ with $u \in \mathsf{U}$ rational and $\eta \in H$ the image of a rational $\eta_0 \in U(X_0)(E)$ ([Lemma](/decl/New.exists_besselU_mul_toBesselH/)). Then

$$\gamma_{c,d} = u_{c,c} \cdot h_c^{-1}\eta h_d,$$

and $h_c^{-1}\eta h_d$ is the image of $g = c_0^{-1}\eta_0 d_0 \in U(X_0)(\mathbb{A}_f)$, where $c_0, d_0$ are the chosen representatives. The first factor is in $\mathsf{U}(\mathbb{A}_f)$ and the second in $H(\mathbb{A}_f)$. A product $u'h'$ with $u' \in \mathsf{U}$ and $h' \in H$ that is integral and $1$ modulo $M$ has $h'$ integral and $1$ modulo $M$, since each entry of $h'$ is an entry of $u'h'$ or of $1$. So the image of $g$ lies in $K(M)$. Admissibility says that the level $L$ is the preimage of $K(M)$, so $g \in L$. That is, $\eta_0 d_0 \in c_0L$, and $c$ and $d$ are the same double coset. So $c = d$, and then $d_0^{-1}\eta_0 d_0 \in L$. The level is free: $U(X_0)(E) \cap d_0Ld_0^{-1} = 1$. So $\eta_0 = 1$, and $\gamma = u \in \mathsf{U}$ with $\gamma_{c,c} \in K(M)$. $\square$

The converse direction finds terms in $R_0$ over each block whose reduction comes from $R_0$.

**Lemma (Terms in the Bessel subgroup exist).** Let $S$ be admissible, let $c$ be a class and let $s$ lie in the reduced image of $R_0(\mathbb{A}_f)$. Then there are a class $d$ and a rational $\gamma \in R_0$ that is a term over $(c, s, d)$.

Lean: `New.Filling.exists_besselS_mem_termsOver` (New/Spanning/Unfolding/BesselLevelStructure.lean).

*Proof.* Let $s = \bar{k}$ with $k \in K \cap R_0(\mathbb{A}_f)$. Write $h_ck = uh$ with $u \in \mathsf{U}(\mathbb{A}_f)$ and $h \in H(\mathbb{A}_f)$, and let $h$ be the image of $g \in U(X_0)(\mathbb{A}_f)$. Approximation gives a rational $x \in \mathsf{U}$ with $h^{-1}u^{-1}xh \in K(M)$. Write $g = \eta_0 d_0 a$ with $\eta_0 \in U(X_0)(E)$, $d$ a class with representative $d_0$ and $a \in L$. Put $\gamma = x\eta$, with $\eta$ the image of $\eta_0$. A computation gives

$$k^{-1}\gamma_{c,d} = (h^{-1}u^{-1}xh)\, a^{-1},$$

with $a$ read in $G(\mathbb{A}_f)$. Both factors lie in $K(M)$, the second by admissibility. So $\gamma$ is a term over $(c, s, d)$ by the lemma on terms with a given reduction. $\square$

### Terms with the same frame image

Two terms that move the frame in the same way differ by an element of $\mathsf{U}^0$. This is the fact that lets the count of the remaining terms work with frame images.

**Lemma (Equal frame images).** For isometries $s, s'$, the product $s^{-1}s'$ fixes every frame vector if and only if $s\mathfrak{f} = s'\mathfrak{f}$. An isometry that fixes every frame vector lies in $R_0$.

Lean: `New.Filling.frameImage_inv_mul_eq_iff` (New/Spanning/Unfolding/Terms.lean). Lean: `New.Filling.mem_besselS_of_frameImage_eq_one` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The first claim is $s^{-1}s'\mathfrak{f}_a = \mathfrak{f}_a \iff s'\mathfrak{f}_a = s\mathfrak{f}_a$. The second is the characterization of $R_0$ as the stabilizer of the frame ([Lemma](/decl/New.Filling.mem_besselS_iff_frameImage/)). $\square$

**Lemma (Reductions of terms with equal frame images).** Let $S$ be admissible. Let $\gamma$ be a term over $(c, r, c')$ and $u$ a term over $(c, r', d)$ with $\gamma\mathfrak{f} = u\mathfrak{f}$. Then $r^{-1}r'$ lies in the reduced image of $R_0(\mathbb{A}_f)$.

Lean: `New.Filling.termsOver.inv_mul_mem_reducedImage` (New/Spanning/Unfolding/Terms.lean).

*Proof.* Let $m = \gamma_{c,c'}$ and $m' = u_{c,d}$. Both lie in $K$. The frame image of $\gamma_{c,c'}$ is that of $\gamma$, written in the coordinates of $h_c\Lambda_0$ (the proof of [Lemma](/decl/New.Filling.frameGram_translateByClassReps/)). So $m\mathfrak{f} = m'\mathfrak{f}$. By the previous lemma $m^{-1}m' \in R_0$. It lies in $K$, and its reduction is $r^{-1}r'$. $\square$

**Lemma (Equal frame images over one reduction).** Let $S$ be admissible. Let $\gamma$ be a term over $(c, r, c')$ and $u$ a term over $(c, r, d)$, with $\gamma\mathfrak{f} = u\mathfrak{f}$. Then $c' = d$ and $\gamma^{-1}u \in \mathsf{U}^0_{c'}(M)$.

Lean: `New.Filling.termsOver.eq_and_mem_classUnipotent₀` (New/Spanning/Unfolding/Terms.lean).

*Proof.* The element $\gamma^{-1}u$ fixes the frame, so it lies in $R_0$. By the composition law it is a term over $(c', r^{-1}r, d) = (c', 1, d)$, so $(\gamma^{-1}u)_{c',d} \in K(M)$. The lemma on identity terms gives $c' = d$ and $\gamma^{-1}u \in \mathsf{U}_{c'}(M)$. It fixes the frame, so it lies in $\mathsf{U}^0$ too. $\square$

So the terms over $(c, r, \cdot)$ with a given frame image form one coset $\gamma\mathsf{U}^0_{c'}(M)$, and they all lie over one block.
