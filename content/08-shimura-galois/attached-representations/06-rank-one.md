---
title: Rank one
lean:
  - Lib/GaloisRep/Main/AttachedRepresentations.lean
  - Lib/ClassField/Local/ArtinMap.lean
  - Lib/PadicHodge/Characters.lean
decls:
  - New.AlgHeckeChar
  - New.AlgHeckeChar.avatar
  - New.AlgHeckeChar.avatar_apply_of_artinMap_eq
  - New.exists_character_of_eigenvalues
  - New.continuous_scalarFin_divStar
  - New.scalarFin_divStar_locIdele
  - New.apply_mul_scalarFin_divStar_principalIdele
  - New.HasHeckePolyAt.rightRegular_ofSplitPlace_scalar
  - New.IsRankOneCharacter
  - New.GaloisRep.Attached.exists_det_eq_avatar
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Rank one

In rank one every notion of this chapter can be computed. A form on $U(1)$ gives a character of the finite ideles, the character is an algebraic Hecke character, and an attached representation is its $\ell$-adic avatar. This section proves this. It is the model case of Section 1.

Let $E$ be a CM field with CM type $\Phi$, and let $\mathbb{A}_f$ be the finite adeles of $E$. For $x \in \mathbb{A}_f^\times$ let $x/\bar x$ be the quotient by the complex conjugate; it has norm one, so it is a scalar matrix in $U(1)(\mathbb{A}_f)$ (Lean `New.scalarFin (Fin 1) (New.divStar x)`). Write $\iota_\ell : \mathbb{C} \to \bar{\mathbb{Q}}_\ell$ as before, and $\mathrm{Art}$ for the Artin map of [class field theory](/chapter/class-field-theory/).

### Algebraic Hecke characters and avatars

**Definition (Algebraic Hecke character).** An *algebraic Hecke character* of a number field $K$ is a pair $(\theta, n)$ of a character $\theta : \mathbb{A}_{K,f}^\times \to \mathbb{C}^\times$ with open kernel and a function $n$ from the embeddings $K \to \mathbb{C}$ to $\mathbb{Z}$, such that for all $x \in K^\times$
$$\theta(x) = \prod_{\sigma} \sigma(x)^{-n_\sigma}.$$
They form a group under pointwise multiplication.

Lean: `New.AlgHeckeChar` (Lib/ClassField/Local/ArtinMap.lean).

The character $\theta$ is a character of the finite ideles only. The classical Hecke character is $\theta$ times the algebraic character $\prod_\sigma \sigma^{n_\sigma}$ at infinity, which is then trivial on $K^\times$; this is the usual notion of a Hecke character of type $A_0$.

**Definition (Avatar).** Let $K$ be totally complex. The *$\ell$-adic avatar* of $(\theta, n)$ is a continuous character $\mu : \mathrm{Gal}(\Omega/K) \to \bar{\mathbb{Q}}_\ell^\times$ such that, if $\mathrm{Art}(x)$ is the class of $g$,
$$\mu(g) = \iota_\ell(\theta(x)) \prod_\sigma (\iota_\ell \sigma)(x)^{n_\sigma},$$
where $(\iota_\ell\sigma)(x)$ is the image under $\iota_\ell \circ \sigma$ of the component of $x$ at the place above $\ell$ that $\iota_\ell \circ \sigma$ induces. The map $(\theta, n) \mapsto \mu$ is a homomorphism.

Lean: `New.AlgHeckeChar.avatar`, `New.AlgHeckeChar.avatar_apply_of_artinMap_eq` (Lib/PadicHodge/Characters.lean).

**Remark (Formalization).** `New.AlgHeckeChar.avatar` is `(exists_avatar).choose`, a choose object. The right side of the formula is a continuous character of the finite ideles that is trivial on $K^\times$, so it factors through the Artin map; the Artin map is onto, so the avatar is determined by the formula. The choice has no other effect. The formula is the lemma `avatar_apply_of_artinMap_eq`, and continuity is `New.AlgHeckeChar.continuous_avatar`.

### From a form to a character

**Lemma.** Let $\pi$ be a representation of a commutative group $A$ on a complex vector space, and let $f \neq 0$. There is a character $\chi : A \to \mathbb{C}^\times$ such that $\chi(x) = c$ whenever $\pi(x) f = c f$.

Lean: `New.exists_character_of_eigenvalues` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* The pairs $(x, c)$ with $\pi(x) f = cf$ form a subgroup $H$ of $A \times \mathbb{C}^\times$, and $c$ is determined by $x$ since $f \neq 0$. So the second projection is a character of the image of $H$ in $A$. The group $\mathbb{C}^\times$ is divisible, so the character extends to $A$. $\square$

**Lemma.** Let $w$ be a split place and $f$ a form on $U(1)$ whose weight is the power $\kappa$ of the determinant.

1. The map $x \mapsto x/\bar x$ from $\mathbb{A}_f^\times$ to $U(1)(\mathbb{A}_f)$ is continuous.
2. For $x \in E_w^\times$, the idele with component $x$ at $w$ and $1$ elsewhere goes to the scalar $x$ embedded at $w$.
3. For $x \in E^\times$, right translation by $x/\bar x$ multiplies $f$ by $\prod_v \bigl(\overline{\Phi_v(x)}/\Phi_v(x)\bigr)^{\kappa_v}$, the product over infinite places.
4. If $f$ has Hecke polynomial $Q$ at $w$, then right translation by a uniformizer $\varpi$ of $E_w$, embedded at $w$, multiplies $f$ by $-Q(0)$.

Lean: `New.continuous_scalarFin_divStar`, `New.scalarFin_divStar_locIdele`, `New.apply_mul_scalarFin_divStar_principalIdele`, `New.HasHeckePolyAt.rightRegular_ofSplitPlace_scalar` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* Parts 1 and 2 are computations with scalar matrices and the definition of the embedding at $w$. For part 3, $x/\bar x$ is a global element $\gamma$ of $U(1)$, and it is central, so $f(g\gamma) = f(\gamma g) = \kappa(\gamma) f(g)$ by the automorphy of $f$. The weight $\kappa$ acts on $\gamma$ through $\Phi_v(\gamma)^{\kappa_v}$ at each $v$. For part 4, $T_{\bar w, 0}$ is the identity on $f$, since $f$ is spherical at $\bar w$ too. By the duality of [Iwahori and Satake](/chapter/iwahori-satake/), $\pi(\varpi) T_{\bar w,0} f = T_{w,1} f = t_1 f$. In rank one $Q = X - t_1$, so $t_1 = -Q(0)$. $\square$

**Definition (Character of a rank-one form).** An algebraic Hecke character $(\theta, n)$ *matches* $f$ of weight $\kappa$ if:

1. $n_\sigma = \kappa_v$ when $\sigma = \Phi_v$, and $n_\sigma = -\kappa_v$ otherwise, where $v$ is the place of $\sigma$;
2. at a split place $w$, if right translation by $x \in E_w^\times$ embedded at $w$ multiplies $f$ by $c$, then $\theta$ at the idele $x$ at $w$ is $c$;
3. at a split place $w$ where $f$ has Hecke polynomial $Q$, $\theta(\varpi) = -Q(0)$ for every uniformizer $\varpi$.

Lean: `New.IsRankOneCharacter` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

### The determinant is an avatar

**Theorem.** Let $f$ be an eigenform on $U(1)$ for $P$, of weight the power $\kappa$ of the determinant, and let $r : \Gamma_E \to \mathrm{GL}_1(\bar{\mathbb{Q}}_\ell)$ be attached to $P$. Then there is an algebraic Hecke character $\theta$ that matches $f$, and $\det r(g) = \mu_\theta(g)$ for all $g$, where $\mu_\theta$ is its avatar.

Lean: `New.GaloisRep.Attached.exists_det_eq_avatar` (Lib/GaloisRep/Main/AttachedRepresentations.lean).

*Proof.* Let $z(x) = x/\bar x$. By the first lemma, applied to $A = \mathbb{A}_f^\times$ acting through $z$, there is a character $\chi$ with $\chi(x) = c$ whenever $z(x)$ multiplies $f$ by $c$. The stabilizer of $f$ is open, so by part 1 its inverse image under $z$ is open, and it lies in the kernel of $\chi$; so $\chi$ has open kernel. Let $n$ be as in condition 1. By part 3, for $x \in E^\times$, $\chi(x) = \prod_v (\overline{\Phi_v(x)}/\Phi_v(x))^{\kappa_v} = \prod_\sigma \sigma(x)^{-n_\sigma}$. So $\theta = (\chi, n)$ is an algebraic Hecke character. Condition 2 follows from part 2, and condition 3 from part 4.

For the determinant, use most Frobenius data $(w, A, s)$. For almost all $w$ of prime norm, $w$ is split, $f$ has Hecke polynomial $P_w$, $w$ is prime to $\ell$ and unramified for $\theta$. Then $\mu_\theta(s) = \iota_\ell(\theta(\varpi_w)) = -\iota_\ell(P_w(0))$ for the geometric Frobenius $s$, by condition 3 and the local formula for the avatar (Lean `New.AlgHeckeChar.eventually_avatar_frob`). Now let $g \in \Gamma_E$. Along $\mathcal{F}_E(g)$, $\mu_\theta(s) \to \mu_\theta(g)$ since $\mu_\theta$ is continuous, and $-\iota_\ell(P_w(0))$ tends to $-(\text{constant coefficient of } X - r(g)) = r(g)$ by Section 4. The filter is not trivial, so $\mu_\theta(g) = \det r(g)$. $\square$

**Remark (Formalization).** The theorem does not say that $\theta$ is unique, and it does not state the local-global compatibility of $r$. The source proves local compatibility for avatars separately (Lean `New.GaloisRep.avatarCompatAt_of_hasPrimitiveRoot5040`, in `Lib/ClassField/Avatar/LocalGlobalCompatibility.lean`). The weight is the pair $(0, \kappa)$: no Young diagram, only a power of the determinant. The theorem also exhibits the junk values of Section 2: $P_w$ at inert places plays no part, since condition 3 is only at split places.

**Example.** Let $\kappa = 0$ and let $f$ be a character of the finite group $U(1)(E) \backslash U(1)(\mathbb{A}_f) / U$ for an open compact $U$. Then $f$ is a form of weight $0$. The character $\theta$ is trivial on $E^\times$ and on an open subgroup, so it is a character of finite order of the idele class group, and $n = 0$. Its avatar satisfies $\mu(\mathrm{Art}(x)) = \iota_\ell(\theta(x))$, so it is a character of finite order of $\Gamma_E$, since $\theta$ factors through the finite group $\mathbb{A}_f^\times / E^\times U'$ for an open compact $U'$ in its kernel. So the representation attached to a weight-$0$ form on $U(1)$ is a character of finite order, as in the classical case.
