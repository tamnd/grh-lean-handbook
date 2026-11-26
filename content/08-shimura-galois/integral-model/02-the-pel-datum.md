---
title: The PEL datum of the source
lean:
  - Lib/Shimura/ThetaModuli/PELThetaTori.lean
  - Lib/Shimura/IntegralModel/PELDataExistence.lean
  - Lib/Shimura/HeckeTower/HeckeData.lean
  - Lib/Adelic/Adeles/Basic.lean
decls:
  - New.PEL
  - New.Variety.HasPadding
  - New.PEL.IsGoodAt
  - New.HasQuadSubfield
  - New.HasPrimitiveRoot5040
  - New.GaloisRep.IsSplitPrimeToDisc
  - New.Variety.IsSafe
  - New.Variety.exists_lagrangian
  - New.Variety.eventually_hasPadding
  - New.Variety.pel_good_of_safe
  - New.Variety.IsSafeGoodPEL
  - New.Variety.exists_pel
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The PEL datum of the source

A Shimura variety of PEL type is cut out by four pieces of linear algebra: a semisimple algebra $B$ with involution, a module $V$ over it, an alternating form on $V$, and a complex structure $h$. The letters stand for polarization, endomorphisms and level. The source needs only one case: $B = E$ is a CM field, $V = E^n$, and the form is a trace of a hermitian form. It packs this case, together with all the numerical data that its construction needs, into one structure. This section states the structure, explains each field, and proves that such data exist at every level divisible by a fixed integer $N$.

### The textbook datum

In Kottwitz (1992), §5, a PEL datum is $(B, {}^*, V, \langle\,,\rangle, h)$ with $B$ a simple $\mathbb{Q}$-algebra, ${}^*$ a positive involution, $V$ a $B$-module, $\langle\,,\rangle$ a non-degenerate alternating form with $\langle bx, y\rangle = \langle x, b^* y\rangle$, and $h : \mathbb{C} \to \operatorname{End}_B(V_{\mathbb{R}})$ a homomorphism with $\langle h(z)x, y\rangle = \langle x, h(\bar z)y\rangle$ and $\langle x, h(i)y\rangle$ symmetric and positive. Milne, *Introduction to Shimura varieties*, §8, gives the same definition. For an integral model one adds a lattice $\Lambda \subset V$ stable under an order of $B$, and a prime $p$ at which everything is unramified.

For $B = E$ a CM field with complex conjugation $c \mapsto \bar c$ and $V = E^n$, every such form has the shape $\langle x, y\rangle = \operatorname{tr}_{E/\mathbb{Q}}(\xi\, \bar y^{\mathsf T} x)$ with $\bar\xi = -\xi$. The group is the unitary similitude group of the hermitian form $\bar y^{\mathsf T} x$, twisted by $\xi$. Its signature at an infinite place $v$ is read from the signs of $\operatorname{Im}\Phi_v(\xi)$ and from $h$.

### The datum of the source

The source works with finite adeles. Write $\mathbb{A}_f = \mathbb{A}_{E,f}$ and $\hat{\mathcal{O}} = \hat{\mathcal{O}}_E$, and let $\mathcal{T}_n = (\mathbb{A}_f/\hat{\mathcal{O}})^n$. This is the torsion $\mathcal{O}_E$-module `AdelicTorsion E (Fin n)`, an adelic form of $(E/\mathcal{O}_E)^n$. Let $\psi_f$ be the standard additive character of $\mathbb{A}_f$, trivial on $\hat{\mathcal{O}}$ composed with the trace. For $\xi \in E$ and $x, y \in \mathbb{A}_f^n$ put $\langle x, y \rangle_\xi = \psi_f(\xi\, \bar y^{\mathsf T} x)$. Below, $\Phi_v$ is the embedding of the CM type at the infinite place $v$, and $v_0$ is the base place.

**Definition (PEL datum of the source).** A *PEL datum* $D$ for $E$ consists of the following data.

1. Integers $\beta, \mathfrak{N} \in \mathcal{O}_E$ (the fields `β` and `level`) with $\bar\beta = 1 - \beta$ and $\mathfrak{N} \neq 0$.
2. An element $\xi \in E$ and a rank $n \neq 0$, with $\operatorname{Re}\Phi_v(\xi) = 0$ and $\operatorname{Im}\Phi_v(\xi) > 0$ for every infinite place $v$.
3. A subgroup $T \subset \mathcal{T}_n$ (field `dualTorsion`) such that the class of $y$ lies in $T$ exactly when $\langle y, z\rangle_\xi = 1$ for every integral $z$. The order of $T$ is odd.
4. A subgroup $L \subset \mathcal{T}_n$ (field `lagrangian`) that is its own annihilator for $\langle\,,\rangle_\xi$ and contains every $s$ with $r s = 0$.
5. Natural numbers $r$ (field `paddedNorm`) with $r \geq 3$, and $i$ (field `exponentBound`), such that the degree condition `isCutDegree` holds for $(T, i, r)$, and every $y \in \mathcal{T}_n$ with $r^j y \in T$ for some $j \leq i$ is killed by $\mathfrak{N}$.
6. Paddings of $1$ and of $\beta$ to $r$ in the sense of the next definition.
7. $\Phi_v(\beta) = \Phi_{v_0}(\bar\beta)$ for every infinite place $v \neq v_0$, and $\Phi_{v_0}(\bar\beta) \neq \Phi_{v_0}(\beta)$.

Lean: `New.PEL` (Lib/Shimura/ThetaModuli/PELThetaTori.lean).

**Definition (Padding).** Let $r \geq 3$ and $c \in \mathcal{O}_E$. A *padding* of $c$ to $r$ is a family $a_1, \ldots, a_{r-3}$ in $\mathcal{O}_E$ that spans $\mathcal{O}_E$ over $\mathbb{Z}$ and satisfies $\bar c c + 3 + \sum_l \bar a_l a_l = r$.

Lean: `New.Variety.HasPadding` (Lib/Shimura/ThetaModuli/PELThetaTori.lean).

The fields have the following roles. The pair $(\xi, T)$ is the polarization: $T$ is the dual lattice of $\hat{\mathcal{O}}^n$ for the form, modulo $\hat{\mathcal{O}}^n$, so $|T|$ is the order of the kernel of the polarization. The subgroup $L$ is a maximal isotropic subgroup, as in Mumford's theory of theta structures. The theta functions of Section 3 are indexed by $T$. The number $r$ is the degree of the theta functions that the source uses as coordinates. Riemann's relation in degree $r$ needs a family of pairs $(a_l, b_l)$ with $\sum \bar a_l a_l = r$ and $\sum \bar a_l b_l = 0$, and the paddings give such families (Section 4). The bound $i$ says how many degrees $r^j$ must be read to determine the closure of Section 5. The last condition encodes the signature. In Section 3, $\beta$ acts on the tangent space of a fibre by $\Phi_{v_0}(\beta)$ on one line and by $\Phi_{v_0}(\bar\beta)$ on a complement of dimension `abelianDim` $- 1$. This is the determinant condition of Kottwitz (1992), §5, for the unitary group of signature $(1, n-1)$ at $v_0$, written with one element.

**Remark (Formalization).** The source's datum differs from the textbook datum in three ways. It fixes $B = E$ and $V = E^n$. It replaces the lattice by the adelic module $\hat{\mathcal{O}}^n$ and the torsion module $\mathcal{T}_n$, so all level structures are adelic. And it adds the numbers $r$, $i$ and the paddings, which have no meaning for the moduli problem; they serve the construction of Sections 4 and 5. The source has no comparison of `New.PEL` with Kottwitz's datum; this is question Q-66 of the findings of the plan. The argument needs no such comparison, since it uses the datum only through the theta tori of Section 3.

**Example.** Let $E \supset \mathbb{Q}(\sqrt{-3})$ and $\beta = (1 + \sqrt{-3})/2$, a primitive sixth root of unity. Then $\bar\beta = 1 - \beta$ and $\bar\beta\beta = 1$. If $\mathcal{O}_E = \mathbb{Z}[\beta]$ (so $E = \mathbb{Q}(\sqrt{-3})$, which has only one infinite place and is excluded later, but the arithmetic is the same), then $a = (1, \beta, 0)$ spans $\mathcal{O}_E$ and $\bar\beta\beta + 3 + (1 + 1 + 0) = 6$. So $1$ and $\beta$ both have paddings to $r = 6$. Each added term $1$ raises both the length $r - 3$ and the norm sum by $1$. So $1$ and $\beta$ have paddings to every $r \geq 6$.

### Good places

The datum must have good reduction at the places where the model is used. The source has its own notion.

**Definition (Good ideal).** The datum $D$ is *good* at an ideal $w$ of $\mathcal{O}_E$ when the following hold.

1. Neither $r$ nor $|T|$ lies in $w$.
2. There are a prime number $p \in w$ and an integer $b \in \mathbb{Z}$ with $\beta - b \in w$, such that $\beta - b$ and $\bar\beta - b$ are coprime.
3. $(\mathfrak{N}) + w \cdot (p, \bar\beta - b) = \mathcal{O}_E$.
4. Some finite place $v \neq w$ contains both $p$ and $\beta - b$.

Lean: `New.PEL.IsGoodAt` (Lib/Shimura/ThetaModuli/PELThetaTori.lean).

Condition 2 says that $w$ lies over a split prime of the quadratic field generated by $\beta$, in a strong form. Condition 4 gives a second place over the same split prime. Section 3 uses it: an element that generates a power of the second place is a unit at $w$ and expands the torus, and this gives good reduction. Condition 3 makes the level prime to $w$.

The places where the source builds its model are defined through the quadratic field. Fix $d_0$.

**Definition (Quadratic subfield).** The class `HasQuadSubfield d E` says that $d \equiv 3 \pmod 4$ and that $E$ is an algebra over $\mathbb{Q}(\sqrt{-d})$.

Lean: `New.HasQuadSubfield` (Lib/Shimura/HeckeTower/HeckeData.lean).

**Definition (Split and prime to the discriminant).** A finite place $u$ of $\mathbb{Q}(\sqrt{-d})$ is *split and prime to the discriminant* when some $b \in \mathbb{Z}$ gives $x = (1 + \sqrt{-d})/2 - b \in u$ with $x$ coprime to $\bar x$.

Lean: `New.GaloisRep.IsSplitPrimeToDisc` (Lib/Shimura/HeckeTower/HeckeData.lean).

By `New.GaloisRep.IsSplitPrimeToDisc.isSplit_and_prime_q` such a place is split, its residue field has prime order $q$, and $u$ and $\bar u$ are the only places that contain $q$.

**Definition (Safe place).** Let $\mathfrak{N} \in \mathcal{O}_E$. A finite place $w$ of $E$ is *safe* for $\mathfrak{N}$ when the place $u$ of $\mathbb{Q}(\sqrt{-d_0})$ below $w$ is split and prime to the discriminant, $\mathfrak{N} \notin w$, and $\mathfrak{N}$ lies in no place of $E$ above $\bar u$.

Lean: `New.Variety.IsSafe` (Lib/Shimura/HeckeTower/HeckeData.lean).

**Definition (Roots of unity of order 5040).** The class `HasPrimitiveRoot5040 E` says that the CM field $E$ contains a primitive root of unity of order $7! = 5040$.

Lean: `New.HasPrimitiveRoot5040` (Lib/Adelic/Adeles/Basic.lean).

The class gives an integer $\gamma$ with $\gamma^2 = -1$ and $\bar\gamma = -\gamma$, and an integer $\omega$ with $\omega + \bar\omega = 1$ and $\omega\bar\omega = 2$. The second comes from $\mathbb{Q}(\sqrt{-7}) \subset \mathbb{Q}(\zeta_7)$. The proof of existence below uses $\gamma$ to build $\xi$.

### Existence of the datum

The construction has two arithmetic inputs. The first is a Lagrangian through a given isotropic set.

**Lemma (Lagrangians).** Let $V$ be an abelian group, $G$ a commutative group, and $e : V \times V \to G$ a pairing that is multiplicative in each variable and alternating, $e(x, x) = 1$. Let $S \subset V$ be a set on which $e$ is trivial (in the form: any two elements $x, y$ of $S$ satisfy $e(x,y) = 1$ or $e(y,x) = 1$). Then there is a subgroup $\Lambda \supset S$ with $x \in \Lambda$ exactly when $e(x, y) = 1$ for all $y \in \Lambda$.

Lean: `New.Variety.exists_lagrangian` (Lib/Shimura/IntegralModel/PELDataExistence.lean).

*Proof.* By Zorn's lemma, take a maximal set $M \supset S$ on which $e$ is trivial in the given form. Let $x, y \in M$. Then $e(x, y) = 1$ or $e(y, x) = 1$. Expand $1 = e(x - y, x - y) = e(x,x)e(y,y)/(e(x,y)e(y,x))$. So $e(x,y) e(y,x) = 1$, and both are $1$. If $x$ pairs trivially with all of $M$, then $M \cup \{x\}$ is still a set of the given kind, so $x \in M$ by maximality. So $M$ is its own annihilator. An annihilator is closed under subtraction because $e$ is multiplicative. So $M$ is a subgroup. $\square$

The second input is the padding.

**Lemma (Paddings exist).** For every $c \in \mathcal{O}_E$, all large enough natural numbers $r$ admit a padding of $c$ to $r$.

Lean: `New.Variety.eventually_hasPadding` (Lib/Shimura/IntegralModel/PELDataExistence.lean).

*Proof.* Let $b_1, \ldots, b_d$ be a $\mathbb{Z}$-basis of $\mathcal{O}_E$, and let $v = (c, b_1, \ldots, b_d)$. Write $X = \sum_l (1 - \bar v_l v_l) = \sum_i n_i b_i$ with $n_i \in \mathbb{Z}$. Then $\bar X = X$. Consider the family $(c, b_1, \ldots, b_d, b_1 + n_1, \ldots, b_d + n_d)$. Its norm sum is
$$\bar c c + \sum_i \bar b_i b_i + \sum_i (\bar b_i + n_i)(b_i + n_i) = \bar c c + 2\sum_i \bar b_i b_i + (X + \bar X) + \sum_i n_i^2.$$
Since $X + \bar X = 2X = 2(1 + d) - 2\bar c c - 2\sum_i \bar b_i b_i$, the norm sum is $2(1 + d) - \bar c c + \sum_i n_i^2$. Add $\sum_i n_i^2 + 1$ zeros and $m$ ones, for any $m \geq 0$. The new family has $2 + 2d + \sum_i n_i^2 + m$ terms and spans $\mathcal{O}_E$, since it contains a basis. Put $r = 5 + 2d + \sum_i n_i^2 + m$. Then the family has $r - 3$ terms, and $\bar c c + 3 + (\text{norm sum}) = 2(1 + d) + 3 + \sum_i n_i^2 + m = r$. So every $r \geq 5 + 2d + \sum_i n_i^2$ admits a padding. $\square$

The next lemma reduces goodness to safety for the datum that the source builds.

**Lemma (Safe places are good).** Let $E$ have a base place, `HasQuadSubfield d E` and `HasPrimitiveRoot5040 E`. Let $D$ be a PEL datum with $\beta = (1 + \sqrt{-d})/2$. Let $w$ be safe for $D.\mathrm{level}$, with $r \notin w$ and $|T| \notin w$. Then $D$ is good at $w$.

Lean: `New.Variety.pel_good_of_safe` (Lib/Shimura/IntegralModel/PELDataExistence.lean).

*Proof.* Condition 1 is the hypothesis. Let $u$ be the place of $\mathbb{Q}(\sqrt{-d})$ below $w$. It is split and prime to the discriminant, so its norm $p$ is prime, and it contains $x = (1 + \sqrt{-d})/2 - b$ with $x$ coprime to $\bar x$. The images in $\mathcal{O}_E$ give condition 2, with $\beta - b \in w$. For condition 3, let $P$ be a prime that contains $\mathfrak{N}$ and $w \cdot (p, \bar\beta - b)$. Then $P \supseteq w$ or $P \supseteq (p, \bar\beta - b)$. In the first case $P = w$, but $\mathfrak{N} \notin w$. In the second case $P$ contains $p$, so it lies over $u$ or $\bar u$. If it lies over $u$, it contains $\beta - b$ and $\bar\beta - b$, which are coprime. If it lies over $\bar u$, it contains $\mathfrak{N}$, which lies in no place above $\bar u$. So no such $P$ exists. For condition 4, `New.GaloisRep.IsSplitPrimeToDisc.exists_place_above_ne` (Lib/GaloisRep/Main/QuadraticStep.lean) gives a place $v \neq w$ of $E$ above $u$. Its proof uses `HasPrimitiveRoot5040 E`. Then $v$ contains $p$ and $\beta - b$. $\square$

**Definition (Safe good datum).** For $d, n \in \mathbb{N}$ and $\mathfrak{N} \in \mathcal{O}_E$, a datum $D$ is *safe and good* for $(d, n, \mathfrak{N})$ when its rank is $n$, its level is $\mathfrak{N}$, $\beta$ is the image of $(1 + \sqrt{-d})/2$, and $D$ is good at every place that is safe for $\mathfrak{N}$.

Lean: `New.Variety.IsSafeGoodPEL` (Lib/Shimura/IntegralModel/PELDataExistence.lean).

**Theorem (Existence of PEL data).** Let $E$ be a CM number field with `HasQuadSubfield d E` and `HasPrimitiveRoot5040 E`. Let $n \neq 0$, let $\sigma : E \to \mathbb{C}$ be an embedding, and let $B$ be a finite set of finite places. Then there is a CM type $\Psi$ with a base place such that $\Psi_{v_0} = \sigma$, and $\Psi_v$ and $\Psi_{v_0}$ differ on $\mathbb{Q}(\sqrt{-d})$ for every $v \neq v_0$. There is also $N \in \mathbb{N}_{>0}$, in no place of $B$, such that for every nonzero $\mathfrak{N} \in \mathcal{O}_E$ with $N \mid \mathfrak{N}$ some PEL datum is safe and good for $(d, n, \mathfrak{N})$.

Lean: `New.Variety.exists_pel` (Lib/Shimura/IntegralModel/PELDataExistence.lean).

*Proof.* The CM type: at each $v \neq v_0$ take the embedding of $v$ or its conjugate, whichever differs from $\sigma$ on $\mathbb{Q}(\sqrt{-d})$. The two embeddings of the quadratic field are conjugate, so one of them works.

The datum. Take $r_0$ such that $1$ and $\beta$ have paddings to every $r \geq r_0$. Let $q_B$ be the largest norm of a place of $B$, and put $s = (r_0 + q_B + 2)!$ and $r = s + 1$. Choose $\xi$ purely imaginary, with $\operatorname{Im}\Phi_v(\xi) > 0$ at every $v$, in the inverse different, and with $m\xi = sc - 1$ for some $m$ in the different and some $c \in \mathcal{O}_E$. For this the source writes $\xi = a\gamma + s(z - \bar z)$, with $\gamma^2 = -1$ from `HasPrimitiveRoot5040`, $a$ a generator of the inverse different of $E^+$ at the primes of $s$, and $z$ an integer that makes the imaginary parts positive. Use the form $r^2 \xi$. The $r$-torsion is isotropic for it, and the lemma on Lagrangians gives $L$. Let $T$ be the dual of the integral vectors. The integer $(sc - 1) r^2$ kills $T$. So $|T|$ is prime to $s$. Since $2 \mid s$, $|T|$ is odd, and it is prime to the norm of each place of $B$, since these norms divide $s$. Choose $j$ by `New.Variety.ThetaNull.eventually_isCutDegree`, and put $N = r^{j+1} |T|$. Then $N$ lies in no place of $B$, because $r$ and $|T|$ are prime to $s$. If $N \mid \mathfrak{N}$ and $r^l t \in T$ with $l \leq j$, then $r^l |T|$ kills $t$, and it divides $\mathfrak{N}$. Finally goodness at safe places follows from the previous lemma, since $r$ and $|T|$ divide $N \mid \mathfrak{N}$, and $\mathfrak{N}$ is in no safe place. $\square$

**Remark (Formalization).** The integer $N$ and the datum are obtained by choice. The theorem says nothing about them beyond the stated properties. In particular $N$ depends on $B$, and the main proof applies it with $B = \{w_0, w'\}$, two places that the later steps need to keep (`New.GaloisRep.exists_rep_of_cuspidal_type`, line 716 of `Lib/GaloisRep/Main/SeedRepresentation.lean`). The degree bound $j$ comes from a statement of the form "for all large $j$", so no value of $j$ is computed.
