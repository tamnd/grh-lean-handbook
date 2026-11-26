---
title: Amitsur and Cayley-Hamilton
lean:
  - Lib/General/LinearAlgebra/Eigenvalues.lean
  - New/Congruences/FirstOrder/RibetMethod.lean
decls:
  - New.exists_adjugate_of_charpoly_mem
  - New.amitsur_charpoly_mem_of_span
  - New.blockFlattenAlgEquiv
  - New.amitsur_charpoly_comp_coeff_mem_range
  - New.Selmer.exists_adjugate_polynomial
  - New.exists_family_algHom_charpoly_mem
  - New.Selmer.det_mem_of_coeff_mem
  - New.Selmer.exists_mul_eq_algebraMap_det
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Amitsur and Cayley-Hamilton

Ribet's method needs an inverse of a matrix up to a scalar, and it needs this scalar in a small ring. Over a commutative ring, the adjugate does this job. Here the matrix has entries in a noncommutative algebra $\Lambda$, a group algebra, and the representation $\rho$ of $\Lambda$ takes values in matrices over a larger ring $L$. The tool is the Cayley and Hamilton theorem, applied to $\rho(w)$ for each $w$. It works when the characteristic polynomial of $\rho(w)$ has its coefficients in the image of the small ring $R$. Amitsur's theorem says that it is enough to know this for a spanning set.

In this section, $R$ is a commutative ring, $L$ is a commutative $R$-algebra, $\Lambda$ is an $R$-algebra, $\sigma$ and $N$ are finite sets, and $\rho : \Lambda \to M_\sigma(L)$ is a map of $R$-algebras. "In the image of $R$" means in the range of $R \to L$.

### Two results from linear algebra

**Theorem (Adjugate from Cayley and Hamilton).** Suppose that the characteristic polynomial of every $\rho(w)$ has its coefficients in the image of $R$. Then for each $w \in \Lambda$ there are $F \in R$ and $v \in \Lambda$ with $\det \rho(w) = F$ and $\rho(v)\rho(w) = \rho(w)\rho(v) = F \cdot 1$.

Lean: `New.exists_adjugate_of_charpoly_mem` (Lib/General/LinearAlgebra/Eigenvalues.lean).

This is background from the linear algebra of [Weyl modules](/chapter/weyl-modules/) in Volume 5. The element $v$ is $(\operatorname{div}_X Q)(-w)$, where $Q$ over $R$ lifts the characteristic polynomial of $\rho(-w)$.

**Theorem (Amitsur).** Suppose that $\Lambda$ is spanned over $R$ by the elements $s$ such that the characteristic polynomial of $\rho(s)$ has its coefficients in the image of $R$. Then every $w \in \Lambda$ has this property.

Lean: `New.amitsur_charpoly_mem_of_span` (Lib/General/LinearAlgebra/Eigenvalues.lean).

This is also background from [Weyl modules](/chapter/weyl-modules/). It follows from Amitsur's formula for the characteristic polynomial of a sum of matrices (S. A. Amitsur, *On the characteristic polynomial of a sum of matrices*, Linear and Multilinear Algebra 8 (1980)). The proof in the source works with $\det(1 - t\rho(w))$ modulo a power of $t$.

### Block matrices

A square matrix $P$ over $\Lambda$, indexed by $N$, gives a block matrix with the blocks $\rho(P_{ij})$. The first lemma of the chapter says that Amitsur's property passes to these block matrices.

**Definition (Flattening of blocks).** The map $M_N(M_\sigma(L)) \to M_{N \times \sigma}(L)$ sends a matrix of blocks $(A_{ij})$ to the matrix with entry $(A_{ij})_{ab}$ at the place $((i, a), (j, b))$. It is an isomorphism of $R$-algebras.

Lean: `New.blockFlattenAlgEquiv` (New/Congruences/FirstOrder/RibetMethod.lean).

**Lemma (Amitsur for block matrices).** Suppose that the characteristic polynomial of every $\rho(w)$ has its coefficients in the image of $R$. Let $P$ be a square matrix over $\Lambda$, indexed by $N$. Then the characteristic polynomial of the block matrix with blocks $\rho(P_{ij})$ has its coefficients in the image of $R$.

Lean: `New.amitsur_charpoly_comp_coeff_mem_range` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Let $\varphi : M_N(\Lambda) \to M_{N \times \sigma}(L)$ apply $\rho$ to each entry and then flatten the blocks. It is a map of $R$-algebras. By Amitsur's theorem for $\varphi$, it is enough to show that $M_N(\Lambda)$ is spanned by matrices $E$ for which the characteristic polynomial of $\varphi(E)$ has its coefficients in the image of $R$.

Every matrix $Q$ is the sum over $q \in N$ of the matrix $E_q$ that has the row $q$ of $Q$ and zeros elsewhere. So the matrices with one nonzero row span $M_N(\Lambda)$. Fix $Q$ and $q$. Let $\mathrm{col}$ be the $(N \times \sigma) \times \sigma$ matrix that is the block column $q$ of the identity matrix. Let $\mathrm{row}$ be the $\sigma \times (N \times \sigma)$ matrix that is the block row $q$ of $\varphi(Q)$. Then $\varphi(E_q) = \mathrm{col} \cdot \mathrm{row}$, since the product has the block row $q$ of $\varphi(Q)$ in the block row $q$ and zeros elsewhere. In the other order, $\mathrm{row} \cdot \mathrm{col} = \rho(Q_{qq})$, the block of $\varphi(Q)$ at $(q, q)$.

For a $m \times n$ matrix $A$ and an $n \times m$ matrix $A'$, the characteristic polynomials satisfy $X^n \chi_{AA'} = X^m \chi_{A'A}$. Here this gives
$$X^{|\sigma|}\, \chi_{\varphi(E_q)} = X^{|N||\sigma|}\, \chi_{\rho(Q_{qq})} .$$
So each coefficient of $\chi_{\varphi(E_q)}$ is $0$ or a coefficient of $\chi_{\rho(Q_{qq})}$. These are in the image of $R$ by the hypothesis. $\square$

**Example.** Take $N = \{1, 2\}$, $\sigma$ one point, $\Lambda = L$ and $\rho$ the identity. For $E = \begin{pmatrix} a & b \\ 0 & 0 \end{pmatrix}$ we have $\mathrm{col} = \begin{pmatrix} 1 \\ 0 \end{pmatrix}$, $\mathrm{row} = (a, b)$ and $\mathrm{row} \cdot \mathrm{col} = a$. The characteristic polynomial of $E$ is $X(X - a)$, and indeed $X \cdot X(X - a) = X^2 (X - a)$.

### Cramer's rule over the polynomial ring

Ribet's method uses an adjugate of a matrix whose entries are polynomials in one variable over $\Lambda$. The variable will act by right multiplication with a fixed element $\rho_0$.

**Lemma (Adjugate over $\Lambda[X]$).** Suppose that the characteristic polynomial of every $\rho(w)$ has its coefficients in the image of $R$. Let $B$ be a square matrix over $\Lambda[X]$, indexed by $N$. Then there are a polynomial $P \in R[X]$ and a square matrix $B'$ over $\Lambda[X]$ such that:

1. $P(0)$ maps to the determinant of the block matrix with blocks $\rho(B_{ij}(0))$;
2. for all $i$, $j$ and $m$, $\rho$ of the coefficient of $X^m$ in $(B'B)_{ij}$ is $\rho$ of the coefficient of $X^m$ in the scalar matrix $P \cdot 1$.

Lean: `New.Selmer.exists_adjugate_polynomial` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Extend $\rho$ coefficient by coefficient to $\rho_X : \Lambda[X] \to M_\sigma(L[X])$, so that the coefficient of $X^m$ in the entry $(a, b)$ of $\rho_X(p)$ is $\rho(p_m)_{ab}$. This is a map of $R[X]$-algebras. On a constant $C(w)$ it gives $\rho(w)$ with entries read as constants, so its characteristic polynomial is that of $\rho(w)$, with coefficients in the image of $R$, hence of $R[X]$. A polynomial $p$ is the sum of the monomials $X^i \cdot C(p_i)$, so the constants span $\Lambda[X]$ over $R[X]$. Amitsur's theorem for $\rho_X$ now says that all characteristic polynomials of $\rho_X$ have their coefficients in the image of $R[X]$.

Let $\varphi_X$ apply $\rho_X$ to the entries of a matrix over $\Lambda[X]$ and flatten the blocks. By Amitsur for block matrices, $\varphi_X$ has the hypothesis of the adjugate theorem over $R[X]$. That theorem gives $B'$ and $P \in R[X]$ with $\det \varphi_X(B) = P$ and $\varphi_X(B')\varphi_X(B) = P \cdot 1$. Since $\varphi_X$ is multiplicative, $\varphi_X(B'B) = \varphi_X(P \cdot 1)$. Reading the blocks of both sides entry by entry and coefficient by coefficient gives the second claim.

For the first claim, apply the constant coefficient $L[X] \to L$ to $\det \varphi_X(B) = P$. The constant coefficient is a ring map, so it commutes with the determinant. It sends $\varphi_X(B)$ to the block matrix with blocks $\rho(B_{ij}(0))$, and it sends $P$ to $P(0)$. $\square$

**Remark (Formalization).** The identity $B'B = P \cdot 1$ is not claimed in $\Lambda[X]$. It is claimed only after $\rho$ is applied to every coefficient of every entry, since $\rho$ need not be injective. The next section uses it only in a quotient of $\Lambda$ by an ideal that contains the kernel of $\rho$, where the two forms agree.

### Families of representations

In the application, $\Lambda$ is a group algebra and there is not one representation but a finite family $u_x$, $x \in Y$, with values in $M_\sigma(O)$. The family becomes one representation over the ring $Y \to L$ of functions on $Y$. Its characteristic polynomials then have coefficients that are functions of $x$.

Let $O$ be a commutative ring with $O \to L$, let $S$ be an $R$-subalgebra of the functions $Y \to L$, and let $\kappa : O \to S$ send $c$ to the constant function with value $c$. Let $u_x : O[G] \to M_\sigma(O)$ be maps of $O$-algebras.

**Lemma (One representation for the family).** Suppose that for each $g \in G$ and each $k$, the function $x \mapsto$ (coefficient of $X^k$ in the characteristic polynomial of $u_x(g)$) lies in $S$. Then there is a map of $S$-algebras $\rho : S[G] \to M_\sigma(Y \to L)$ such that:

1. on an element $r$ of $O[G]$, carried to $S[G]$ along $\kappa$, the matrix $\rho(r)$ at the point $x$ is $u_x(r)$;
2. the characteristic polynomial of every $\rho(a)$, $a \in S[G]$, has its coefficients in $S$.

Lean: `New.exists_family_algHom_charpoly_mem` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Let $\rho$ send $g$ to the matrix of functions $x \mapsto u_x(g)$, and extend it $S$-linearly. Claim 1 holds on group elements by definition. It passes to sums, and it passes to $c \cdot r$ because $\kappa(c)$ is the constant $c$. For claim 2, the group elements span $S[G]$ over $S$. Evaluation at $x$ is a ring map $(Y \to L) \to L$, and it commutes with the characteristic polynomial. So the coefficient of $X^k$ in $\chi_{\rho(g)}$, at $x$, is that of $\chi_{u_x(g)}$. By the hypothesis it lies in $S$. Amitsur's theorem then gives claim 2 for all $a$. $\square$

**Lemma (Determinants of a family).** Under the hypothesis of the last lemma, for each $w \in O[G]$ the function $x \mapsto \det u_x(w)$ lies in $S$.

Lean: `New.Selmer.det_mem_of_coeff_mem` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* Take $\rho$ from the last lemma. The function $x \mapsto \det u_x(w)$ is $\det \rho(w)$, read through $\kappa$. The adjugate theorem for $\rho$ over $S$ gives $D \in S$ with $\det \rho(w) = D$. $\square$

**Lemma (Cayley and Hamilton for a family).** Let $\rho$ be as in the conclusion of the lemma on one representation for the family. For each $w \in O[G]$ there are $D \in S$, equal to the function $x \mapsto \det u_x(w)$, and $v \in S[G]$ with $\rho(v \cdot \kappa(w)) = D \cdot 1$.

Lean: `New.Selmer.exists_mul_eq_algebraMap_det` (New/Congruences/FirstOrder/RibetMethod.lean).

*Proof.* The adjugate theorem for $\rho$ and $\kappa(w)$ gives $v$ and $D$ with $\det \rho(\kappa w) = D$ and $\rho(v)\rho(\kappa w) = D \cdot 1$. At the point $x$, $\det \rho(\kappa w)$ is $\det u_x(w)$ by claim 1. Since $\rho$ is multiplicative, $\rho(v \cdot \kappa w) = D \cdot 1$. $\square$

The last lemma is the step where a determinant becomes an element of a left ideal. If $w$ lies in a left ideal $I$, then $v \cdot \kappa(w)$ lies in the left ideal generated by the image of $I$, and $\rho$ sends it to the scalar $D$. The next section uses this to put $D$ times the Ribet element into $\mathcal{J}$.
