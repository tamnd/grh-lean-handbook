---
title: Class counts at the data
lean:
  - New/UpperBound/Size/Estimates.lean
decls:
  - New.Data.card_stdClasses_le_exp_mul_log
  - New.Data.card_stdClasses_le_exp
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Class counts at the data

The levels of the chain are not the standard level $K_0$. They are smaller groups that contain a principal congruence subgroup. This section bounds the number of classes for such a level, first for a general level $G$ and then for the level $\pi_M\pi_N$ of the data. The result is the bound $\exp(x^{30})$, which Section 7 uses at each of the $m$ stages of the chain and Section 8 uses once on $Y_m$.

### Principal levels

For a nonzero integer $\alpha$ of $E$, the principal level $K(\alpha)$ is the set of $g \in K_0$ with $g \equiv 1$ modulo $\alpha\hat{\mathcal O}$, entry by entry ([adeles and hermitian spaces](/chapter/adeles-hermitian-spaces/); Lean: `New.principalLevel`). If $\alpha \mid \beta$, then $K(\beta) \subseteq K(\alpha)$ (`New.principalLevel_le_of_dvd`). Two facts from Volume 4 are used.

- *Index.* $[K_0 : K(\alpha)] \le \mathrm N(\alpha)^{r^2}$, where $r = \#n$ and $\mathrm N(\alpha)$ is the absolute norm of the ideal $(\alpha)$. The group $K(\alpha)$ is the kernel of the reduction $K_0 \to \mathrm{GL}_n(\hat{\mathcal O}/\alpha\hat{\mathcal O})$, and the ring $\hat{\mathcal O}/\alpha\hat{\mathcal O}$ has $\mathrm N(\alpha)$ elements (`New.relIndex_principalLevel_le`).
- *Classes of a smaller level.* For subgroups $K$, $K'$ of $G_f$, every class of $\Gamma\backslash G_f/K'$ is the class of $xq$, with $x$ a representative of a class of $\Gamma\backslash G_f/K$ and $q$ a representative of a coset of $K/(K\cap K')$ (`New.surjective_doubleCoset_mk_mul`).

For the second fact, here is the short proof. Let $g \in G_f$. The representative of the $K$-class of $g$ is $\gamma g k$ with $\gamma \in \Gamma$ and $k \in K$. The representative of the coset of $k^{-1}$ in $K/(K\cap K')$ is $k^{-1}l$ with $l \in K\cap K'$. The product is $\gamma g kk^{-1}l = \gamma g l$, which lies in the $K'$-class of $g$.

So, with $K = K_0$ and $K'$ any subgroup of finite index in $K_0$ modulo $K'$,
$$\#\bigl(\Gamma\backslash G_f/K'\bigr) \le \#\bigl(\Gamma\backslash G_f/K_0\bigr)\cdot[K_0 : K_0\cap K'] .$$

### A general level

**Proposition (Classes of a level that contains a principal level).** Let $D$ be data, $G \ge 1$ an integer, and $n$ an index set with $\#n \le 2n_m$. Let $K$ be a subgroup of $G_f$ that contains the principal level $K(G)$. Then
$$\#\bigl(\Gamma\backslash G_f/K\bigr) \le \exp\bigl(x^{29}(1 + \log G)\bigr).$$

Lean: `New.Data.card_stdClasses_le_exp_mul_log` (New/UpperBound/Size/Estimates.lean).

*Proof.* Put $f$ for the number of infinite places of $E$ and $R = 2n_m$, so $\#n \le R$.

*The index.* As $K(G) \subseteq K\cap K_0$,
$$[K_0 : K\cap K_0] \le [K_0 : K(G)] \le \mathrm N(G)^{(\#n)^2}.$$
The field $E$ has degree $2f$ over $\mathbb Q$, so $\mathrm N(G) = G^{2f}$. With $G \ge 1$ and $\#n \le R$ the index is at most $G^{2fR^2}$. In particular it is finite.

*The standard classes.* The number $q_1 d$ lies in the different of $E$ ([CM fields](/chapter/cm-fields/); Lean: `New.Parameters.conductor_mem_differentIdeal`). The theorem on the class count of Section 2, with $N = q_1d$, gives
$$\#\bigl(\Gamma\backslash G_f/K_0\bigr) \le \bigl(1 + 2(6q_1d(f\#n)^2)^3\bigr)^{4f(\#n)^2} \le C^{4fR^2}, \qquad C = 1 + 2\bigl(6q_1d(fR)^2\bigr)^3 .$$

*The product.* By the fact on classes of a smaller level,
$$\#\bigl(\Gamma\backslash G_f/K\bigr) \le C^{4fR^2}\,G^{2fR^2} = \exp\bigl(4fR^2\log C + 2fR^2\log G\bigr).$$

*The sizes.* The table of sizes gives $f \le q_1 \le x^{12}$, $d \le C_P \le \log\log b \le x^{1/100}$ and $R \le 2e^{12}x^{11/2}$. So $fR^2 \le 4e^{24}x^{23}$ and $(fR)^2 \le 4e^{24}x^{35}$, and
$$\log C \le \log 3 + 3\log\bigl(6q_1d(fR)^2\bigr) \le \log 3 + 3\log\bigl(6\cdot x^{12}\cdot x^{1/100}\cdot 4e^{24}x^{35}\bigr) \le 150\log x .$$
Hence $4fR^2\log C \le 16e^{24}x^{23}\cdot 150\log x \le x^{29}$ and $2fR^2 \le x^{29}$, as $x$ is far larger than $e^{100}$. The exponent is at most $x^{29} + x^{29}\log G$. $\square$

**Remark (Formalization).** The source proves the two size bounds of the last step with the automation `le_of_hasLogBound` of [the data and their sizes](/chapter/data-and-sizes/#the-table-of-sizes). The index $[K_0 : K\cap K_0]$ is `Subgroup.relIndex`, which is $0$ for an infinite index. The proof first shows that the index of $K(G)$ is not $0$, so the finite index instance holds and no junk value enters. The hypothesis $G \ge 1$ is the instance `NeZero G`; for $G = 0$ the group $K(0)$ is trivial and the index is infinite.

### The level of the data

The levels of the chain contain the principal level of $\pi_M\pi_N$. Here $\pi_M$ and $\pi_N$ are integers of $E$ with $\pi_M\bar\pi_M = M$ and $\pi_N\bar\pi_N = N$ ([the objects of the upper bound](/chapter/upper-bound-objects/)).

**Corollary (Classes at the data).** Let $n$ be an index set with $\#n \le n_m$, and let $K$ be a subgroup of $G_f$ that contains $K(\pi_M\pi_N)$. Then
$$\#\bigl(\Gamma\backslash G_f/K\bigr) \le \exp(x^{30}).$$

Lean: `New.Data.card_stdClasses_le_exp` (New/UpperBound/Size/Estimates.lean).

*Proof.* The integer $\pi_M\pi_N$ divides $\pi_M\bar\pi_M\pi_N\bar\pi_N = MN$. So $K(MN) \subseteq K(\pi_M\pi_N) \subseteq K$. The proposition with $G = MN$ and $\#n \le n_m \le 2n_m$ gives the bound $\exp(x^{29}(1 + \log MN))$. By the table of sizes, $\log M \le 22\log b$ and $\log N \le 30m\log b \le 60\sqrt x\log b$. With $\log b \le x^{1/100}$ this gives $1 + \log MN \le 1 + 22x^{1/100} + 60x^{1/2 + 1/100} \le x$. So the exponent is at most $x^{30}$. $\square$

### Where the corollary is used

The two results are used in three kinds of places.

1. In Section 7, at each stage $j < m$ of the chain. The level $K_j$ of $X_j$ contains $K(\pi_M\pi_N)$ (`New.Data.principalLevel_le_levelX`), and $\#X_j = n_j \le n_m$. So the tuples of classes number at most $\exp(x^{30})^m = \exp(mx^{30})$.
2. In Section 8, for the level of the forms on $Y_m$, since $\#Y_m \le n_m$ (`New.Data.card_Y_le`).
3. In other parts of the source: the comparison operator and the Hecke values of the one lift, the auxiliary forms of the determinant, and the existence of fit twists. In each place a sum over classes is bounded by the number of classes times its largest term.

The bound $\exp(x^{30})$ is very weak. It is still enough, because every use compares it with quantities of size at least $fa \ge x^{11}\cdot x^{999}x_1$. On the logarithmic scale, the class count costs $x^{30}$ at each stage, while the main terms of the exponent are of order $fa\log b$.

### An example of the index bound

Take $E = \mathbb Q(i)$, $n$ with one element and $G = 3$. Then $f = 1$ and $\mathrm N(3) = 9$, since $3$ is inert in $\mathbb Z[i]$. The bound says $[K_0 : K(3)] \le 9$. The true index is the number of elements of norm one in $(\mathbb Z[i]/3)^\times = \mathbb F_9^\times$ that come from $K_0$. The norm one elements of $\mathbb F_9^\times$ are the $u$ with $u^{4} = 1$, since the conjugation of $\mathbb F_9$ is $u \mapsto u^3$ and $u\cdot u^3 = 1$. There are $4$ of them, and the index is at most $4 \le 9$. The bound counts all of $\mathbb F_9$, and it loses only the factor $9/4$.

For $G = 5 = (2 + i)(2 - i)$ the norm is $25$. The reduction modulo $5$ sends the norm one units at the two places above $5$ to pairs $(u, u^{-1})$, so the image has at most $4$ elements, while the bound gives $25$.
