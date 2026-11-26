---
title: The sizes of later parts
lean:
  - New/Spanning/Unfolding/Setup.lean
  - New/Spanning/Frames/RealPlaceGauge.lean
  - New/Spanning/Frames/FiniteShells.lean
  - New/Spanning/Bessel/FillingData.lean
  - New/Spanning/Unfolding/FillingAdmissible.lean
  - New/Determinant/Twist/LongForms.lean
  - New/UpperBound/Objects/LabelsAndIndexTypes.lean
decls:
  - New.Filling
  - New.Filling.IsAdmissible
  - New.Floors.RealPlaceSizes
  - New.Data.realPlaceSizes
  - New.Data.N_le_pow
  - New.Data.mul_completion_cost_le
status: drafted
drafted_by: writer@claude-opus-5-5
---
## The sizes of later parts

Several later parts of the source do not work with the data $D$ directly. They work with a structure of their own, which lists the size conditions that the part needs. The data then build an instance of that structure, and each condition is proved from the table of Section 3. This section lists these structures, their size conditions, and how the data meet them. The two main ones are the filling data of the spanning theorem and the sizes at a real place.

### The shape of the data

The spanning theorem works with a shape $\mathfrak{s}$: a number $\varrho$ of hyperbolic planes, a rank $k$ of the positive summand $X_0$, and the rank $r$ of the whole space. Write $n = \varrho + 1$ (`Shape.n`, Lib/General/Groups/BesselGroups.lean:97). The shape of the data is `New.Data.shape` (UpperBound/Objects/LabelsAndIndexTypes.lean:258), with

$$\varrho = \frac{m}{2} - 1 \quad (\texttt{New.Data.ϱ}, \text{ line } 247), \qquad n = \frac{m}{2}, \qquad 2\varrho + 2 = m.$$

Its rank of $X_0$ is the rank $k$ of the data (`New.Data.card_X₀`, Spanning/Bessel/FillingData.lean:63), and its rank $r$ is the rank $r$ of the data (`New.Data.card_rowIndex`, LabelsAndIndexTypes.lean:275). So in the data, $n \approx \tfrac12\sqrt{x}$, $\varrho \approx \tfrac12\sqrt{x}$, and $k, r \approx x^5$. The identity $m = 2\varrho + 2$ is `New.Data.m_eq_two_mul_varrho_add_two` (UpperBound/Objects/Columns.lean:891).

### The filling data

**Definition (Filling data, size fields).** Filling data on a CM field $E$ with shape $\mathfrak{s}$ contain a real number $b$, primes $p_0, p_1, N$, and other objects. Write $f$ for the number of infinite places of $E$ and $\mathrm{rd}$ for its root discriminant. The size fields are:

1. $b^{10} \leq p_i \leq b^{11}$ for $i = 0, 1$;
2. $10^5 \leq \varrho$;
3. $2^{-\varrho} \leq b^{-6}$;
4. $(\varrho + 1)[E : \mathbb{Q}] \leq 2^{2\varrho}$;
5. $1000 (2\varrho + 2)^9 \leq k$ and $1000(2\varrho + 2) \leq k$;
6. $k \leq f$;
7. $(200 f k\, \mathrm{rd})^{1000} \leq b$;
8. $f \leq b/1000$, $k \leq b$, $\mathrm{rd} \leq b$, $\varrho + 1 \leq b$, $1000 \leq b$ and $1 \leq b$;
9. $b^{19} \leq p_0 p_1 \leq b^{23}$;
10. $5 \leq N$;
11. $10^{10} n^4 \leq n^6$, $3n^6 + 12 \leq n^7$ and $n^7 \leq k$.

Lean: `New.Filling` (New/Spanning/Unfolding/Setup.lean).

The structure is at Setup.lean:58. The size fields are at lines 92 to 146. Note that $b$ is a field of the structure, a real number, and not a scale of data. In the filling data of $D$ it is $D.b$.

**Definition (Admissible filling data, size fields).** Filling data are admissible if, besides two conditions on the level, the following hold at each infinite place $v$: $\lvert \varpi \rvert_v \leq b$ for the generator $\varpi$ of the different; $1 \leq \lvert \kappa_v \rvert \leq b^{23}$ for the real weight $\kappa_v$; $N \leq b^{60 n}$; $b^{11 k f} I \leq \mathcal{M} \leq (M/b^6)^{k f} I$ for the main and the identity second moments $\mathcal{M}$ and $I$; the number of Bessel coordinates is at most $b^{2 k f}$; and an index is at least $(N^k/b)^f$.

Lean: `New.Filling.IsAdmissible` (New/Spanning/Unfolding/Setup.lean).

The class is at Setup.lean:501. The instance for the data is at Spanning/Unfolding/FillingAdmissible.lean:743.

**Lemma (The data give filling data).** The filling data of $D$ (`New.Data.filling`, Spanning/Bessel/FillingData.lean:461) have $b = D.b$, the primes of $D$, and each size field holds.

*How the fields are proved.* Field 1 is the field `levelPrime_mem` of the data: `le_levelPrime i := (D.levelPrime_mem i).1`. Every other size field is proved by `D.le_of_hasLogBound` or `D.nat_le_of_hasLogBound`, with `D.card_X₀` to identify the rank. In terms of the table:

- Field 2: $\varrho = m/2 - 1$, and $\varrho \geq \tfrac12\sqrt{x} - 1$ is far above $10^5$.
- Field 3: $2^\varrho \geq b^{10}$ is an instance of FillingData.lean:448, from $\varrho \log 2 \geq 10 \log b$. Here $\varrho \approx \sqrt{x}/2$ and $\log b \leq x^{1/100}$ by (S2).
- Field 5: $(2\varrho + 2)^9 = m^9 \leq 2^9 x^{9/2}$, against $k \geq e^{-2} x^5$.
- Field 6: $k \leq e^3 x^5$, against $f \geq m^{22} \geq x^{11}$.
- Field 7: $f \leq x^{12}$, $k \leq e^3 x^5$ and $\mathrm{rd} \leq x^{12}$, so $200 f k\,\mathrm{rd} \leq 200 e^3 x^{29}$, and its $1000$-th power is about $x^{29000}$, against $b \geq x^{10^{12}}$.
- Field 9: $M \in [b^{20}, b^{22}]$, inside $[b^{19}, b^{23}]$.
- Field 11: $n^7 \approx 2^{-7} x^{7/2}$, against $k \geq e^{-2} x^5$.

$\square$

**Lemma (The level is not too large).** For the data $D$, $N \leq b^{60 n}$, where $n = \varrho + 1$ for the shape of $D$.

Lean: `New.Data.N_le_pow` (New/Spanning/Unfolding/FillingAdmissible.lean).

*Proof.* By `log_N_mem_Icc`, $\log N \leq 30 m \log b$. Since $m = 2\varrho + 2 = 2n$, this is $30 \cdot 2n \log b = 60 n \log b$. $\square$

The lemma is at FillingAdmissible.lean:725. This is the one condition of a later part that the data meet with no room at all: the bound $30 m \log b$ of Section 3 becomes $60 n \log b$ exactly. The constant $30$ comes from $24 m \log b$ for $\log N_-$, plus $\sqrt{\log b} \leq 6m\log b$ for the window (`New.Data.log_N_mem_Icc`, LevelAndTwists.lean:234). So the constant $60$ of the filling data and the constant $30$ of the data match.

### The sizes at a real place

**Definition (Sizes at a real place).** Let $\mathfrak{s}$ be a shape with $n = \varrho + 1$, let $\rho$ and $b$ be real numbers, and let $s$ be a natural number. The sizes at a real place hold if

1. $\rho = b^{6n + 2}$;
2. $8r \leq \rho$;
3. $k = s + 3n + 6$;
4. $10^9 n^3 < s$;
5. $n^7 \leq k$;
6. $10^8 \leq \varrho$;
7. $2 \leq b$.

Lean: `New.Floors.RealPlaceSizes` (New/Spanning/Frames/RealPlaceGauge.lean).

The structure is at RealPlaceGauge.lean:290. Here $\rho$ is a box radius, and $s$ is an exponent of the real place. It is not the exponent `towerExp` of the tower of the data. Field 3 defines it as $s = k - (3n + 6)$.

**Lemma (The data give the sizes at a real place).** For the data $D$, the sizes at a real place hold for the shape of $D$, the box radius $b^{6n+2}$, the exponent $k - (3n + 6)$ and the base $D.b$.

Lean: `New.Data.realPlaceSizes` (New/Spanning/Bessel/FillingData.lean).

*Proof.* The lemma is at FillingData.lean:260. Fields 1 and 3 hold by definition, given $k \geq 3n + 6$. Field 4 needs $10^9 n^3 + 3n + 6 < k$, and $10^9 n^3 \approx 10^9 x^{3/2}/8$ is small against $k \geq e^{-2} x^5$. Field 2 needs $8 r \leq b \leq b^{6n+2}$. Field 5 is as in the filling data. Field 6 needs $\varrho \geq 10^8$, which holds since $\varrho \geq \tfrac12\sqrt{x} - 1$ and $\log x \geq 6.4 \cdot 10^{15}$. $\square$

**Remark (Formalization).** The filling data ask $10^5 \leq \varrho$, and the sizes at a real place ask $10^8 \leq \varrho$. The two structures are independent, so the two constants need not agree. The data meet both, and much more: $\varrho \approx \sqrt{x}/2$. The research note d, §3, and its question 2 ask whether the concrete $\varrho$ reaches $10^8$, and how $k \leq f$ fits with $1000(2\varrho+2)^9 \leq k$. The answers are: $\varrho \approx \sqrt{x}/2$ is far above $10^8$; $k \approx x^5$ lies between $1000\, m^9 \approx 2^{9} \cdot 10^3 x^{9/2}$ and $f \geq x^{11}$.

### The local ranks of the finite shells

The file Spanning/Frames/FiniteShells.lean has, at line 59, the section variables

$$r + 10^8 n^4 \leq k, \qquad t + 10^{10} n^4 \leq k.$$

These $r$ and $t$ are not the ranks $r$ and $t = 5r$ of the data. They are local natural numbers of the section, exponents of the shells. The use in Spanning/MainTerm/FiniteSieveSystem.lean:123 takes the local $r$ equal to $k - n^7$, and the condition then follows from the field `pow_chain` of the filling data: $10^{10} n^4 \leq n^6 \leq n^7$, so $k - n^7 + 10^8 n^4 \leq k$. The research note d, §3, lists "$r + 10^8 n^4 \leq k$" next to the rank conditions. Read with $r$ the rank of the data, the condition would fail, since $r > k$. With the local $r$, it holds.

### Other size conditions in the spanning part

The file FillingData.lean proves three more size facts for the data:

- $3\kappa_0 + c_1 \leq b^2$, where $c_1 \leq a$ is a count of columns (`New.Data.liftWeight_add_columnCount_le`, line 283);
- $r + k + 3a \leq b^3$ (`New.Data.rank_add_le_cube`, line 291);
- $10^{30}\bigl((r + k)^2 \log b^3\bigr)^3 \leq r^7$ (`New.Data.rank_sq_mul_log_le`, line 299).

The last one compares a power of $x$ with a power of $\log b$. With $r + k \leq 2r$, it reads $10^{30} \cdot 64\, r^6 \cdot 27 (\log b)^3 \leq r^7$, that is $1.728 \cdot 10^{33} (\log b)^3 \leq r$. This holds since $r \geq x^5$ and $(\log b)^3 \leq x^{3/100}$. The docstring says that $r^7$ bounds from below the gaps of the Harish-Chandra parameters at the real places. So here the rank $r \approx x^5$ must be large against a power of $\log b$. This is one place where (S2) is used in the spanning part.

### Theorem C and the long forms

The lower bound for the covolume, Theorem C, completes the family of forms to a basis by auxiliary forms. Three size facts close its proof, all in Determinant/Twist/LongForms.lean:

- The auxiliary forms have squared length at most $\exp(2 x_1^2 b^2)$, and the proof uses $x^{99} + x^{202} b^2 \leq 2 x_1^2 b^2$ (line 97). This needs $x_1^2 \geq x^{202}$, which (S3) gives with a huge margin.
- The cost of completing the family: if $n \geq (1 - 4/b^2)\dim$ and $\dim = n + n'$, then $n'(2x_1^2 b^2 + b) \leq \dim \cdot b$ (`New.Data.mul_completion_cost_le`, line 120). The proof uses $4(2x_1^2 + 1/b) \leq b$. This needs $b \geq 8x_1^2 + 4/b$, which (S4) gives.
- The inverse ratios of Hecke values: there are at most $2m^2 t$ of them, each of height cost $x_1$, and the proof uses $2 m^2 t x_1 \leq b$ (line 231). Here $m^2 t \approx 20 x^6$, so this needs $b \geq 40 x^6 x_1$, which (S4) gives.

These are the places where $b$ must be large against $x_1$. Each needs only a fixed power of $x_1$ (at most $x_1^3$) below $b$. The exponent $10^6$ in (S4) is far more than these uses need. Section 7 gives the uses that need more.

### A summary of the later conditions

| Part | Condition | Met by |
|-------------|----------------|-------------|
| Filling | $10^5 \leq \varrho$ | $\varrho \approx \sqrt{x}/2$ |
| Filling | $1000\,m^9 \leq k \leq f$ | $m^9 \ll x^5$, $k \approx x^5$, $f \geq x^{11}$ |
| Filling | $b^{19} \leq M \leq b^{23}$ | $M \in [b^{20}, b^{22}]$ |
| Filling | $(200 f k\,\mathrm{rd})^{1000} \leq b$ | $x^{29000} \ll x_1 \leq b$ |
| Filling | $n^7 \leq k$ | $n^7 \approx x^{7/2}/128$ |
| IsAdmissible | $N \leq b^{60n}$ | $\log N \leq 30 m \log b$, $m = 2n$ |
| RealPlaceSizes | $10^8 \leq \varrho$, $10^9 n^3 < s$ | $\varrho \approx \sqrt{x}/2$, $s = k - 3n - 6$ |
| FiniteShells | $r + 10^8 n^4 \leq k$ | local $r = k - n^7$ |
| LongForms | $2 m^2 t x_1 \leq b$ | (S4) |
