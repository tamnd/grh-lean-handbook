---
title: Exercises
lean:
  - New/Spanning/Frames/Depth.lean
  - New/Spanning/Frames/Gains.lean
  - New/Spanning/Frames/OneFrame.lean
  - New/Spanning/Frames/Shells.lean
decls: []
status: drafted
drafted_by: writer@claude-opus-5-5
---
## Exercises

**Exercise 1.** Let $r_a = k + 1 + 2(\varrho - a - 1)$ and $d_a = r_a$. Check the exponents in [Lemma](/decl/New.Floors.PlaceData.headDensity_sq_mul_eq_modulus/): the head density squared gives $|p_aq_a|^{r_a}$, the squared floor modulus gives $|p_a|^{-(2r_a+1)}$, and the modulus of the twist gives $|p_a/q_a|^{r_a+1}$. Show that the product over $a < j$ is $|q_0\cdots q_{j-1}|^{-1}$. Why does this mean that the theorem on one shell needs only $q$ to be a head?

*Hint.* The exponent of $|p_a|$ is $r_a - 2r_a - 1 + r_a + 1 = 0$, and that of $|q_a|$ is $r_a - r_a - 1 = -1$. A head $q$ has $(q_0\cdots q_{l-1})^{-1}$ of size $1$, and a number of size $1$ has modulus at most $\Lambda$.

**Exercise 2.** Let $A$ be a nonarchimedean local field with ring of integers $\mathcal{O}$, uniformizer $\varpi$, residue field of $q$ elements, and the Haar measure with $\mathrm{vol}(\mathcal{O}) = 1$. Suppose $\mathfrak{d}_a(x, y) = \varpi^e\mathcal{O}$ with $e \geq 0$. Compute the depth $\delta_a(x, y)$ and the index $[\mathcal{O} : \varpi^e\mathcal{O}]$. Compare with `New.Floors.IntegralPlace.IsLargeLatticeData.exists_ideal_depth_eq`.

*Hint.* $\mathrm{vol}(\varpi^e\mathcal{O}) = q^{-e}$, so $\delta_a = q^e$, which is the index.

**Exercise 3.** Let $\mu$ be a measure, $T$ a measurable map, and $f, B, B', w \geq 0$ measurable with $w > 0$ and $f(g)^2 \leq \frac{B(g)}{w(g)}\cdot\frac{B'(Tg)}{w(Tg)}$. Show that

$$\Bigl(\int f\,d\mu\Bigr)^2 \leq \int\frac{B(g)}{w(Tg)}\,d\mu(g)\int\frac{B'(Tg)}{w(g)}\,d\mu(g).$$

Explain how [Theorem](/decl/New.Floors.Gauge.sq_lintegral_le_mul_lintegral/) uses this with $T = w_p^{-1}$ and $w = \wp_j(\cdot, x)$, and why the pairing is crossed.

*Hint.* Rearrange the product as $\frac{B(g)}{w(Tg)}\cdot\frac{B'(Tg)}{w(g)}$ and apply the Cauchy-Schwarz inequality. In each integral, $B$ or $B'$ is invariant under $R^{(j)}$ and does not depend on the Heisenberg variables, while the inverse weight at the other frame does. So the inverse weight integrates out by [Lemma](/decl/New.Floors.Gauge.lintegral_invDepthWeight_le/).

**Exercise 4.** Let $h \geq 1$ and $\tau^{800n^2} = h^{-1}$. Show that $\tau^{9\cdot 10^7n^4} = h^{-112500n^2}$, and that $\tau^{9\cdot 10^7n^4}h^{1+10^5n^2} \leq 1$ for $n \geq 1$. Then show that $h > \Lambda^{2400n^2}$ implies $\Lambda^{1200n^2} \leq \tau^{400n^2}h$. Which fields of [Definition](/decl/New.Floors.Gauge.IsShell/) do these facts feed?

*Hint.* $9\cdot 10^7 = 800\cdot 112500$, and $112500n^2 \geq 1 + 10^5n^2$. Also $\tau^{400n^2}h = h^{1/2}$, and $h^{1/2} > \Lambda^{1200n^2}$. The second fact is the condition of the field on deep vectors with $\sigma = \tau$.

**Exercise 5.** Let $A = \mathbb{R}$, $r \geq 1$, $\varphi \in L^2(\mathbb{R}^r)$, and $\hat\varphi(y) = \int\varphi(z)e^{-2\pi i\langle y, z\rangle}\,dz$. For $\xi \neq 0$ show that

$$\int_{\mathbb{R}^r}|\hat\varphi(\xi y)|^2\,dy = |\xi|^{-r}\int_{\mathbb{R}^r}|\varphi|^2.$$

Compare with the factor $(c_P/|\xi|)^{\#\mathrm{FreeIndex}}$ in [Theorem](/decl/New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_heads/). What is the role of $c_P$?

*Hint.* Substitute $u = \xi y$ and use Plancherel. The constant $c_P$ (`kernelBound`) absorbs the normalization of the Haar measure and of the character at a general place, and the fact that the source integrates over a quadric and not over the whole space.

**Exercise 6.** In [Theorem](/decl/New.Floors.Gauge.lintegral_le_of_shells/), suppose $e \geq 1$. Show that the hypothesis on the gain is empty, and that the conclusion is the bound without gain. Then let $e < 1$ and $r = 0$. What does the theorem say?

*Hint.* For $e \geq 1$, $\min(1, e)^r = 1$. For $r = 0$ the factor is again $1$, and the theorem says only that the integral is finite in terms of $\Lambda$ and $\mathcal{N}(W)$; the condition $9\cdot 10^7n^4 \leq s$ is still needed for the shells beyond the threshold.

## Notes and references

The Cauchy-Schwarz inequality is used in three ways: on a floor, with the weights crossed to separate the frames, and on the cover of a shell. Plancherel's formula and Parseval's inequality on the Heisenberg groups and on the quadrics are the source of the gains; see W. Rudin, *Fourier analysis on groups*, Interscience, 1962, for the theorem on a locally compact abelian group. The bounds for duals over a head use Cramer's rule, which the source names in TwoGauges.lean. The factorization $\mathsf{M} = \eta_{<l} * \rho$ is, by the source's own description in OneFrame.lean, a form of Weil's quotient integral formula; see A. Weil, *L'intégration dans les groupes topologiques et ses applications*, Hermann, 1940. The source names Cramer and Weil but cites no work for either, and this chapter has not compared the source with a text.

The eleven files of this chapter cite almost nothing else. The [register of findings](/chapter/register-of-findings/) records this as F-105, and the question whether the methods of `Frames` are new or adapted as Q-33, which is open. The depth, the weights $\wp_j$, the shells and the constants $\Lambda^{10^6n^3}$ and $\Lambda^{4\cdot 10^8n^4}$ follow the source. The statements in this chapter are those of Lean. Lean accepts them, if the reported checks hold. This chapter does not claim that the argument proves Theorem B in the sense of a refereed proof, and it does not claim that the Generalized Riemann Hypothesis is proved.

Status: drafted by a model. No person has checked this chapter against the Lean source.
