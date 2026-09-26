# Complete proof guide for JSP-000957 / Erdős 1152

Reviewer edition prepared 2026-09-26 from the proposed proof sources and the supplied mathematical manuscript. Source version: `412bf5f3bdff311fcd485459a394aadbcee8a103`.

**Verification status: FULL_FINAL_ELABORATED_STANDARD_AXIOMS.** `The complete seven-stage Lake build and all seven checks succeeded on the selected source bytes. Both full-type regression checks and exact-name transitive axiom audits passed. All nine dependency checkouts matched the locked revisions and were clean before and after the run; all driver-hashed source files remained unchanged. This is Lean verification by the build environment, not an independent mathematical review.`

This document reconstructs the complete proposed mathematical route to `Erdos1152.V5.ae_limsup_eq_top`, including the arguments connecting its analytic constructions to the conclusion. It is a source guide for review. Its preparation is not a Lean execution receipt or an independent mathematical certification. The final selected source revision, actual endpoint output, and mathematical review must be identified separately. Mathematical review: `NOT INDEPENDENTLY REVIEWED; submitted argument requires review`.

All source paths below are relative to the project root. Declarations in `Erdos1152/V4/` have namespace prefix `Erdos1152.V4`, those in `Erdos1152/V5/` have prefix `Erdos1152.V5`, and declarations directly in `Erdos1152/` have prefix `Erdos1152`, unless stated otherwise. Their names identify the proposed proof objects; listing them is not evidence that elaboration has succeeded.

## 1. Exact conclusion and quantifiers

For each integer \(N\geq1\), let \(X_N\subset[-1,1]\) contain \(N\) distinct points, and let nonnegative integers \(r_N\) satisfy \(r_N/N\to0\). The target is one \(f\in C([-1,1],\mathbb R)\) such that **every** polynomial sequence with

\[
 \deg p_N\leq N+r_N,\qquad p_N(t)=f(t)\quad(t\in X_N)
\]

satisfies

\[
 \limsup_{N\to\infty}|p_N(x)|=+\infty
 \quad\text{for Lebesgue-almost every }x\in[-1,1].
\]

The same \(f\) is chosen before the polynomial sequence. Its exceptional null set may depend on that sequence; a common exceptional set for an uncountable family is not asserted.

`Erdos1152/Nodes.lean` represents \(N\) by `n + 1`. `NodeArray.node n` is an injective map from `Fin (n+1)` into `Segment := Set.Icc (-1) 1`. `ContinuousFunction` is `C(Segment, ℝ)`. `NodeArray.Interpolates` requires equality at every node and `p.natDegree ≤ n+1+r n`; this natural-degree convention includes the zero polynomial. The endpoint in `Erdos1152/V5/Main.lean` is:

```lean
theorem ae_limsup_eq_top (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0)) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤
```

Mathematically, a strict degree bound \(d<N(1+\varepsilon_N)\), with \(\varepsilon_N\to0\), is covered by

\[
 r_N=\max(0,\lceil N\varepsilon_N\rceil-1),\qquad
 0\leq r_N/N\leq\max(\varepsilon_N,0)+1/N\to0.
\]

This is the reduction following Theorem 1 in the supplied manuscript. This guide does not certify a separately checked Lean endpoint for that ceiling/reindexing reduction.

The explicit formal bridge is prepared for `Erdos1152/V5/StrictEpsilon.lean`, with endpoint `Erdos1152.V5.ae_limsup_eq_top_strict_epsilon`. Integration and complete verification: **The strict endpoint is integrated in JSP957Final.lean. Its actual complete build, independent expected-type check and transitive axiom audit all passed in the same canonical run as the integer-excess endpoint.**. It uses the convenient larger budget `strictEpsilonExcess`, namely \(r(n)=\lceil(n+1)|\varepsilon(n+1)|\rceil\), for which \(r(n)/(n+1)\leq|\varepsilon(n+1)|+1/(n+1)\to0\). A nonzero polynomial satisfying the strict bound is inside this larger integer budget; the zero case is handled separately. The endpoint retains the true degree of zero as minus infinity using `WithBot.map`, including finite initial rows with a nonpositive strict bound. There is no sign assumption on \(\varepsilon\), and the bound uses \(\varepsilon(n+1)\) because the original row size is \(N=n+1\). The larger budget permits choosing one \(f\) once and then applying the integer-excess theorem to every strictly admissible polynomial sequence. [STATEMENT_CORRESPONDENCE.md](STATEMENT_CORRESPONDENCE.md) supplies the full expected type; [REPRODUCE.md](REPRODUCE.md) lists the separate full-type and axiom checks for both endpoints.

## 2. Upstream partial formalization and the replacement route

The supplied manuscript, *Almost everywhere divergence of polynomial interpolation with sublinear excess degree*, states the target as Theorem 1, Section 1, page 1. It presents a full mathematical argument; its page 16 explicitly describes the accompanying Lean archive as partial. The original formal endpoint `Erdos1152.ae_limsup_eq_top_of_cardinalGrowth_minimal` in `Erdos1152/Main.lean` retains:

1. `RemezChebyshevInequality`;
2. `CardinalGrowthCover X A`;
3. `LocalAmplificationMinimal X r A`.

Those are substantive analytic inputs, not conclusions established by that original endpoint.

The current route reuses the original polynomial correction, sign counting, compatible finite-data construction, and Baire argument. It constructs a coarse Remez estimate and an empirical logarithmic-potential cover. On the remaining region it replaces the original weighted Christoffel–Darboux/KSSV implementation route by explicit auxiliary-mesh Gamma identities, finite sinc reconstruction with two corrected moments, and polynomial tilts matched to the actual exterior-node field. The finite Bernstein construction is described in V5 as following the Fejér/Privalov argument of Olevskii–Ulanovskii, OWP2013-16; it does not assume an infinite sampling theorem.

The original manuscript and code require upstream attribution. The later assistant-assisted continuation arguments are separate contributions; their authorship or correctness cannot be attributed to the upstream author by association. The supplied PDF/TeX have empty author/date fields. An earlier public v7 attribution and later recorded Zenodo metadata have not been reconciled here into a verified identity/version. [ATTRIBUTION.md](ATTRIBUTION.md) preserves that distinction.

## 3. The local statement that suffices

For each \(H>1\), seek \(c=c(H)\in(0,1]\) such that, for almost every interior \(x\) and each upper scale \(\varepsilon>0\), there is \(0<h\leq\varepsilon\) with the following property. For **every** finite set \(S\) of already assigned points and every row threshold, one can choose a later original row and prescribe values of absolute value at most one at its nodes outside \(S\), so that **every** polynomial of the original allowed degree taking these values satisfies

\[
 |\{z\in(x-h,x+h):|p(z)|\leq H\}|\leq(1-c)\,2h. \tag{1}
\]

These are `LocalIntervalData` and `LocalAmplification` in `Erdos1152/LocalData.lean`. Their order is
\(H\mapsto c\), then \((x,\varepsilon)\mapsto h\), then \((S,\text{row threshold})\mapsto\text{row and values}\), then \(\forall p\).
In particular, \(h\) precedes \(S\).

`LocalRegions.lean` separates (1) on a measurable high-potential region and its complement; `localAmplification_of_above_minimal` combines their fractions by taking the minimum. Sections 4–17 supply these inputs. Section 18 gives the retained finite/category deduction.

## 4. A fixed weak limit, logarithmic potentials, and deletion

For \(\mu_N=N^{-1}\sum_{t\in X_N}\delta_t\), compactness of probability measures on the segment gives one strictly increasing subsequence converging weakly to a probability \(\mu\). It is fixed before later finite deletions. The source uses `V3.exists_empirical_weak_subsequence` in `Erdos1152/V3/WeakKernel.lean`, with choices `canonicalRows`, `canonicalMeasure`, and `canonicalMeasure_weak` in `V4/HighRegion.lean`.

Put \(a_k=1/(k+1)\) and

\[
 U_k(x)=\int\log\max(a_k,|x-t|)\,d\mu(t),\qquad
 U^*(x)=\inf_k U_k(x).
\]

The real representative \(U(x)=\int\log|x-t|\,d\mu(t)\) is used at almost every target point where the source section is integrable. The extended infimum, not the totalized real integral at a singular point, defines the genuine pointwise potential.

In `V4/PotentialL1.lean`, product integrability and truncation are controlled by the integrable logarithm on \([-2,2]\). The quantity

\[
 e_k=\int_{-2}^2|\log\max(a_k,|u|)-\log|u||\,du
\]

tends to zero. For each fixed \(k\), continuous-kernel weak convergence is uniform in the target variable by a finite-net argument. Truncate, pass to the weak limit, then let \(k\to\infty\): `weak_convergence_potential_L1` yields actual logarithmic \(L^1([-1,1])\) convergence. `ae_source_off_diagonal` and `ae_extendedPotential_eq` in `V4/PotentialLevel.lean` identify \(U^*=U\) almost everywhere. The logarithmic diagonal is Lebesgue-null in the target variable even when the source has atoms.

For \(Y_N=X_N\setminus S\), normalize its finite potential by the original \(N\). Removing at most \(|S|\) terms changes its \(L^1\) norm by at most

\[
 \frac{|S|}{N}\int_{-2}^2|\log|u||\,du\longrightarrow0.
\]

Thus every fixed deletion has the same potential limit: `finitePotential_deletion_L1`, `unassigned_potential_L1`, and `unassigned_error_lintegral_tendsto_zero` in `V4/FinitePotential.lean`. Thresholds may depend on \(S\); there is no single eventual threshold asserted for all finite \(S\).

## 5. High potentials: cardinal growth and coarse Remez

For \(k\in\mathbb N\), rational \(b\), and rational \(\eta>0\), take

\[
 V=\{t:U_k(t)<b-2\eta\},\qquad
 B=\{x\in[-1,1]:U(x)\geq b+3\eta\},
\]

whenever \(\mu(V)>0\). Let \(G\) be the countable union of these target layers.

Openness of \(V\) and weak convergence give a positive linear number of row nodes in \(V\), so fixed \(S\) cannot remove them all. Uniform convergence of truncated potentials, paying the bounded cost of deletion and the selected node's self-term, gives a surviving \(z_N\in Y_N\cap V\) with

\[
 \log|\omega_{Y_N\setminus\{z_N\}}(z_N)|\leq Nb,
 \qquad \omega_Y(x)=\prod_{t\in Y}(x-t).
\]

See `V4/SourceCount.lean`, especially `eventually_finite_source_hypotheses`. Except on a set of measure tending to zero, the finite potential on \(B\) is at least \(b+2\eta\). Its exceptional measure is bounded by the \(L^1\) error divided by \(\eta\), with the finite node set removed. Hence the cardinal polynomial

\[
 L_{Y_N,z_N}(x)=
 \frac{\omega_{Y_N\setminus\{z_N\}}(x)}
      {\omega_{Y_N\setminus\{z_N\}}(z_N)}
\]

has \(|L_{Y_N,z_N}(x)|\geq e^{\eta N}\) on the good set. Removing \(x-z_N\) from the numerator costs at most \(\log2\), paid by \(\eta N\geq\log2\).
The precise finite lemmas are `V3.cardinal_growth_of_potential_bounds` and `V3.cardinalGoodSet_error_measure` in `V3/AnalyticCardinal.lean`. `V4.cardinalGrowthOn_potential_layer` and `cardinalGrowthCover_canonical` assemble the cover.

The new Remez bound is

\[
 \|q\|_{[-1,1]}\leq H_0
 \left(\frac{32e}{|E|}\right)^{\deg q} \tag{2}
\]

for measurable \(E\subset[-1,1]\) with positive measure and \(|q|\leq H_0\) on \(E\). `coarse_remez` in `CoarseRemez.lean` proves it by selecting \(d+1\) ordered points of \(E\) with gaps at least \(\delta=|E|/[4(d+1)]\). Greedily deleting radius-\(\delta\) neighborhoods cannot exhaust \(E\), since even \(d+1\) such neighborhoods have total measure at most \(|E|/2\); sorting the selected points gives the stronger index-gap bound \(|x_i-x_j|\geq\delta|i-j|\). Lagrange interpolation gives \(H_0(4/\delta)^d/d!\), and \((d+1)^d/d!\leq(2e)^d\). The finite ingredients are `exists_sorted_samples` in `SeparatedSamples.lean` and `eval_bound_of_separated_nodes` in `FiniteLagrangeBounds.lean`.

Prescribe one at \(z_N\) and zero at every other unassigned node. Every admissible \(p\) factors as \(L_{Y_N,z_N}T\), where \(T(z_N)=1\) and \(\deg T\leq r_N+|S|+1=o(N)\). If its low set in a good layer had measure at least fixed \(\lambda>0\), (2) would imply

\[
 1\leq H e^{-\eta N}
       (32e/\lambda)^{r_N+|S|+1}\longrightarrow0.
\]

Thus the low set in the whole layer becomes arbitrarily small, including the vanishing exceptional set. `CoarseAmplification.lean` proves `low_set_measure_lt_of_coarse_remez` and the two `eventually_cardinal_amplification...coarse` statements. At almost every layer point choose a small interval with layer complement at most one quarter of its length, and make its low set in the layer smaller than another quarter. This gives (1) with \(c=1/2\), by `localIntervalData_of_cardinalGrowth_coarse` and `localAmplificationAbove_of_cardinalGrowthCover_coarse` in `CoarseCardinalLocal.lean`.

## 6. The complementary region is the actual minimum level

Define

\[
 A=\inf\{a\in\mathbb R:\exists k,\ \mu\{t:U_k(t)<a\}>0\}
\]

as an extended real number. `V4/PotentialLevel.lean` identifies it with the infimum of \(U^*\) on the real support of \(\mu\), and proves

\[
 G=\{x\in[-1,1]:A<U(x)\}.
\]

The rational margins do not shrink this set. One has \(A\leq\log2\). If \(A=-\infty\), \(G\) is the entire segment, so no complementary argument is needed.

For finite \(A\), the minimum principle gives \(U^*(x)\geq A\) for every real \(x\). At a support point, a truncated value below \(A\) would by continuity create a positive-source-measure open sublevel set, contradicting the definition. On a bounded support gap \((a,b)\), the actual potential is finite and concave. At \(a+\delta,b-\delta\), comparison with endpoint truncations of cutoff at most \(\delta\) gives the lower bound

\[
 A+\log(1-\delta/(b-a)).
\]

Concavity propagates it to a fixed gap point; then let \(\delta\downarrow0\). Outside the extreme support points, distance monotonicity supplies the bound. This does not assume logarithmic integrability at the gap endpoints.

The source is `V4/MinimumPrinciple.lean`: `potential_concave_gap`, `potential_ge_of_gap_endpoint_bounds`, `potential_ge_left_of_support`, `potential_ge_right_of_support`, and `potentialFloor_le_extended`. Together with the almost-everywhere representative identity, `ae_compl_high_is_minimum` gives the genuine value \(U(x)=A\) at almost every remaining point.

## 7. Positive source density is proved on the minimum region

Set \(U_y(x)=\int\log|x+iy-t|\,d\mu(t)\), \(y>0\). The complex logarithmic integral is analytic in the upper half-plane: source differences avoid the branch cut, and the inverse-distance bound \(2/\operatorname{Im}z\) on a neighborhood justifies differentiation. Its real part is harmonic. Comparison with sufficiently fine real truncations gives \(U_y(x)\geq A\). See `hasDerivAt_holPotential`, `harmonic_regularPotential`, and `floor_le_regularPotential` in `V4/RegularizedPotential.lean`.

Apply disk Harnack to the nonnegative harmonic function \(U_y-A\). For \(0<y\leq1\), use center \(x+4i\), radius \(4-y/2\), and point \(x+iy\). The closed disk stays above height \(y/2\); the Harnack factor is \(y/(16-3y)\geq y/16\). The center potential is at least \(\log4\), whereas \(A\leq\log2\). Thus

\[
 U_y(x)-A\geq(\log2/16)y. \tag{3}
\]

This is `regularPotential_boundary_lower` in `V4/DiskHarnack.lean`, from `disk_harnack_lower`.

The vertical derivative is

\[
 \partial_yU_y(x)=\int\frac{y}{(x-t)^2+y^2}\,d\mu(t).
\]

A dyadic majorant gives an upper bound \(8c\) whenever every ball mass is at most \(cr\). If this holds only for \(r\leq R\), restrict the nearby source and use total mass at most one for the remote part, obtaining \(8c+y/R^2\). These are `poissonSlope_integral_le_of_ball_growth` and `poissonSlope_integral_le_local` in `V4/BoundaryKernel.lean`.

At a regular minimum point, actual section integrability and a source-null diagonal justify continuity at \(y=0\), dominated by \(|\log|x-t||+\log3\). In `V4/VerticalBoundary.lean` set \(c_*=\log2/512\). If all \(0<r\leq R\) had mass at most \(c_*r\), take \(y=\min(1,c_*R^2)\). The mean value theorem gives an increment slope at most \(9c_*\), while (3) gives \(32c_*\), a contradiction. Hence at every scale some smaller ball has mass greater than \(c_*r\) (`minimum_has_large_source_ball`).

Lebesgue differentiation of the actual pushed-forward measure gives, almost everywhere, a finite density limit
\(w(x)=\lim_{r\downarrow0}\mu([x-r,x+r])/(2r)\).
The obstruction forces

\[
 w(x)\geq c_*/2=\log2/1024>0
\]

at almost every remaining point. `sourceDensity` is the real-valued Radon–Nikodym density, not an arbitrary function postulated to satisfy the limit. The relevant results are `ae_sourceDensity_limit`, `sourceDensity_lower_at_minimum`, and `ae_positive_density_on_minimum` in `V4/PositiveDensity.lean`. Absolute continuity of the entire source measure is not assumed.

## 8. Tangent probabilities and the explicit model

A positive source atom would force \(A=-\infty\). Thus the finite-\(A\) branch is atom-free, including at interval boundaries (`potentialFloor_bot_of_atom` and `realSource_singleton_zero_of_floor_ne_bot` in `V4/AtomFree.lean`).

The source CDF is monotone and differentiable almost everywhere. Where both its derivative and the symmetric density limit exist, the derivative equals \(w(x)\). For fixed \(\alpha<\beta\),

\[
 \mu((x+h\alpha,x+h\beta))/h\longrightarrow w(x)(\beta-\alpha).
\]

See `CDF_derivative_eq_density`, `ae_positive_CDF_derivative_on_minimum`, and `tangent_interval_mass` in `V4/LocalMass.lean`. Hence \(m_h=\mu((x-h,x+h))\sim2w(x)h>0\), and the quarter-radius mass fraction tends to \(1/4\).

Restrict to \((x-h,x+h)\), normalize by \(m_h\), and map \(t\mapsto(t-x)/h\). The resulting probability \(\nu_h\) on the segment converges weakly to uniform probability \(du/2\) (`tangentProbability_tendsto` in `V4/TangentMeasure.lean`). The logarithmic \(L^1\) theorem from Section 4 then applies.

The explicit model is

\[
 Q(u)=\tfrac12((1+u)\log(1+u)+(1-u)\log(1-u)),
 \quad Q'=\operatorname{artanh},\quad Q''=1/(1-u^2)
\]

on \((-1,1)\), with \(Q(0)=0\). Direct integration gives
\(\frac12\int_{-1}^1\log|u-v|\,dv=Q(u)-1\).
These are `externalField_derivative`, `artanh_derivative`, and `uniformPotential_eq` in `Erdos1152/ExternalField.lean`. `potential_uniformSegment` and `ae_minimum_tangent_potential_L1_model` in `V4/UniformLocalPotential.lean` identify the actual \(L^1\) limit with this particular model.

## 9. Full small-scale external-field convergence

Define the normalized limiting exterior field

\[
 F_h(u)=-m_h^{-1}\int_{|t-x|\geq h}
    (\log|x+hu-t|-\log|x-t|)\,d\mu(t).
\]

It has \(F_h(0)=0\) and positive second derivative; `V4/LimitFieldRegularity.lean` justifies differentiation on compact subintervals of \((-1,1)\).

Fix \(|u|\leq b<1\) and \(R\geq2\). The part with \(h\leq|t-x|\leq Rh\) converges uniformly, after normalization, to

\[
 \frac12\int_{1\leq|v|\leq R}\frac{dv}{(v-u)^2}
 =\frac12\left(\frac1{1-u}+\frac1{1+u}
                  -\frac1{R-u}-\frac1{R+u}\right).
\]

`V5/AnnulusKernel.lean` evaluates this integral with a continuous clipped kernel equal to the real kernel on the annulus. `V5/FilterKernel.lean` transfers weak convergence to restrictions using atom-free boundaries and ramps. `V5/AnnulusLimit.lean` keeps the normalization and integral partition explicit.

Finite centered density gives a global linear ball bound \(\mu(B(x,r))\leq C_xr\): small radii use differentiation, large radii use total probability mass. `V4/ExternalTail.lean` proves the remote estimate

\[
 \int_{|t-x|\geq Rh}\frac{h^2}{(x+hu-t)^2}\,d\mu(t)
 \leq64C_xh/R.
\]

As \(m_h>w(x)h\) eventually, the normalized bound is \(64C_x/(w(x)R)\). First fix \(R\), then send \(h\downarrow0\), then \(R\to\infty\). This gives \(F_h''\to Q''\) uniformly on \([-b,b]\), namely `ae_minimum_second_small_scale`.

Retain the affine error:
\(\beta_h=F_h'(0)\), \(E_h(u)=F_h(u)-Q(u)-\beta_hu\).
Two mean-value estimates give
\(|F_h'-Q'-\beta_h|\leq\delta b\), \(|E_h|\leq\delta b^2\)
from \(|F_h''-Q''|\leq\delta\) (`field_affine_error` in `V5/AffineControl.lean`).

Let \(L_h\) denote the actual logarithmic potential of \(\nu_h\). The exact decomposition is

\[
 U(x+hu)-U(x)=m_h(L_h(u)-L_h(0)-F_h(u)).
\]

At almost every remaining point, the fixed measurable regular minimum set has density one. Together with \(L_h\to Q-1\) in \(L^1\), this supplies
\(u\in(-1/4,-1/8)\), \(v\in(1/8,1/4)\),
whose physical points belong to that same minimum set and whose two tangent-potential errors are small. See `minimum_samples` and `ae_minimum_samples` in `V5/MinimumSamples.lean`. This uses one fixed measurable set, not an uncountable intersection over moving levels.

The equal original potential values cancel the central value exactly:

\[
 \beta_h(v-u)=
 [L_h(v)-(Q(v)-1)]-[L_h(u)-(Q(u)-1)]-E_h(v)+E_h(u).
\]

Four errors of size at most \(\delta\) and gap \(v-u\geq1/4\) imply \(|\beta_h|\leq16\delta\). Enlarge the working compact radius to at least \(1/2\) for the samples, and take \(\delta=\varepsilon/64\). All three jet errors then tend uniformly to zero. This is `ae_minimum_small_scale_field` / `ae_minimum_C2_model` in `V5/SmallScaleField.lean`.

## 10. A physical scale fixed before deletion

For a finite surviving row \(Y=X_N\setminus S\), write \(I=(x-h,x+h)\), \(s=|Y\cap I|\), and

\[
 F_Y(u)=-s^{-1}\sum_{t\in Y\setminus I}
   (\log|x+hu-t|-\log|x-t|).
\]

These are `insideNodes`, `outsideNodes`, and `finiteField` with its two derivatives in `V4/FiniteExternalField.lean`. The exterior ratios are positive on \(|u|<1\), the field is convex, and

\[
 \omega_{Y\setminus I}(x+hu)/\omega_{Y\setminus I}(x)
       =e^{-sF_Y(u)}. \tag{4}
\]

Multiplying a polynomial \(P((z-x)/h)\) of degree at most \(s-1\) by that normalized exterior polynomial gives degree less than \(|Y|\), vanishes at every node of \(Y\setminus I\), and has value \(e^{-sF_Y(u)}P(u)\) inside. No value condition is imposed here on the previously assigned nodes in \(S\). The exact lemmas are `exp_finiteField_eq_weight`, `liftLocalPolynomial_degree`, `liftLocalPolynomial_eval`, and `liftLocalPolynomial_zero_outside`.

Fix the height-dependent \(\rho,b,\delta\) needed below. At an almost-everywhere minimum point, choose \(h\) using Section 9 and the quarter-interval mass limit, with \([x-h,x+h]\subset(-1,1)\). Only afterwards introduce \(S\). For each fixed \(S\), along sufficiently late canonical rows,

\[
 \begin{split}
 &s\to\infty,\qquad (r_N+|S|+1)/s\to0,\\
 &|Y\cap(x-h/4,x+h/4)|\leq(1/4+1/(16\rho))s,\\
 &\sup_{|u|\leq b}|F_Y^{(j)}(u)-Q^{(j)}(u)|<\delta
                         \quad(j=0,1,2). \tag{5}
 \end{split}
\]

`V4/RestrictedKernel.lean` proves convergence for restricted kernels, `V4/DeletedKernel.lean` handles finite deletion and quotient stability, and `V4/ExternalFieldLimit.lean` gives `finiteFieldJet_tendsto_uniform` and `insideNodes_fraction_tendsto`. `ae_minimum_choose_field_scale` in `V5/RowGeometry.lean` combines them. The positive limiting interval mass makes \(s\) a positive fraction of \(N\), so the global sublinear excess remains negligible locally.

## 11. A finite Bernstein witness for arbitrary nearby nodes

For every \(B>1\), constants \(\rho\in\mathbb N_{>0}\), \(0<\sigma<\pi\), \(M,\ell,C>0\) are chosen **before** a finite \(\Lambda\subset[-\rho,\rho]\), \(|\Lambda|\leq2\rho+1\). A real-on-real entire \(g\) is then constructed with

\[
 \begin{split}
 &|g(x)|\leq M\ (x\in\mathbb R),\quad
 |g|\leq1\text{ on }\Lambda\text{ and on }|x|\geq\rho,\\
 &g(x)\geq B\text{ on some }[a,b]\subset[-\rho,\rho],
                         \quad b-a=\ell,\\
 &|g(z)|\leq C e^{\sigma|\operatorname{Im}z|}/(1+|z|)^6. \tag{6}
 \end{split}
\]

The complete finite mechanism is:

1. Normalized squared Dirichlet kernels on a circle grid give nonnegative Fejér weights summing to one and interpolating their coefficients. With \(L=4mA\) coefficients and only \((4A-1)m\) homogeneous constraints, a nonzero common-kernel vector exists. Normalize at a coefficient of largest modulus to get \(Q_0(t_0)=1\), \(\|Q_0\|_\infty\leq1\), and every constraint. Source: `exists_common_kernel_vector` in `V5/FiniteFourier.lean`; `exists_normalized_fejer_annihilator` in `V5/FejerGrid.lean`; `exists_privalov_grid` in `V5/PrivalovProbe.lean`.
2. The low/high cosine-block difference equals \(2\sin(At)\sum_{j=1}^A\sin(jt)/j\), bounded by \(2(1+\pi)\) independently of \(A\). Normalize by `probeNormalization = 2*(1+π)`. The low block retains \(H_A=\sum_{j=1}^A1/j\). Source: `harmonicSine_bound` and `privalov_split_bound` in `V5/SinePolynomial.lean`.
3. For any linear projection \(U\) onto band \([-k,k]\), set \(d=2L\), \(k=Ad=8mA^2\). Low modulations times \(Q_0\) remain in the band. High modulations, after projection and reflection, have frequencies of absolute value at least \(2L\). A Vallée Poussin convolution fixes the former, kills the latter, and has \(L^1\) norm at most three. Some bounded input satisfying the \(m\) additional constraints therefore has projected value at least \(H_A/[3\,\text{probeNormalization}]\). Source: `finite_privalov` in `V5/Privalov.lean`, supported by `V5/FejerFilter.lean` and `V5/Spectrum.lean`. Its orbit is a finite sum of continuous outputs, so no continuity assumption on the arbitrary full operator is inserted.
4. Extend the prescribed finite circle node set to \(2k+m+1\) points. Interpolate on \(2k+1\) using the actual trigonometric interpolation projection and impose zero output at the remaining \(m\) through the extra constraints. Every prescribed node is retained. Source: `finite_trigonometric_sampling_witness` in `V5/CircleInterpolation.lean`. Rotation, scaling, and taking the real part at a maximum give `real_trig_sampling` in `V5/NormalizeTrig.lean`.
5. Since \(H_{2^j}\geq1+j/2\), choose \(A\) for height \(M=8B\), then an integer \(q>\max(1,M/\gamma)\), where
   \[
   k=32qA^2,\quad R=k+q,\quad\rho=k+2q,\quad
   \sigma_0=\frac{32\pi A^2}{32A^2+1},\quad
   \gamma=\frac{\pi}{16(32A^2+1)}.
   \]
   Use \(m=4q\) in the preceding step, so its budget is \(2\rho+1\). Extend the trigonometric polynomial to an entire function at scale \(R\), and multiply by a fourth-power sinc window about its peak. Since \(\rho-R=q\) and \(M\leq\gamma q\), this gives the exterior bound. A uniform derivative bound gives a positive-length interval on which this first localized function is at least \(2B\); bandwidth is \(\sigma_0+4\gamma<\pi\). Sources: `V5/HarmonicBudget.lean`, `V5/TrigExtension.lean`, and `local_bernstein_exists` in `V5/LocalBernstein.lean`.
6. A sixth-power sinc window about zero, chosen using the remaining bandwidth, is at least \(1/2\) on the fixed peak region and at most one on the real line. Thus the preceding \(2B\) peak remains at least \(B\), as required by (6). The window also supplies its algebraic decay, with bandwidth recomputed after multiplication. This is `local_bernstein_decay_exists` in `V5/SixthWindow.lean`.

These steps do not assume a uniform separation of the prescribed nodes.

## 12. Contour sampling and finite moment correction

For \(t_0\leq t\leq1\), \(|\theta|\leq1/2\), and \(\sigma<\pi t_0\), put \(v_j=(j+\theta)/t\), and let \(\operatorname{sinc}_\pi u=\sin(\pi u)/(\pi u)\), with value one at zero. The denominator \(\sin(\pi(tz-\theta))\) has simple zeros \(v_j\), with derivative \(\pi t(-1)^j\). Circles centered at \(\theta/t\) with radius \((J+1/2)/t\), \(J\geq1\), have lower bound
\[
 |\sin(\pi(tz-\theta))|\geq c_{\sin}e^{\pi t|\operatorname{Im}z|},
 \qquad c_{\sin}=\min\bigl((2e^\pi)^{-1},(1-e^{-\pi/2})/2\bigr)>0.
\]

The source treats both the near-real-axis and high-imaginary portions of the circle. Combined with (6), the polynomial factors of degrees zero and one still leave vanishing moment contour integrals; the extra Cauchy denominator yields the reconstruction limit as well.

`V5/FinitePoles.lean` gives the finite residue calculation, `V5/SineContour.lean` the denominator bound, `V5/SamplingContours.lean` the limiting estimates, and `V5/SamplingDecay.lean` absolute summability. `hasSum_shannon` and `hasSum_alternating_moment` in `V5/SamplingFormula.lean` yield

\[
 g(\xi)=\sum_{j\in\mathbb Z}g(v_j)\operatorname{sinc}_\pi(t(\xi-v_j)),
 \qquad \sum_j(-1)^jv_j^d g(v_j)=0\quad(d=0,1). \tag{7}
\]

Truncation to \(-J\leq j\leq J\), \(J\geq1\), loses the moments. Let their errors be \(M_0,M_1\), put \(a=v_0,b=v_1\), and set

\[
 \alpha=(bM_0-M_1)/(a-b),\qquad
 \beta=(M_1-aM_0)/(a-b).
\]

Add \(\alpha\) to coefficient zero and subtract \(\beta\) from coefficient one. The new alternating moments are \(M_0+\alpha+\beta=0\) and \(M_1+a\alpha+b\beta=0\). Since \(a-b=-1/t\), the correction is bounded by \(64C(1+2/t_0)\) times a uniform lattice tail.

The corrected finite sum \(S(\xi)\) uniformly approximates \(g\). For \(|v_j|\leq T\) and \(|\xi|\geq2T\), expand

\[
 (\xi-v)^{-1}=\xi^{-1}+v\xi^{-2}
                         +v^2/(\xi^2(\xi-v)).
\]

The first two sums cancel and \(|\xi-v|\geq|\xi|/2\), giving

\[
 |S(\xi)|\leq\frac{2}{\pi t}
                  \frac{\sum_j|c_j|v_j^2}{|\xi|^3}. \tag{8}
\]

The exact declarations are `corrected_moments`, `corrected_sampling_approximation`, and `finite_sinc_cubic_tail` in `V5/FiniteSampling.lean`. `uniform_corrected_sampling` in `V5/SamplingPacket.lean` chooses \(J,T,K\) before \(t,\theta,g\), with any specified positive approximation tolerance and tail \(K/|\xi|^3\).

## 13. Exact auxiliary-mesh Gamma/sinc identities

For \(m\geq1\), define
\(\tau_j=-1+(2j+1)/m\), \(0\leq j<m\), and
\(W_m(u)=\prod_j(u-\tau_j)\).
This auxiliary mesh is chosen by the proof, independently of original-node spacing.

Set

\[
 a(v)=\frac{\Gamma(v+1/2)e^{v-v\log v}}{\sqrt{2\pi}},
 \qquad A_m(u)=a(m(1+u)/2)a(m(1-u)/2),
\]

with \(v\log v=0\) at zero. Gamma reflection and shift identities give, including endpoints,

\[
 W_m(u)=2(-1)^m e^{m(Q(u)-1)}A_m(u)
                       \cos(\pi m(1+u)/2).
\]

Differentiating at the mesh nodes gives, for their Lagrange basis \(L_{m,j}\),

\[
 e^{-m(Q(u)-Q(\tau_j))}L_{m,j}(u)=
 \operatorname{sinc}_\pi(m(u-\tau_j)/2)\frac{A_m(u)}{A_m(\tau_j)}. \tag{9}
\]

These are `meshPolynomial_exact`, `meshPolynomial_derivative_at_node`, and `meshKernel_exact` in `V5/MeshKernel.lean`. `V5/GammaAmplitude.lean`, using `GammaIncrementBounds.lean` and Stirling asymptotics, supplies positivity, \(a(v)\to1\), global positive lower and upper bounds, and \(A_m\to1\) uniformly on compact subintervals of \((-1,1)\). The tails below need those global bounds, not only interior asymptotics.

## 14. A polynomial tilt matched to the actual field

For \(F=F_Y\), choose after (6)

\[
 t_0=(\sigma/\pi+1)/2,\quad
 \kappa=(1-t_0)/2\in(0,1/4],\quad
 b=1-\kappa/256,\quad\delta=\kappa/1024.
\]

For large \(s\), let \(m=\lfloor(1-\kappa)s\rfloor\), \(k=\lfloor(s-m)/2\rfloor\). `packet_degree_budget` in `V5/TiltBudget.lean` pays rounding losses:

\[
 t_0\leq m/s\leq1-\kappa,\quad
 k\geq(9/20)(s-m),\quad m-1+k\leq s-1.
\]

For \(|y|\leq1/4\), put \(R=F-(m/s)Q\), \(\alpha=sR'(y)/k\), and

\[
 E_y(u)=e^{-s(R(u)-R(y))}(1+\alpha(u-y))^k.
\]

The derivative tolerance and degree slack give \(|\alpha|\leq3/4\), hence the tilt base is at least \(1/16\) on the segment. On \([-b,b]\), \(R''\geq\kappa-\delta>0\). Outside it, use convexity of the actual \(F\) and the model endpoint bound

\[
 Q(u)-Q(b)-Q'(b)(u-b)\leq\log(2/(1+b))\leq\kappa/64
\]

(and reflection). The residual supporting-line margin is at least
\(\kappa/8-\kappa/64-4\delta>\kappa/16\).
Because \(k\alpha=sR'(y)\), the linear term cancels under \((1+v)^k\leq e^{kv}\). Consequently

\[
 0<E_y(u)\leq1\ (|u|<1),\qquad
 E_y(u)\leq e^{-\kappa s/16}\ (b<|u|<1). \tag{10}
\]

For \(u=y+2\xi/s\), the remaining error is quadratic:
\(s(C_2+2)(u-y)^2=4(C_2+2)\xi^2/s\).
It tends to zero uniformly for bounded \(\xi\), without requiring \(s\|F_Y-Q\|\to0\).

Sources: `V5/TaylorSupport.lean`; `matchedSlope_bound`, `matched_base_pos`, `matchedEnvelope_global`, and `matchedEnvelope_micro_bound` in `V5/WeightedEnvelope.lean`. `uniform_actual_packet_control` in `V5/UniformPacketControl.lean` combines these with Gamma amplitude estimates at one threshold independent of later \(Y,x,h,y\).

## 15. One actual polynomial peak

Take
\(\theta=\lfloor m(1+y)/2\rfloor+1/2-m(1+y)/2\), so \(|\theta|\leq1/2\).
The retained mesh nodes have microscopic coordinates
\(v_j=(j+\theta)/(m/s)\); `packetIndex_properties` places their indices in the mesh for \(m\geq8(J+2)\).
Using Section 12's corrected coefficients, form

\[
 P(u)=\frac{e^{sF(y)-mQ(y)}}{A_m(y)}
 (1+\alpha(u-y))^k
 \sum_{j=-J}^{J}c_j A_m(\tau_{i_j})e^{mQ(\tau_{i_j})}L_{m,i_j}(u).
\]

The exact coefficient precompensation in (9) gives

\[
 e^{-sF(u)}P(u)=E_y(u)\frac{A_m(u)}{A_m(y)}
                              S(s(u-y)/2). \tag{11}
\]

`weightedPacket_eval` in `V5/WeightedPolynomial.lean` proves this identity; `weightedPacket_degree` gives degree at most \(m-1+k\leq s-1\). The corrected moments apply to exactly these \(c_j\), not to different amplitude-weighted samples.

Take as \(\Lambda\) the nodes of \(Y\cap I\) with microscopic coordinate in \([-\rho,\rho)\), provided their number is at most \(2\rho+1\). All other nodes of \(Y\cap I\) have microscopic absolute value at least \(\rho\), where (6) also bounds \(g\) by one. Choose \(\eta=\min(1/64,1/[16(M+1)])\). On the controlled compact interval, `packet_product_error` bounds the combined errors in \(E_y\), \(A_m(u)/A_m(y)\), and \(S-g\); on the remaining outer part of the local interval, (10) suppresses the global amplitude and sinc-sum bounds.

Lift via (4). The resulting actual polynomial has degree less than \(|Y|\), vanishes at the nodes of \(Y\setminus I\), has absolute value at most \(3/2\) at every node of \(Y\), and is at least \(B-1\) on a microscopic interval of length \(\ell\). Its cubic bound \(D/|\xi|^3\) applies when \(z\in I\) and \(|\xi|\geq2T\), where \(\xi=s((z-x)/h-y)/2\) is its center-relative microscopic coordinate. It is not a decay assertion on the whole real line. This is `local_weighted_peak_exists` in `V5/LocalWeightedPeak.lean`. Its constants and threshold precede the finite node set, physical center/scale, and moving center.

## 16. Many separated peaks with alternating signs

In microscopic coordinate \(Z=s(z-x)/(2h)\), the central interval is \((-s/8,s/8)\). Use half-open cells of length \(2\rho\), discarding the left boundary cell; their number is \(\lfloor s/(8\rho)\rfloor-1\). A bad cell contains at least \(2\rho+2\) nodes. The count in (5) and disjoint counting give

\[
 \#\{\text{good cells}\}\geq3s/[32\rho(\rho+1)]-2,
\]

hence at least \(3s/[64\rho(\rho+1)]\) for large \(s\). These are `countingNodes_central_subset`, `countingNodes_disjoint`, and `goodBoxes_card_lower` in `V5/GoodBoxes.lean`. The discarded boundary cell ensures the counted nodes lie in the open central interval.

Choose an integer stride \(q\) before the row, with \(L=2\rho q\) satisfying

\[
 L\geq4T,\quad L\geq4\rho,\quad 32D/L^3\leq1/4.
\]

Use `exists_packet_stride` in `V5/SelectedCenters.lean`. A residue class of good indices modulo \(q\) retains at least a \(1/q\) fraction (`exists_large_residue_class`). Its ordered centers \(c_i\) satisfy \(|c_i-c_j|\geq L|i-j|\), and their number \(K\) obeys

\[
 K\geq a_0s,\qquad a_0=3/[64\rho(\rho+1)q]>0.
\]

At any point \(z\in I\), a nearest-center choice places every other center at microscopic distance at least \(L|i-j|/2\geq2T\), so their cubic bounds sum to at most \(32D/L^3\leq1/4\). The finite estimates are `fin_distance_cube_sum`, `cubic_cross_sum`, `own_center_nearest`, and `exists_nearest_center` in `V5/CrossTails.lean`.

Construct each peak at parameter \(B=8(H+1)\). Its physical peak interval has length \(2h\ell/s\) and contains no node of \(Y\): such a node would violate the \(3/2\) bound because the peak is at least \(8(H+1)-1\). Previously assigned points in \(S\) need not be excluded. The node polynomial \(\omega_Y\) therefore has constant nonzero sign there. Choose \(\sigma_i\in\{\pm1\}\) making \(\sigma_i\omega_Y>0\) on interval \(i\), and set

\[
 F=\tfrac12\sum_{i=0}^{K-1}(-1)^i\sigma_i P_i.
\]

At a node of \(Y\cap I\), one nearest peak is at most \(3/2\) and the others sum to at most \(1/4\), so \(|F|\leq1\). At a node of \(Y\setminus I\), every peak polynomial is zero. On peak interval \(i\), which lies inside \(I\), its own peak dominates, giving \(|F|>H\) and \((-1)^iF/\omega_Y>0\). The intervals are ordered and disjoint, and \(\deg F<|Y|\).
Sources: `assemble_packet_family` in `V5/AssemblePeaks.lean` and `actual_weighted_family` in `V5/WeightedFamily.lean`.

## 17. Alternation forces every interpolant to be large

If \(p=F\) on \(Y\) and \(\deg p\leq|Y|+d\), then
\(p=F+\omega_Yq\), \(\deg q\leq d\)
by `interpolation_correction` in `Erdos1152/Interpolation.lean`.

Let \(L_{\mathrm{low}}\subset\{0,\ldots,K-1\}\) be the original indices of intervals not wholly high for \(p\), and choose a low point in each. There the correction \(q\) must oppose the signed peak. A sign change is forced only when **both original consecutive indices** \(i,i+1\) belong to \(L_{\mathrm{low}}\), not merely when two indices become adjacent after deletions. Put

\[
 J=\{i:i\in L_{\mathrm{low}},\ i+1\in L_{\mathrm{low}}\}.
\]

The disjoint ordered gaps for these pairs give distinct roots, hence \(|J|\leq\deg q\leq d\). The retained-position inequality is \(2|L_{\mathrm{low}}|\leq K+1+|J|\). Since the wholly high intervals number \(K-|L_{\mathrm{low}}|\), it follows that

\[
 K\leq2\#\{\text{intervals wholly high for }p\}+d+1.
\]

These are the original `alternating_interval_bound` in `Intervals.lean` and `retained_positions`, `sign_changes_le_degree`, `alternating_sample_bound` in `SignCount.lean`. For disjoint intervals of length \(w=2h\ell/s\),

\[
 2|\{z\in I:|p(z)|>H\}|\geq(K-d-1)w. \tag{12}
\]

`V3.alternating_high_measure` and `V3.low_measure_of_alternating_polynomial` in `V3/AlternatingMeasure.lean` prove the measure step; `V5.low_measure_of_fin_family` adapts the finite index type.

For the deleted row take \(d=r_N+|S|\). The original bound \(N+r_N\) is at most \(|Y|+d\). Choose the row using (5), late enough that \((d+1)/s<a_0/2\) and every other threshold holds. With

\[
 c=\min(1/2,a_0\ell/8)>0,
\]

one has \(2c(2h)\leq(K-d-1)(2h\ell/s)\). Equation (12) is exactly (1). The prescribed new values are \(F(t)\), bounded by one. This proves the proposed `localAmplificationMinimal_canonical` in `V5/Minimal.lean`, with no field, density, sampling, or peak-family hypothesis retained in its interface.

## 18. Finite stages, dense open sets, and a single continuous function

**Local to interval.** A `Stage` stores finitely many selected rows and one consistent bounded assignment on their union of nodes. `LocalIntervalData.extend` uses that union as \(S\), so later values do not overwrite earlier ones. A finite disjoint Vitali selection covers more than half the measure of any interior interval. Extend over its intervals sequentially; later stages shrink the common low set and preserve preceding losses. `intervalAmplification_of_localData` in `LocalToInterval.lean` gives interval fraction \(c_I=c/2\), using `finite_disjoint_intervals` in `Vitali.lean`.

**Uniform contraction.** For selected rows \(T\), let
\(L_T(p,H)=[-1,1]\cap\bigcap_{n\in T}\{|p_n|\leq H\}\).
Its boundary has a cover by at most
\(B_T=2+2\sum_{n\in T}(n+1+r_n)\)
points: the segment endpoints and relevant roots of \(p_n\pm H\), with constant-polynomial cases handled separately (`Boundary.lean` and `Stage.boundary_cover`). Choose a uniform partition whose cells meeting any such boundary have total length at most \(\delta/4\) (`exists_uniform_partition` in `Partition.lean`). Apply interval amplification in every cell before seeing the polynomial sequence. If the old low set has measure at least \(\delta\), at least three quarters of its measure is in cells wholly belonging to it. The new low set has measure at most
\((1-3c_I/4)|L_T(p,H)|\).
This is `one_batch` in `Batches.lean`, using `partition_contraction` in `Contraction.lean`. The choices are uniform over all sequences fitting the finite data.

**Finite obstruction.** Iterate the batch finitely many times: a fixed contraction below one reduces initial measure at most two below any prescribed \(\delta>0\). `exists_small_low_stage` and `finiteAmplification_of_intervalAmplification` in `FiniteConstruction.lean` give the result. `Stage.continuous_extension_fits` extends the consistent values to a continuous \(g\), \(\|g\|\leq1\). Thus for every \(H>1,\delta>0,N_0\), some finite rows above \(N_0\) force common low-set measure below \(\delta\) for every interpolating sequence of \(g\). This is `FiniteAmplification`.

**Openness.** A finite obstruction at \(H>M\) is stable at height \(M\) under sufficiently small uniform changes of the continuous function. On each selected row subtract the Lagrange interpolant of the data perturbation. Its degree is at most the row size minus one and its norm is bounded by a finite Lagrange constant times the perturbation. This recovers an admissible polynomial for the old data. Radius less than \((H-M)/C_T\), for a common finite constant, gives `finiteObstruction_interior` in `FiniteObstruction.lean`.

**Density.** Approximate an arbitrary continuous function by a polynomial \(h_0\), and choose a small \(\varepsilon>0\). Take \(H\) so that \(\varepsilon H>M+\|h_0\|\), with margin, and choose rows large enough to absorb \(\deg h_0\). The function \(h_0+\varepsilon g\) is in the chosen neighborhood. For an interpolant \(p_n\) of it, \((p_n-h_0)/\varepsilon\) interpolates \(g\) with the required degree budget, so the finite obstruction applies. These are `finiteObstruction_translate` and `dense_finiteObstruction_interior` in `Density.lean`.

**Baire and null sets.** In the complete space of continuous functions, intersect these dense open sets for integer height \(M\), row threshold \(N_0\), and tolerance \(1/(k+1)\). `exists_all_finiteObstructions` in `Baire.lean` gives one \(f\) in all of them. Now fix any entire sequence of interpolants of that \(f\). For fixed \(M,N_0\), the set where all tail values are bounded by \(M\) is contained in finite common low sets of arbitrarily small measure, hence is null (`common_tail_null`). The countable union over \(M,N_0\) is null. Off it, every tail exceeds every integer height, giving EReal limsup \(+\infty\). The final declarations are `ae_unbounded_of_finiteAmplification`, `limsup_eq_top_of_unbounded`, and `ae_limsup_eq_top_of_finiteAmplification`. Segment endpoints are null.

The Baire choice of \(f\) precedes the polynomial sequence; only the final spatial null set depends on the sequence. The original quantifier order is preserved.

## 19. Terminal dependency chain and constant ledger

| Source | Declaration and role |
| --- | --- |
| `Erdos1152/V4/HighRegion.lean` | `cardinalGrowthCover_canonical`: constructed high cover |
| `Erdos1152/CoarseCardinalLocal.lean` | `localAmplificationAbove_of_cardinalGrowthCover_coarse`: high local input |
| `Erdos1152/V5/RowGeometry.lean` | `ae_minimum_choose_field_scale`: actual minimum-point row geometry |
| `Erdos1152/V5/WeightedFamily.lean` | `actual_weighted_family`: actual alternating peaks |
| `Erdos1152/V5/Minimal.lean` | `localAmplificationMinimal_canonical`: complementary local input |
| `Erdos1152/LocalRegions.lean` | `localAmplification_of_above_minimal`: full local input |
| `Erdos1152/Main.lean` | `ae_limsup_eq_top_of_localAmplification`: finite/Baire conclusion |
| `Erdos1152/CoarseMain.lean` | `ae_limsup_eq_top_of_cardinalGrowth_minimal_coarse`: coarse-Remez route |
| `Erdos1152/V4/Main.lean` | `ae_limsup_eq_top_of_canonical_minimal`: canonical high cover inserted |
| `Erdos1152/V5/Main.lean` | `ae_limsup_eq_top`: constructed minimal input inserted |

| Step | Constant or budget | Purpose |
| --- | --- | --- |
| Coarse Remez | \(32e\) | Exponential degree dependence |
| High layer | \(b-2\eta,b+3\eta,b+2\eta\) | Pays \(\log2\) and leaves \(e^{\eta N}\) |
| High local fraction | \(1/2\) | Two quarter-interval losses |
| Density | \(c_*=\log2/512,\ w\geq\log2/1024\) | Slope \(32c_*\) contradicts upper bound \(9c_*\) |
| Remote second derivative | \(64C_xh/R\) | Normalized \(O(1/R)\) tail |
| Affine recovery | Gap \(1/4\), slope \(16\delta\), \(\delta=\varepsilon/64\) | All three jets converge |
| Finite Privalov | \(L=4mA,d=2L,k=8mA^2\), filter norm \(\leq3\) | Low/high frequency separation |
| Bernstein localization | \(k=32qA^2,R=k+q,\rho=k+2q\) | Node budget and exterior margin |
| Moment correction | \(64C(1+2/t_0)\) | Uniform finite correction |
| Packet field | \(b=1-\kappa/256,\delta=\kappa/1024\) | Global supporting-line margin |
| Degree allocation | \(m=\lfloor(1-\kappa)s\rfloor,k=\lfloor(s-m)/2\rfloor\) | \(m-1+k\leq s-1\) |
| Tilt | \(|\alpha|\leq3/4\), base \(\geq1/16\) | Positivity and outer \(e^{-\kappa s/16}\) |
| One peak | \(B=8(H+1)\), node bound \(3/2\) | Assembly margin and node-free intervals |
| Stride | \(L\geq4T,4\rho,\ 32D/L^3\leq1/4\) | Cross-peak control |
| Peak count | \(a_0=3/[64\rho(\rho+1)q]\) | \(K\geq a_0s\) |
| Minimal fraction | \(\min(1/2,a_0\ell/8)\) | Pays the \(d+1\) correction loss |
| Finite contraction | \(c_I=c/2,\ 1-3c_I/4<1\) | Arbitrarily small common low sets |

Parameters with reused letters in different finite constructions are local to those constructions. The essential order is: height-dependent constants first; then almost-everywhere point and physical scale; then finite deletion; then sufficiently late row; then its finite polynomials; finally all interpolants.

## 20. Evidence supplied and remaining acceptance requirements

The proposed argument now specifies how the two regions exhaust the segment almost everywhere, how both construct the original local predicate, and how the finite/Baire route produces the exact universal conclusion. Equations (5) and (12) are concrete review interfaces between the new analytic route and the retained finite machinery. They are not extra assumptions in the displayed V5 endpoint.

A reviewer can trace every major analytic input through the declarations identified above. Particular checks include the extended-potential representative, restricted-measure limits, finite Privalov frequency counts, contour estimates, actual coefficient precompensation, and scale-before-deletion order. Selected calculation checks do not certify every module or the full argument.

Formal acceptance requires an actual successful project build of the final selected revision with Lean `4.33.0` and mathlib commit `db584cd6d46c92f209a44c0f1c829460d327499d`. The full statement and transitive-axiom checks are `checks/FinalStatement.lean`, `checks/FinalAxioms.lean`, `checks/StrictEpsilonStatement.lean`, and `checks/StrictEpsilonAxioms.lean`; final strict-endpoint integration must preserve the original integer-excess checks. `JSP957Final.lean` is the release entry. A submission must attach or link genuine results for the exact public source revision, including the absence of unacceptable proof placeholders or added assumptions. Run-specific receipt: `logs/v6/20260926T121829_907367Z/BUILD_RESULT.json`; receipt SHA-256: `899475250553c5acc4991fbc46477f544b8fcadaf60d7efe725b9b53c9bbaf99`. This guide itself is not that receipt.

The manuscript, its explicitly partial original formalization, and this replacement route must remain separately attributed. Until the required mathematical and formal evidence is available, the accurate description is a **complete proposed proof route and formalization candidate**, not an established published or kernel-verified solution.


## 21. Current definition locations

These source moves preserve namespaces, names, types and defining expressions. They separate reusable definitions from later theorems; they do not remove the actual external-field or peak constructions from the final proof.

| Declaration | Definition file | Continued use |
| --- | --- | --- |
| `Erdos1152.V4.finiteFieldJet` | `Erdos1152/V4/FiniteFieldJet.lean` | `ExternalFieldLimit.lean` imports this definition and retains its convergence theorems; `RowGeometry.lean` uses that convergence chain. |
| `Erdos1152.V5.modelJet` | `Erdos1152/V5/ModelJet.lean` | `AnnulusKernel.lean` imports this definition and retains the actual annular integral calculations. |
| `Erdos1152.V5.microCoordinate`, `Erdos1152.V5.countingNodes` | `Erdos1152/V5/LocalCoordinates.lean` | `LocalWeightedPeak.lean` and `GoodBoxes.lean` import these definitions; `WeightedFamily.lean` explicitly retains the peak-existence input. |

The substantive calculations and constants in Sections 3–19 are unchanged by these source moves. In particular, a definition-only import is not a substitute for the convergence input (5) or the peak and measure arguments (11)–(12).
