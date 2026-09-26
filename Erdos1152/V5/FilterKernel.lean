import Erdos1152.V4.RestrictedKernel

/-!
# Restricted weak kernel limits for the actual radius filter

The V4 statements were indexed by natural-number rows.  Here the same
finite-cover/ramp proof is carried out for an arbitrary filter, in particular
`𝓝[>] 0`.  Only a null boundary of the limiting interval is needed.  The
uniform tangent probability supplies that condition explicitly below.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V5
open V4

/-- Finite-cover proof, not a sequential-uniformity assumption. -/
theorem weak_kernel_filter {ι : Type*} {l : Filter ι}
    (μs : ι → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs l (𝓝 μ))
    (K : Segment × Segment → ℝ) (hK : Continuous K) :
    ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ x : Segment,
      |(∫ t, K (x,t) ∂(μs i : Measure Segment)) -
        ∫ t, K (x,t) ∂(μ : Measure Segment)| < ε := by
  intro ε hε
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous hK) (ε/4) (by positivity)
  obtain ⟨A,_,hA,hcover⟩ := finite_cover_balls_of_compact
    (isCompact_univ : IsCompact (univ : Set Segment)) hδ
  have hpoint (y : Segment) : ∀ᶠ i in l,
      |(∫ t, K (y,t) ∂(μs i : Measure Segment)) -
        ∫ t, K (y,t) ∂(μ : Measure Segment)| < ε/4 := by
    let Ky : C(Segment,ℝ) :=
      ⟨fun t => K (y,t),hK.comp (continuous_const.prodMk continuous_id)⟩
    have ht := ((ProbabilityMeasure.continuous_integral_continuousMap Ky).tendsto μ).comp hμ
    simpa only [Metric.mem_ball,Real.dist_eq,Ky,ContinuousMap.coe_mk,Function.comp_apply] using
      ht.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε/4))
  have hfin : ∀ᶠ i in l, ∀ y ∈ hA.toFinset,
      |(∫ t, K (y,t) ∂(μs i : Measure Segment)) -
        ∫ t, K (y,t) ∂(μ : Measure Segment)| < ε/4 :=
    (eventually_all_finset hA.toFinset).mpr (fun y _ => hpoint y)
  filter_upwards [hfin] with i hi
  intro x
  obtain ⟨y,hy,hxy⟩ : ∃ y ∈ A, dist x y < δ := by
    simpa only [Set.mem_iUnion,Metric.mem_ball,exists_prop] using hcover (mem_univ x)
  have hk (t : Segment) : |K (x,t)-K (y,t)| ≤ ε/4 := by
    have hd : dist (x,t) (y,t) < δ := by
      simpa only [Prod.dist_eq,dist_self,max_eq_left dist_nonneg] using hxy
    simpa only [Real.dist_eq] using (hmod hd).le
  have hleft := V3.integral_kernel_difference_le K hK (μs i) x y (ε/4) hk
  have hright := V3.integral_kernel_difference_le K hK μ x y (ε/4) hk
  have hc := hi y (hA.mem_toFinset.mpr hy)
  have ht₁ := abs_sub_le (∫ t, K (x,t) ∂(μs i : Measure Segment))
    (∫ t, K (y,t) ∂(μs i : Measure Segment))
    (∫ t, K (x,t) ∂(μ : Measure Segment))
  have ht₂ := abs_sub_le (∫ t, K (y,t) ∂(μs i : Measure Segment))
    (∫ t, K (y,t) ∂(μ : Measure Segment))
    (∫ t, K (x,t) ∂(μ : Measure Segment))
  rw [abs_sub_comm (∫ t, K (y,t) ∂(μ : Measure Segment))] at ht₂
  linarith

theorem interval_mass_filter {ι : Type*} {l : Filter ι}
    (μs : ι → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs l (𝓝 μ)) (a b : ℝ)
    (hbd : (μ : Measure Segment) (frontier (sourceInterval a b)) = 0) :
    Tendsto (fun i => (μs i : Measure Segment).real (sourceInterval a b)) l
      (𝓝 ((μ : Measure Segment).real (sourceInterval a b))) :=
  (ENNReal.continuousAt_toReal (measure_ne_top (μ : Measure Segment) _)).tendsto.comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hbd)

theorem rampGap_filter {ι : Type*} {l : Filter ι}
    (μs : ι → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs l (𝓝 μ)) (a b : ℝ)
    (hbd : (μ : Measure Segment) (frontier (sourceInterval a b)) = 0) (k : ℕ) :
    Tendsto (fun i => rampGap (μs i) a b k) l (𝓝 (rampGap μ a b k)) := by
  let f : C(Segment,ℝ) := ⟨intervalRamp a b k,continuous_intervalRamp a b k⟩
  exact (interval_mass_filter μs μ hμ a b hbd).sub
    (((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ).comp hμ)

theorem weak_restricted_kernel_filter {ι : Type*} {l : Filter ι}
    (μs : ι → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs l (𝓝 μ)) (a b : ℝ)
    (hbd : (μ : Measure Segment) (frontier (sourceInterval a b)) = 0)
    (K : Segment × Segment → ℝ) (hK : Continuous K) :
    ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ x : Segment,
      |(∫ t in sourceInterval a b, K (x,t) ∂(μs i : Measure Segment)) -
        ∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment)| < ε := by
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (univ : Set (Segment × Segment))).exists_bound_of_continuousOn hK.continuousOn
  let M := max 1 C
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM (x t : Segment) : |K (x,t)| ≤ M := by
    have hn : |K (x,t)| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (x,t) (mem_univ _)
    exact hn.trans (le_max_right _ _)
  intro ε hε
  obtain ⟨k,hk⟩ := ((rampGap_tendsto_zero μ a b).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < ε/(8*M)))).exists
  have hstep : ε/(8*M) < ε/(4*M) := by
    apply div_lt_div_of_pos_left hε (by positivity)
    nlinarith
  have hramp := (rampGap_filter μs μ hμ a b hbd k).eventually
    (gt_mem_nhds (hk.trans hstep))
  let K' : Segment × Segment → ℝ := fun z => K z*intervalRamp a b k z.2
  have hK' : Continuous K' := hK.mul ((continuous_intervalRamp a b k).comp continuous_snd)
  filter_upwards [hramp,weak_kernel_filter μs μ hμ K' hK' (ε/4) (by positivity)] with i hi hki
  intro x
  have hl := restricted_kernel_ramp_error (μs i) K hK M hM a b k x
  have hr := restricted_kernel_ramp_error μ K hK M hM a b k x
  have hl' : M*rampGap (μs i) a b k < ε/4 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 4*M)).mp hi
    nlinarith
  have hr' : M*rampGap μ a b k < ε/8 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8*M)).mp hk
    nlinarith
  have ht₁ := abs_sub_le
    (∫ t in sourceInterval a b, K (x,t) ∂(μs i : Measure Segment))
    (∫ t, K' (x,t) ∂(μs i : Measure Segment))
    (∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment))
  have ht₂ := abs_sub_le
    (∫ t, K' (x,t) ∂(μs i : Measure Segment))
    (∫ t, K' (x,t) ∂(μ : Measure Segment))
    (∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment))
  rw [abs_sub_comm (∫ t, K' (x,t) ∂(μ : Measure Segment))] at ht₂
  have hkx := hki x
  change |(∫ t in sourceInterval a b, K (x,t) ∂(μs i : Measure Segment)) -
    ∫ t, K' (x,t) ∂(μs i : Measure Segment)| ≤ M*rampGap (μs i) a b k at hl
  change |(∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment)) -
    ∫ t, K' (x,t) ∂(μ : Measure Segment)| ≤ M*rampGap μ a b k at hr
  linarith

theorem weak_exterior_kernel_filter {ι : Type*} {l : Filter ι}
    (μs : ι → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs l (𝓝 μ)) (a b : ℝ)
    (hbd : (μ : Measure Segment) (frontier (sourceInterval a b)) = 0)
    (K : Segment × Segment → ℝ) (hK : Continuous K) :
    ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ x : Segment,
      |(∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μs i : Measure Segment)) -
        ∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment)| < ε := by
  intro ε hε
  filter_upwards [weak_kernel_filter μs μ hμ K hK (ε/2) (half_pos hε),
    weak_restricted_kernel_filter μs μ hμ a b hbd K hK (ε/2) (half_pos hε)] with i hi hj
  intro x
  have hint (ν : ProbabilityMeasure Segment) : Integrable (fun t => K (x,t)) (ν : Measure Segment) :=
    (hK.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he₁ := integral_add_compl (measurableSet_sourceInterval a b) (hint (μs i))
  have he₂ := integral_add_compl (measurableSet_sourceInterval a b) (hint μ)
  have heq : (∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μs i : Measure Segment)) -
      ∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment) =
      ((∫ t, K (x,t) ∂(μs i : Measure Segment)) - ∫ t, K (x,t) ∂(μ : Measure Segment)) -
      ((∫ t in sourceInterval a b, K (x,t) ∂(μs i : Measure Segment)) -
        ∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment)) := by linarith
  rw [heq]
  exact (abs_sub _ _).trans_lt (by linarith [hi x,hj x])


end Erdos1152.V5
