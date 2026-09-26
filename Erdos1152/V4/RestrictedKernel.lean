import Erdos1152.V4.AtomFree
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Weak convergence restricted to a genuine local interval

A continuous interior ramp, together with Portmanteau convergence of the
interval mass, yields uniform convergence of restricted continuous kernels.
No convergence of restricted integrals is assumed.  This supplies the fixed-h
local-field passage; it is separate from the later h → 0 tangent-measure limit.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def sourceInterval (a b : ℝ) : Set Segment :=
  Subtype.val ⁻¹' Ioo a b

noncomputable def intervalRamp (a b : ℝ) (k : ℕ) (t : Segment) : ℝ :=
  min 1 ((k+1 : ℝ) * max 0 (min ((t : ℝ)-a) (b-(t : ℝ))))

@[measurability] theorem measurableSet_sourceInterval (a b : ℝ) :
    MeasurableSet (sourceInterval a b) :=
  measurable_subtype_coe measurableSet_Ioo

@[continuity] theorem continuous_intervalRamp (a b : ℝ) (k : ℕ) :
    Continuous (intervalRamp a b k) := by
  unfold intervalRamp
  fun_prop

theorem intervalRamp_nonneg (a b : ℝ) (k : ℕ) (t : Segment) :
    0 ≤ intervalRamp a b k t := by
  unfold intervalRamp
  positivity

theorem intervalRamp_le_one (a b : ℝ) (k : ℕ) (t : Segment) :
    intervalRamp a b k t ≤ 1 := min_le_left _ _

theorem intervalRamp_eq_zero {a b : ℝ} (k : ℕ) {t : Segment}
    (ht : t ∉ sourceInterval a b) : intervalRamp a b k t = 0 := by
  have hd : min ((t : ℝ)-a) (b-(t : ℝ)) ≤ 0 := by
    by_contra! hd
    exact ht ⟨by linarith [(lt_min_iff.mp hd).1], by linarith [(lt_min_iff.mp hd).2]⟩
  simp only [intervalRamp, max_eq_left hd, mul_zero, min_eq_right zero_le_one]

theorem intervalRamp_le_indicator (a b : ℝ) (k : ℕ) (t : Segment) :
    intervalRamp a b k t ≤ (sourceInterval a b).indicator (fun _ => (1 : ℝ)) t := by
  by_cases ht : t ∈ sourceInterval a b
  · simpa only [Set.indicator_of_mem ht] using intervalRamp_le_one a b k t
  · simp only [Set.indicator_of_notMem ht, intervalRamp_eq_zero k ht, le_refl]

theorem intervalRamp_tendsto (a b : ℝ) (t : Segment) :
    Tendsto (fun k => intervalRamp a b k t) atTop
      (𝓝 ((sourceInterval a b).indicator (fun _ => (1 : ℝ)) t)) := by
  by_cases ht : t ∈ sourceInterval a b
  · let d : ℝ := min ((t : ℝ)-a) (b-(t : ℝ))
    have hd : 0 < d := lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2)
    obtain ⟨K, hK⟩ := exists_nat_gt (1/d)
    have he : ∀ᶠ k in atTop, intervalRamp a b k t = 1 := by
      apply eventually_atTop.mpr
      refine ⟨K, ?_⟩
      intro k hk
      have hcast : (K : ℝ) ≤ k := by exact_mod_cast hk
      have hprod : 1 ≤ (k+1 : ℝ)*d := by
        have hKd := (div_lt_iff₀ hd).mp hK
        nlinarith
      change min 1 ((k+1 : ℝ) * max 0 d) = 1
      rw [max_eq_right hd.le, min_eq_left hprod]
    simpa only [Set.indicator_of_mem ht] using
      (tendsto_const_nhds.congr' (he.mono fun _ hk => hk.symm) :
        Tendsto (fun k => intervalRamp a b k t) atTop (𝓝 1))
  · simpa only [Set.indicator_of_notMem ht, intervalRamp_eq_zero _ ht] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem intervalRamp_integrable (μ : ProbabilityMeasure Segment) (a b : ℝ) (k : ℕ) :
    Integrable (intervalRamp a b k) (μ : Measure Segment) :=
  (continuous_intervalRamp a b k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_intervalRamp_tendsto (μ : ProbabilityMeasure Segment) (a b : ℝ) :
    Tendsto (fun k => ∫ t, intervalRamp a b k t ∂(μ : Measure Segment)) atTop
      (𝓝 ((μ : Measure Segment).real (sourceInterval a b))) := by
  have ht := tendsto_integral_of_dominated_convergence (μ := (μ : Measure Segment))
    (fun _ : Segment => (1 : ℝ))
    (fun k => (continuous_intervalRamp a b k).aestronglyMeasurable)
    (integrable_const 1)
    (fun k => Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (intervalRamp_nonneg a b k t)]
      exact intervalRamp_le_one a b k t))
    (Filter.Eventually.of_forall (intervalRamp_tendsto a b))
  simpa only [integral_indicator (measurableSet_sourceInterval a b),
    setIntegral_const, smul_eq_mul, mul_one] using ht

noncomputable def rampGap (μ : ProbabilityMeasure Segment) (a b : ℝ) (k : ℕ) : ℝ :=
  (μ : Measure Segment).real (sourceInterval a b) - ∫ t, intervalRamp a b k t ∂(μ : Measure Segment)

theorem rampGap_nonneg (μ : ProbabilityMeasure Segment) (a b : ℝ) (k : ℕ) :
    0 ≤ rampGap μ a b k := by
  have hle := integral_mono (intervalRamp_integrable μ a b k)
    ((integrable_const (1 : ℝ)).indicator (measurableSet_sourceInterval a b))
    (intervalRamp_le_indicator a b k)
  simp only [integral_indicator (measurableSet_sourceInterval a b),
    setIntegral_const, smul_eq_mul, mul_one] at hle
  exact sub_nonneg.mpr hle

theorem rampGap_tendsto_zero (μ : ProbabilityMeasure Segment) (a b : ℝ) :
    Tendsto (rampGap μ a b) atTop (𝓝 0) := by
  have hc : Tendsto (fun _ : ℕ => (μ : Measure Segment).real (sourceInterval a b))
      atTop (𝓝 ((μ : Measure Segment).real (sourceInterval a b))) := tendsto_const_nhds
  change Tendsto (fun k => rampGap μ a b k) atTop (𝓝 0)
  simpa only [rampGap, sub_self] using
    hc.sub (integral_intervalRamp_tendsto μ a b)

/-- Endpoint atoms are absent in the finite-floor branch, so this is an actual
continuity set of the fixed weak limit. -/
theorem sourceInterval_null_frontier (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) {a b : ℝ} (hab : a < b) :
    (μ : Measure Segment) (frontier (sourceInterval a b)) = 0 := by
  apply measure_mono_null (continuous_subtype_val.frontier_preimage_subset (Ioo a b))
  rw [← realSource_apply μ _ (isClosed_frontier.measurableSet)]
  have hsub : frontier (Ioo a b) ⊆ ({a,b} : Set ℝ) := by
    intro x hx
    have hx' : x ∈ Icc a b ∧ x ∉ Ioo a b := by
      simpa only [frontier, closure_Ioo hab.ne, interior_Ioo, Set.mem_sdiff] using hx
    by_cases hxa : x = a
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hxa, true_or]
    · have hax : a < x := lt_of_le_of_ne hx'.1.1 (Ne.symm hxa)
      have hxb : x = b := le_antisymm hx'.1.2 (not_lt.mp (fun h => hx'.2 ⟨hax,h⟩))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, hxb, or_true]
  apply measure_mono_null hsub
  rw [show ({a,b} : Set ℝ) = {a} ∪ {b} by ext x; simp [or_comm]]
  exact measure_union_null
    (realSource_singleton_zero_of_floor_ne_bot μ hfloor a)
    (realSource_singleton_zero_of_floor_ne_bot μ hfloor b)

theorem weak_sourceInterval_mass (μs : ℕ → ProbabilityMeasure Segment)
    (μ : ProbabilityMeasure Segment) (hμ : Tendsto μs atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) {a b : ℝ} (hab : a < b) :
    Tendsto (fun n => (μs n : Measure Segment).real (sourceInterval a b)) atTop
      (𝓝 ((μ : Measure Segment).real (sourceInterval a b))) := by
  exact (ENNReal.continuousAt_toReal (measure_ne_top (μ : Measure Segment) _)).tendsto.comp
    (ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ
      (sourceInterval_null_frontier μ hfloor hab))

theorem weak_rampGap (μs : ℕ → ProbabilityMeasure Segment)
    (μ : ProbabilityMeasure Segment) (hμ : Tendsto μs atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) {a b : ℝ} (hab : a < b) (k : ℕ) :
    Tendsto (fun n => rampGap (μs n) a b k) atTop (𝓝 (rampGap μ a b k)) := by
  let f : C(Segment, ℝ) := ⟨intervalRamp a b k, continuous_intervalRamp a b k⟩
  exact (weak_sourceInterval_mass μs μ hμ hfloor hab).sub
    (((ProbabilityMeasure.continuous_integral_continuousMap f).tendsto μ).comp hμ)

private theorem continuous_section_integrable (μ : ProbabilityMeasure Segment)
    (K : Segment × Segment → ℝ) (hK : Continuous K) (x : Segment) :
    Integrable (fun t => K (x,t)) (μ : Measure Segment) :=
  (hK.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- A weighted ramp error is controlled by its actual scalar mass deficit. -/
theorem restricted_kernel_ramp_error (μ : ProbabilityMeasure Segment)
    (K : Segment × Segment → ℝ) (hK : Continuous K) (M : ℝ)
    (hM : ∀ x t : Segment, |K (x,t)| ≤ M) (a b : ℝ) (k : ℕ) (x : Segment) :
    |(∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment)) -
      ∫ t, K (x,t)*intervalRamp a b k t ∂(μ : Measure Segment)| ≤ M*rampGap μ a b k := by
  let E := sourceInterval a b
  let r := intervalRamp a b k
  let e : Segment → ℝ := fun t => E.indicator (fun _ => (1 : ℝ)) t - r t
  have he0 (t) : 0 ≤ e t := sub_nonneg.mpr (intervalRamp_le_indicator a b k t)
  have hi := continuous_section_integrable μ K hK x
  have hir : Continuous (fun t : Segment => K (x,t)*r t) :=
    (hK.comp (continuous_const.prodMk continuous_id)).mul (continuous_intervalRamp a b k)
  have hip : Integrable (fun t => K (x,t)*r t) (μ : Measure Segment) :=
    hir.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hie : Integrable e (μ : Measure Segment) :=
    ((integrable_const (1 : ℝ)).indicator (measurableSet_sourceInterval a b)).sub
      (intervalRamp_integrable μ a b k)
  have hidentity (t : Segment) :
      E.indicator (fun t => K (x,t)) t - K (x,t)*r t = K (x,t)*e t := by
    by_cases ht : t ∈ E
    · simp only [e, Set.indicator_of_mem ht]
      ring
    · simp only [e, Set.indicator_of_notMem ht]
      ring
  rw [← integral_indicator (measurableSet_sourceInterval a b),
    ← integral_sub (hi.indicator (measurableSet_sourceInterval a b)) hip]
  change |∫ t, (E.indicator (fun t => K (x,t)) t - K (x,t)*r t) ∂(μ : Measure Segment)| ≤
    M*rampGap μ a b k
  simp_rw [hidentity]
  calc
    _ ≤ ∫ t, |K (x,t)*e t| ∂(μ : Measure Segment) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun t => K (x,t)*e t)
    _ ≤ ∫ t, M*e t ∂(μ : Measure Segment) := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (hie.const_mul M)
      filter_upwards with t
      rw [abs_mul, abs_of_nonneg (he0 t)]
      exact mul_le_mul_of_nonneg_right (hM x t) (he0 t)
    _ = M*rampGap μ a b k := by
      rw [integral_const_mul]
      congr 1
      rw [integral_sub ((integrable_const (1 : ℝ)).indicator (measurableSet_sourceInterval a b))
        (intervalRamp_integrable μ a b k)]
      simp only [rampGap, integral_indicator (measurableSet_sourceInterval a b),
        setIntegral_const, smul_eq_mul, mul_one, r, E]

/-- The restricted-kernel convergence is now proved, including uniformity in
all moving centers represented by the compact parameter x. -/
theorem weak_convergence_uniform_restricted_kernel
    (μs : ℕ → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hfloor : potentialFloor μ ≠ ⊥)
    (K : Segment × Segment → ℝ) (hK : Continuous K) {a b : ℝ} (hab : a < b) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x : Segment,
      |(∫ t in sourceInterval a b, K (x,t) ∂(μs n : Measure Segment)) -
        ∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment)| < ε := by
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Segment × Segment))).exists_bound_of_continuousOn hK.continuousOn
  let M := max 1 C
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM (x t : Segment) : |K (x,t)| ≤ M := by
    have hb : |K (x,t)| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (x,t) (Set.mem_univ _)
    exact hb.trans (le_max_right _ _)
  intro ε hε
  have hsmall := (rampGap_tendsto_zero μ a b).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < ε/(8*M)))
  obtain ⟨k,hk⟩ := hsmall.exists
  have hmargin : ε/(8*M) < ε/(4*M) := by
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_pos hε hM0]
  have hnsmall := (weak_rampGap μs μ hμ hfloor hab k).eventually
    (gt_mem_nhds (hk.trans hmargin))
  let K' : Segment × Segment → ℝ := fun z => K z * intervalRamp a b k z.2
  have hK' : Continuous K' := hK.mul ((continuous_intervalRamp a b k).comp continuous_snd)
  have happrox := V3.weak_convergence_uniform_kernel μs μ hμ K' hK' (ε/4) (by positivity)
  filter_upwards [hnsmall,happrox] with n hn hnap
  intro x
  have hleft := restricted_kernel_ramp_error (μs n) K hK M hM a b k x
  have hright := restricted_kernel_ramp_error μ K hK M hM a b k x
  have hmleft : M*rampGap (μs n) a b k < ε/4 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 4*M)).mp hn
    nlinarith
  have hmright : M*rampGap μ a b k < ε/8 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 8*M)).mp hk
    nlinarith
  have hc := hnap x
  have ht1 := abs_sub_le
    (∫ t in sourceInterval a b, K (x,t) ∂(μs n : Measure Segment))
    (∫ t, K' (x,t) ∂(μs n : Measure Segment))
    (∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment))
  have ht2 := abs_sub_le
    (∫ t, K' (x,t) ∂(μs n : Measure Segment))
    (∫ t, K' (x,t) ∂(μ : Measure Segment))
    (∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment))
  rw [abs_sub_comm (∫ t, K' (x,t) ∂(μ : Measure Segment))] at ht2
  change |(∫ t in sourceInterval a b, K (x,t) ∂(μs n : Measure Segment)) -
    ∫ t, K' (x,t) ∂(μs n : Measure Segment)| ≤ M*rampGap (μs n) a b k at hleft
  change |(∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment)) -
    ∫ t, K' (x,t) ∂(μ : Measure Segment)| ≤ M*rampGap μ a b k at hright
  linarith

/-- Exterior kernels are a difference of the full and interior integrals.
This includes all endpoint and exterior node contributions. -/
theorem weak_convergence_uniform_exterior_kernel
    (μs : ℕ → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs atTop (𝓝 μ)) (hfloor : potentialFloor μ ≠ ⊥)
    (K : Segment × Segment → ℝ) (hK : Continuous K) {a b : ℝ} (hab : a < b) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x : Segment,
      |(∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μs n : Measure Segment)) -
        ∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment)| < ε := by
  intro ε hε
  filter_upwards [V3.weak_convergence_uniform_kernel μs μ hμ K hK (ε/2) (half_pos hε),
    weak_convergence_uniform_restricted_kernel μs μ hμ hfloor K hK hab (ε/2) (half_pos hε)] with n hn hi
  intro x
  have he₁ := integral_add_compl (measurableSet_sourceInterval a b)
    (continuous_section_integrable (μs n) K hK x)
  have he₂ := integral_add_compl (measurableSet_sourceInterval a b)
    (continuous_section_integrable μ K hK x)
  have hbound := abs_sub_le
    ((∫ t, K (x,t) ∂(μs n : Measure Segment)) - ∫ t, K (x,t) ∂(μ : Measure Segment))
    0
    ((∫ t in sourceInterval a b, K (x,t) ∂(μs n : Measure Segment)) -
      ∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment))
  have hid : (∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μs n : Measure Segment)) -
      ∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment) =
      ((∫ t, K (x,t) ∂(μs n : Measure Segment)) - ∫ t, K (x,t) ∂(μ : Measure Segment)) -
      ((∫ t in sourceInterval a b, K (x,t) ∂(μs n : Measure Segment)) -
        ∫ t in sourceInterval a b, K (x,t) ∂(μ : Measure Segment)) := by linarith
  rw [hid]
  have hsum := add_lt_add (hn x) (hi x)
  simp only [sub_zero, zero_sub, abs_neg] at hbound
  linarith

end Erdos1152.V4
