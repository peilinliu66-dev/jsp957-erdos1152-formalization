import Erdos1152.V4.MinimumPrinciple
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions

/-!
# Actual upper-half-plane regularization of the logarithmic potential

The holomorphic function is the integral of the principal complex logarithm,
whose slit never meets an upper-half-plane source difference. Its derivative
and harmonicity are proved from the compact source measure. In particular no
Poisson representation or harmonicity is an additional input.
-/

open MeasureTheory Set Filter Topology Complex InnerProductSpace Metric
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def holPotential (μ : ProbabilityMeasure Segment) (z : ℂ) : ℂ :=
  ∫ t : Segment, Complex.log (z - ((t : ℝ) : ℂ)) ∂(μ : Measure Segment)

noncomputable def regularPotential (μ : ProbabilityMeasure Segment) (z : ℂ) : ℝ :=
  (holPotential μ z).re

def upperHalf : Set ℂ := {z | 0 < z.im}

theorem isOpen_upperHalf : IsOpen upperHalf :=
  isOpen_lt continuous_const Complex.continuous_im

theorem upper_source_slit (z : ℂ) (hz : 0 < z.im) (t : Segment) :
    z - ((t : ℝ) : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inr (by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hz.ne')

theorem upper_source_ne_zero (z : ℂ) (hz : 0 < z.im) (t : Segment) :
    z - ((t : ℝ) : ℂ) ≠ 0 := by
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at hi
  exact hz.ne' hi

theorem continuous_complexLog_section (μ : ProbabilityMeasure Segment)
    (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun t : Segment => Complex.log (z - ((t : ℝ) : ℂ))) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc : Continuous (fun t : Segment => z - ((t : ℝ) : ℂ)) :=
    continuous_const.sub (Complex.continuous_ofReal.comp continuous_subtype_val)
  exact (Complex.hasDerivAt_log (upper_source_slit z hz t)).continuousAt.comp
    (f := fun t : Segment => z - ((t : ℝ) : ℂ)) (x := t) hc.continuousAt

theorem integrable_complexLog_section (μ : ProbabilityMeasure Segment)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun t : Segment => Complex.log (z - ((t : ℝ) : ℂ))) (μ : Measure Segment) :=
  (continuous_complexLog_section μ z hz).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem continuous_inverse_section (z : ℂ) (hz : 0 < z.im) :
    Continuous (fun t : Segment => (z - ((t : ℝ) : ℂ))⁻¹) := by
  exact (continuous_const.sub (Complex.continuous_ofReal.comp continuous_subtype_val)).inv₀
    (fun t => upper_source_ne_zero z hz t)

theorem integrable_inverse_section (μ : ProbabilityMeasure Segment)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun t : Segment => (z - ((t : ℝ) : ℂ))⁻¹) (μ : Measure Segment) :=
  (continuous_inverse_section z hz).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem im_lower_of_mem_upper_ball {z w : ℂ} (hz : 0 < z.im)
    (hw : w ∈ ball z (z.im / 2)) : z.im / 2 < w.im := by
  have hd : ‖w - z‖ < z.im / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
  have hi := (abs_le.mp (Complex.abs_im_le_norm (w - z))).1
  simp only [Complex.sub_im] at hi
  linarith

/-- Differentiation is under the actual probability integral, uniformly in
all source points, with the integrable bound 2 / Im(z). -/
theorem hasDerivAt_holPotential (μ : ProbabilityMeasure Segment)
    (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (holPotential μ)
      (∫ t : Segment, (z - ((t : ℝ) : ℂ))⁻¹ ∂(μ : Measure Segment)) z := by
  have hball : ball z (z.im / 2) ∈ 𝓝 z := ball_mem_nhds z (by positivity)
  have hpos (w : ℂ) (hw : w ∈ ball z (z.im / 2)) : 0 < w.im :=
    (by positivity : (0 : ℝ) < z.im / 2).trans (im_lower_of_mem_upper_ball hz hw)
  change HasDerivAt (fun w => ∫ t : Segment, Complex.log (w - ((t : ℝ) : ℂ))
    ∂(μ : Measure Segment)) _ z
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun w (t : Segment) => (w - ((t : ℝ) : ℂ))⁻¹)
    (bound := fun _ : Segment => 2 / z.im) hball ?_
    (integrable_complexLog_section μ z hz)
    (integrable_inverse_section μ z hz).aestronglyMeasurable ?_
    (integrable_const _) ?_).2
  · filter_upwards [hball] with w hw
    exact (integrable_complexLog_section μ w (hpos w hw)).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t w hw
    have hnorm : z.im / 2 ≤ ‖w - ((t : ℝ) : ℂ)‖ := by
      have hi := Complex.abs_im_le_norm (w - ((t : ℝ) : ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero,
        abs_of_pos (hpos w hw)] at hi
      exact (im_lower_of_mem_upper_ball hz hw).le.trans hi
    calc
      ‖(w - ((t : ℝ) : ℂ))⁻¹‖ = 1 / ‖w - ((t : ℝ) : ℂ)‖ := by simp [one_div]
      _ ≤ 1 / (z.im / 2) := one_div_le_one_div_of_le (by positivity) hnorm
      _ = 2 / z.im := by field_simp
  · apply Filter.Eventually.of_forall
    intro t w hw
    simpa only [mul_one, Function.comp_def, id_eq] using
      (Complex.hasDerivAt_log (upper_source_slit w (hpos w hw) t)).comp w
        ((hasDerivAt_id w).sub_const ((t : ℝ) : ℂ))

theorem analyticOnNhd_holPotential (μ : ProbabilityMeasure Segment) :
    AnalyticOnNhd ℂ (holPotential μ) upperHalf := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_upperHalf
  intro z hz
  exact (hasDerivAt_holPotential μ z hz).differentiableAt.differentiableWithinAt

theorem harmonic_regularPotential (μ : ProbabilityMeasure Segment) :
    HarmonicOnNhd (regularPotential μ) upperHalf := by
  intro z hz
  exact (analyticOnNhd_holPotential μ z hz).harmonicAt_re

theorem harmonic_regularPotential_sub (μ : ProbabilityMeasure Segment) (A : ℝ) :
    HarmonicOnNhd (fun z => regularPotential μ z - A) upperHalf := by
  intro z hz
  simpa only [Pi.sub_apply, Complex.sub_re, Complex.ofReal_re, regularPotential] using
    ((analyticOnNhd_holPotential μ z hz).sub
      (analyticAt_const (v := (A : ℂ)))).harmonicAt_re

theorem regularPotential_eq_integral_log_norm (μ : ProbabilityMeasure Segment)
    (z : ℂ) (hz : 0 < z.im) :
    regularPotential μ z =
      ∫ t : Segment, Real.log ‖z - ((t : ℝ) : ℂ)‖ ∂(μ : Measure Segment) := by
  unfold regularPotential holPotential
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm
    Complex.reCLM (integrable_complexLog_section μ z hz)]
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.log_re]

theorem integrable_log_norm_section (μ : ProbabilityMeasure Segment)
    (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun t : Segment => Real.log ‖z - ((t : ℝ) : ℂ)‖) (μ : Measure Segment) := by
  simpa only [Function.comp_def, Complex.reCLM_apply, Complex.log_re] using
    Complex.reCLM.integrable_comp (integrable_complexLog_section μ z hz)

/-- The floor cannot exceed log 2: every source lies in [-1,1], including all
singular source measures. -/
theorem potentialFloor_le_log_two (μ : ProbabilityMeasure Segment) :
    potentialFloor μ ≤ (Real.log 2 : EReal) := by
  by_contra! hfloor
  obtain ⟨c, hc₁, hc₂⟩ := EReal.exists_between_coe_real hfloor
  have hlog : Real.log 2 < c := EReal.coe_lt_coe_iff.mp hc₁
  have hbound (t : Segment) : truncPotential μ 0 t ≤ Real.log 2 := by
    calc
      _ ≤ ∫ _z : Segment, Real.log 2 ∂(μ : Measure Segment) := by
        apply integral_mono (integrable_trunc_section μ 0 t) (integrable_const _)
        intro z
        apply Real.log_le_log (lt_of_lt_of_le (cutoff_pos 0) (le_max_left _ _))
        apply max_le
        · exact (cutoff_le_one 0).trans (by norm_num)
        · apply abs_le.mpr
          constructor <;> linarith [t.property.1, t.property.2, z.property.1, z.property.2]
      _ = Real.log 2 := by simp
  have hs : SourceLevel μ c := by
    refine ⟨0, ?_⟩
    have heq : {t : Segment | truncPotential μ 0 t < c} = Set.univ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact (hbound t).trans_lt hlog
    rw [heq]
    simp
  exact (not_le_of_gt hc₂) (sInf_le ⟨c, hs, rfl⟩)

/-- Every real lower bound for the true boundary floor remains a lower bound
for the actual harmonic regularization. There is no presumed Poisson integral
identity at the singular boundary. -/
theorem floor_le_regularPotential (μ : ProbabilityMeasure Segment) (A : ℝ)
    (hA : (A : EReal) ≤ potentialFloor μ) (z : ℂ) (hz : 0 < z.im) :
    A ≤ regularPotential μ z := by
  obtain ⟨k, hk⟩ := (cutoff_tendsto_zero.eventually (gt_mem_nhds hz)).exists
  have hlo : A ≤ truncPotential μ k z.re :=
    EReal.coe_le_coe_iff.mp (hA.trans ((potentialFloor_le_extended μ z.re).trans
      (iInf_le _ k)))
  apply hlo.trans
  rw [regularPotential_eq_integral_log_norm μ z hz]
  apply integral_mono (integrable_trunc_section μ k z.re) (integrable_log_norm_section μ z hz)
  intro t
  apply Real.log_le_log (lt_of_lt_of_le (cutoff_pos k) (le_max_left _ _))
  apply max_le
  · have hi := Complex.abs_im_le_norm (z - ((t : ℝ) : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_of_pos hz] at hi
    exact hk.le.trans hi
  · simpa only [Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm (z - ((t : ℝ) : ℂ))

theorem regularPotential_ge_log_height (μ : ProbabilityMeasure Segment)
    (z : ℂ) (hz : 0 < z.im) : Real.log z.im ≤ regularPotential μ z := by
  rw [regularPotential_eq_integral_log_norm μ z hz]
  calc
    Real.log z.im = ∫ _t : Segment, Real.log z.im ∂(μ : Measure Segment) := by simp
    _ ≤ _ := by
      apply integral_mono (integrable_const _) (integrable_log_norm_section μ z hz)
      intro t
      apply Real.log_le_log hz
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, abs_of_pos hz] using
        Complex.abs_im_le_norm (z - ((t : ℝ) : ℂ))

end Erdos1152.V4
