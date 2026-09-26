import Erdos1152.V4.BoundaryKernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Boundary continuity and a positive local source-mass obstruction

The boundary value is the genuine integrable logarithmic section. Its
continuity is a dominated-convergence proof. Combined with the actual disk
Harnack bound and the dyadic derivative estimate, a minimum point cannot
have arbitrarily small linear source density at every sufficiently small
scale. None of these statements assumes the desired positive-density result.
-/

open MeasureTheory Set Filter Topology Complex Metric
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def verticalLog (d y : ℝ) : ℝ := (1 / 2 : ℝ) * Real.log (d^2 + y^2)

noncomputable def verticalRegular (μ : ProbabilityMeasure Segment) (x y : ℝ) : ℝ :=
  ∫ t : Segment, verticalLog (x - (t : ℝ)) y ∂(μ : Measure Segment)

@[simp] theorem verticalLog_zero (d : ℝ) : verticalLog d 0 = logProfile d := by
  simp only [verticalLog, show (0 : ℝ)^2 = 0 by norm_num, add_zero,
    Real.log_pow, logProfile, Real.log_abs]
  ring

@[simp] theorem verticalRegular_zero (μ : ProbabilityMeasure Segment) (x : ℝ) :
    verticalRegular μ x 0 = potential μ x := by
  simp only [verticalRegular, verticalLog_zero, potential]

theorem verticalLog_eq_log_norm (x y : ℝ) (t : Segment) :
    verticalLog (x - (t : ℝ)) y = Real.log ‖verticalPoint x y - ((t : ℝ) : ℂ)‖ := by
  have hn : ‖verticalPoint x y - ((t : ℝ) : ℂ)‖^2 = (x - (t : ℝ))^2 + y^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, verticalPoint_re, verticalPoint_im]
    ring
  unfold verticalLog
  rw [← hn, Real.log_pow]
  ring

theorem verticalRegular_eq (μ : ProbabilityMeasure Segment) (x y : ℝ) (hy : 0 < y) :
    verticalRegular μ x y = regularPotential μ (verticalPoint x y) := by
  rw [regularPotential_eq_integral_log_norm μ _ (by simpa using hy)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (verticalLog_eq_log_norm x y)

theorem integrable_verticalLog (μ : ProbabilityMeasure Segment) (x y : ℝ) (hy : 0 < y) :
    Integrable (fun t : Segment => verticalLog (x - (t : ℝ)) y) (μ : Measure Segment) := by
  simp_rw [verticalLog_eq_log_norm]
  exact integrable_log_norm_section μ _ (by simpa using hy)

theorem hasDerivAt_verticalLog (d y : ℝ) (hy : 0 < y) :
    HasDerivAt (verticalLog d) (y / (d^2 + y^2)) y := by
  have hden : d^2 + y^2 ≠ 0 := (by positivity : 0 < d^2 + y^2).ne'
  convert! ((((hasDerivAt_id y).pow 2).const_add (d^2)).log hden).const_mul (1 / 2 : ℝ)
    using 1 <;> simp only [verticalLog, Pi.pow_apply, id_eq, pow_one, mul_one] <;> ring

/-- Derivative at every positive height, computed under the source integral. -/
theorem hasDerivAt_verticalRegular (μ : ProbabilityMeasure Segment) (x y : ℝ) (hy : 0 < y) :
    HasDerivAt (verticalRegular μ x)
      (∫ t, poissonSlope x y t ∂(μ : Measure Segment)) y := by
  have hb : ball y (y / 2) ∈ 𝓝 y := ball_mem_nhds y (by positivity)
  have hpos (v : ℝ) (hv : v ∈ ball y (y / 2)) : y / 2 < v := by
    have hdist : |v - y| < y / 2 := by simpa only [mem_ball, Real.dist_eq] using hv
    linarith [(abs_lt.mp hdist).1]
  unfold verticalRegular
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun v t => poissonSlope x v t) (bound := fun _ : Segment => 2 / y)
    hb ?_ (integrable_verticalLog μ x y hy)
    (integrable_poissonSlope (μ : Measure Segment) x y hy).aestronglyMeasurable
    ?_ (integrable_const _) ?_).2
  · filter_upwards [hb] with v hv
    exact (integrable_verticalLog μ x v (by linarith [hpos v hv])).aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t v hv
    have hv0 : 0 < v := by linarith [hpos v hv]
    rw [Real.norm_eq_abs, abs_of_nonneg (poissonSlope_nonneg x v hv0.le t)]
    have hh : poissonSlope x v t ≤ 1 / v := by
      unfold poissonSlope
      apply (div_le_div_iff₀ (by positivity) hv0).mpr
      nlinarith [sq_nonneg (x - (t : ℝ))]
    calc
      _ ≤ 1 / v := hh
      _ ≤ 1 / (y / 2) := one_div_le_one_div_of_le (by positivity) (hpos v hv).le
      _ = 2 / y := by field_simp
  · apply Filter.Eventually.of_forall
    intro t v hv
    exact hasDerivAt_verticalLog (x - (t : ℝ)) v (by linarith [hpos v hv])

/-- A single integrable majorant at the singular boundary. -/
theorem verticalLog_abs_bound (d y : ℝ) (hd : d ≠ 0)
    (hd2 : |d| ≤ 2) (hy : |y| ≤ 1) :
    |verticalLog d y| ≤ |logProfile d| + Real.log 3 := by
  have hdpos : 0 < d^2 := sq_pos_of_ne_zero hd
  have hlower : logProfile d ≤ verticalLog d y := by
    have hh := Real.log_le_log hdpos (by nlinarith [sq_nonneg y] : d^2 ≤ d^2 + y^2)
    have h0 : (1 / 2 : ℝ) * Real.log (d^2) = logProfile d := by
      rw [Real.log_pow, logProfile, Real.log_abs]
      ring
    unfold verticalLog
    linarith
  have hu : d^2 + y^2 ≤ 9 := by
    have hd' := (abs_le.mp hd2)
    have hy' := (abs_le.mp hy)
    nlinarith [sq_nonneg (2 - d), sq_nonneg (2 + d), sq_nonneg (1 - y), sq_nonneg (1 + y)]
  have hupper : verticalLog d y ≤ Real.log 3 := by
    have hh := Real.log_le_log (by positivity : 0 < d^2 + y^2) hu
    have h9 : Real.log (9 : ℝ) = 2 * Real.log 3 := by
      calc
        Real.log (9 : ℝ) = Real.log ((3 : ℝ)^2) := by norm_num
        _ = _ := by rw [Real.log_pow]; norm_num
    rw [h9] at hh
    unfold verticalLog
    linarith
  apply abs_le.mpr
  have h3 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  exact ⟨by linarith [neg_abs_le (logProfile d)], by linarith [abs_nonneg (logProfile d)]⟩

/-- This theorem uses the source-section integrability and diagonal facts
already obtained Lebesgue a.e. from Fubini; it does not assume a pointwise
convergence of potentials at a selected minimum. -/
theorem continuousAt_verticalRegular_zero (μ : ProbabilityMeasure Segment)
    (x : Segment)
    (hi : Integrable (fun t : Segment => logProfile ((x : ℝ) - (t : ℝ))) (μ : Measure Segment))
    (hd : ∀ᵐ t : Segment ∂(μ : Measure Segment), (x : ℝ) ≠ (t : ℝ)) :
    ContinuousAt (verticalRegular μ x) 0 := by
  unfold verticalRegular
  apply tendsto_integral_filter_of_dominated_convergence
    (fun t : Segment => |logProfile ((x : ℝ) - (t : ℝ))| + Real.log 3)
  · apply Filter.Eventually.of_forall
    intro y
    have hm : Measurable (fun t : Segment => verticalLog ((x : ℝ) - (t : ℝ)) y) := by
      unfold verticalLog
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with y hy
    filter_upwards [hd] with t ht
    rw [Real.norm_eq_abs]
    apply verticalLog_abs_bound _ y (sub_ne_zero.mpr ht)
    · apply abs_le.mpr
      constructor <;> linarith [x.property.1, x.property.2, t.property.1, t.property.2]
    · have hy' : |y| < 1 := by
        simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using hy
      exact hy'.le
  · exact hi.abs.add (integrable_const _)
  · filter_upwards [hd] with t ht
    unfold verticalLog
    apply ContinuousAt.const_mul
    apply ContinuousAt.log
    · fun_prop
    · simpa only [pow_two, mul_zero, add_zero] using
        (sq_pos_of_ne_zero (sub_ne_zero.mpr ht)).ne'

noncomputable def densityObstructionConstant : ℝ := Real.log 2 / 512

theorem densityObstructionConstant_pos : 0 < densityObstructionConstant :=
  div_pos (Real.log_pos (by norm_num)) (by norm_num)

/-- A true minimum point has a quantitative source-mass obstruction at every
scale. This is a proved local statement, not an assumed density interface. -/
theorem minimum_has_large_source_ball (μ : ProbabilityMeasure Segment)
    (x : Segment) (A : ℝ) (hA : potentialFloor μ = (A : EReal))
    (hxA : potential μ x = A)
    (hi : Integrable (fun t : Segment => logProfile ((x : ℝ) - (t : ℝ))) (μ : Measure Segment))
    (hd : ∀ᵐ t : Segment ∂(μ : Measure Segment), (x : ℝ) ≠ (t : ℝ))
    (R : ℝ) (hR : 0 < R) :
    ∃ r, 0 < r ∧ r ≤ R ∧
      ENNReal.ofReal (densityObstructionConstant * r) <
        (μ : Measure Segment) (sourceBall x r) := by
  by_contra! hsmall
  let c := densityObstructionConstant
  have hc : 0 < c := densityObstructionConstant_pos
  let y := min 1 (c * R^2)
  have hy : 0 < y := lt_min (by norm_num) (by positivity)
  have hy1 : y ≤ 1 := min_le_left _ _
  have hyc : y / R^2 ≤ c := by
    apply (div_le_iff₀ (by positivity : 0 < R^2)).mpr
    exact min_le_right _ _
  have hcont : ContinuousOn (verticalRegular μ x) (Icc 0 y) := by
    intro z hz
    rcases eq_or_lt_of_le hz.1 with he | hp
    · subst z
      exact (continuousAt_verticalRegular_zero μ x hi hd).continuousWithinAt
    · exact (hasDerivAt_verticalRegular μ x z hp).continuousAt.continuousWithinAt
  obtain ⟨z, hz, hder⟩ := exists_hasDerivAt_eq_slope
    (verticalRegular μ x) (fun z => ∫ t, poissonSlope x z t ∂(μ : Measure Segment))
    hy hcont (fun z hz => hasDerivAt_verticalRegular μ x z hz.1)
  have hupper := poissonSlope_integral_le_local μ x z R c hz.1 hR hc.le hsmall
  have hzsmall : z / R^2 ≤ c :=
    (div_le_div_of_nonneg_right hz.2.le (sq_nonneg R)).trans hyc
  have hylow := regularPotential_boundary_lower μ A (by rw [hA]) x y hy hy1
  rw [← verticalRegular_eq μ x y hy] at hylow
  rw [verticalRegular_zero, hxA, sub_zero] at hder
  have hl : (Real.log 2 / 16) ≤
      (verticalRegular μ x y - A) / y := (le_div_iff₀ hy).mpr hylow
  rw [← hder] at hl
  have hcdef : 32 * c = Real.log 2 / 16 := by dsimp [c, densityObstructionConstant]; ring
  nlinarith

end Erdos1152.V4
