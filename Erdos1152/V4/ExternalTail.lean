import Erdos1152.V4.LocalMass

/-!
# Uniform remote-source control for the small-scale external field

A finite centered density implies a *global* linear ball-mass bound, with a
point-dependent constant. The already proved actual Poisson integral estimate
then gives an O(1/R) bound for the second-derivative contribution from sources
at distance at least R h. This is uniform in h and the moving center u.
No exterior-tail or mass-growth assumption is retained in the a.e. theorem.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V4

/-- Obtain the global ball bound from the actual density limit. The remote
part is bounded by the total probability mass, not an assumed global density. -/
theorem global_sourceBall_growth_of_density_limit (μ : ProbabilityMeasure Segment)
    (x w : ℝ) (hw : 0 ≤ w)
    (hd : Tendsto (fun r : ℝ => (realSource μ).real (closedBall x r)/(2*r))
      (𝓝[>] 0) (𝓝 w)) :
    ∃ C : ℝ, 0 < C ∧ ∀ r > 0,
      (μ : Measure Segment) (sourceBall x r) ≤ ENNReal.ofReal (C*r) := by
  have hs := hd.eventually (gt_mem_nhds (by linarith : w < w+1))
  obtain ⟨R,hR,hsmall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hs
  let C := max (2*(w+1)) (1/R)
  have hC : 0 < C := lt_of_lt_of_le (by linarith : 0 < 2*(w+1)) (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro r hr
  by_cases hrR : r < R
  · have hratio := hsmall (show r ∈ Ioo (0 : ℝ) R from ⟨hr,hrR⟩)
    have hm : (realSource μ).real (closedBall x r) ≤ C*r := by
      have hval := (div_lt_iff₀ (by positivity : 0 < 2*r)).mp hratio
      have hmul := mul_le_mul_of_nonneg_right (le_max_left (2*(w+1)) (1/R)) hr.le
      dsimp only [C]
      nlinarith
    calc
      _ ≤ realSource μ (closedBall x r) := sourceBall_le_closedBall μ x r
      _ = ENNReal.ofReal ((realSource μ).real (closedBall x r)) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (C*r) := ENNReal.ofReal_le_ofReal hm
  · have hRr : R ≤ r := le_of_not_gt hrR
    have hone : (1 : ℝ) ≤ C*r := by
      have hrdiv : 1 ≤ r/R := (le_div_iff₀ hR).mpr (by simpa using hRr)
      have hm := mul_le_mul_of_nonneg_right (le_max_right (2*(w+1)) (1/R)) hr.le
      have hrdiv' : (1 : ℝ) ≤ (1/R)*r := by
        simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hrdiv
      exact hrdiv'.trans hm
    calc
      _ ≤ 1 := by
        simpa using (measure_mono (Set.subset_univ (sourceBall x r)) :
          (μ : Measure Segment) (sourceBall x r) ≤ (μ : Measure Segment) Set.univ)
      _ ≤ ENNReal.ofReal (C*r) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hone

theorem ae_global_sourceBall_growth (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂(volume : Measure ℝ), ∃ C : ℝ, 0 < C ∧ ∀ r > 0,
      (μ : Measure Segment) (sourceBall x r) ≤ ENNReal.ofReal (C*r) := by
  filter_upwards [ae_sourceDensity_limit μ] with x hx
  exact global_sourceBall_growth_of_density_limit μ x (sourceDensity μ x)
    (sourceDensity_nonneg μ x) hx

noncomputable def remoteSecondIntegral (μ : ProbabilityMeasure Segment) (x h R u : ℝ) : ℝ :=
  ∫ t in (sourceBall x (R*h))ᶜ, h^2/(x+h*u-(t : ℝ))^2 ∂(μ : Measure Segment)

private theorem remoteSecond_pointwise (x h R u : ℝ) (hh : 0 < h) (hR : 2 ≤ R)
    (hu : |u| ≤ 1) (t : Segment) (ht : t ∉ sourceBall x (R*h)) :
    h^2/(x+h*u-(t : ℝ))^2 ≤ (8*h/R)*poissonSlope x (R*h) t := by
  let d := |x-(t : ℝ)|
  let q := x+h*u-(t : ℝ)
  have hR0 : 0 < R := by linarith
  have hd : R*h ≤ d := le_of_not_gt ht
  have hd0 : 0 < d := lt_of_lt_of_le (mul_pos hR0 hh) hd
  have hhu : |h*u| ≤ h := by
    rw [abs_mul,abs_of_pos hh]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu hh.le
  have htri : d ≤ |q|+h := by
    have he : x-(t : ℝ) = q-h*u := by dsimp [q]; ring
    dsimp only [d]
    rw [he]
    exact (abs_sub _ _).trans (add_le_add_right hhu _)
  have hqpos : 0 < |q| := by nlinarith
  have hq0 : 0 < q^2 := sq_pos_of_ne_zero (abs_pos.mp hqpos)
  have hq : d^2 ≤ 4*q^2 := by
    have hdq : d ≤ 2*|q| := by nlinarith
    have hs := mul_le_mul hdq hdq (le_of_lt hd0) (by positivity)
    nlinarith [sq_abs q]
  have hRh : (R*h)^2 ≤ d^2 := by
    exact (sq_le_sq₀ (by positivity) hd0.le).mpr hd
  calc
    h^2/q^2 ≤ 4*h^2/d^2 := by
      apply (div_le_div_iff₀ hq0 (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_left hq (sq_nonneg h)
      nlinarith
    _ ≤ 8*h^2/(d^2+(R*h)^2) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_left hRh (show 0 ≤ 4*h^2 by positivity)
      nlinarith
    _ = (8*h/R)*poissonSlope x (R*h) t := by
      unfold poissonSlope
      dsimp only [d]
      rw [sq_abs]
      field_simp

/-- The remote second derivative is bounded using an integral of the actual
Poisson kernel. No dyadic tail is left as an independent input. -/
theorem remoteSecondIntegral_le (μ : ProbabilityMeasure Segment) (x h R u C : ℝ)
    (hh : 0 < h) (hR : 2 ≤ R) (hu : |u| ≤ 1) (hC : 0 ≤ C)
    (hg : ∀ r > 0, (μ : Measure Segment) (sourceBall x r) ≤ ENNReal.ofReal (C*r)) :
    remoteSecondIntegral μ x h R u ≤ 64*C*h/R := by
  let «λ» : Measure Segment := (μ : Measure Segment).restrict (sourceBall x (R*h))ᶜ
  have hR0 : 0 < R := by linarith
  have hy : 0 < R*h := mul_pos hR0 hh
  have hpois := integrable_poissonSlope «λ» x (R*h) hy
  have hbound : ∀ᵐ (t : Segment) ∂«λ», |h^2/(x+h*u-(t : ℝ))^2| ≤
      (8*h/R)*poissonSlope x (R*h) t := by
    filter_upwards [ae_restrict_mem (measurable_sourceBall x (R*h)).compl] with t ht
    rw [abs_of_nonneg (by positivity : 0 ≤ h^2/(x+h*u-(t : ℝ))^2)]
    exact remoteSecond_pointwise x h R u hh hR hu t ht
  have hi : Integrable (fun t : Segment => h^2/(x+h*u-(t : ℝ))^2) «λ» :=
    (hpois.const_mul (8*h/R)).mono'
      (show AEStronglyMeasurable (fun t : Segment => h^2/(x+h*u-(t : ℝ))^2) «λ» from
        (show Measurable (fun t : Segment => h^2/(x+h*u-(t : ℝ))^2) by fun_prop).aestronglyMeasurable)
      (by simpa only [Real.norm_eq_abs] using hbound)
  have hlow := integral_mono_ae hi (hpois.const_mul (8*h/R))
    (hbound.mono (fun t ht => (le_abs_self _).trans ht))
  have hlam : ∀ r > 0, «λ» (sourceBall x r) ≤ ENNReal.ofReal (C*r) := by
    intro r hr
    change ((μ : Measure Segment).restrict (sourceBall x (R*h))ᶜ) (sourceBall x r) ≤ _
    rw [Measure.restrict_apply (measurable_sourceBall x r)]
    exact (measure_mono Set.inter_subset_left).trans (hg r hr)
  have hp := poissonSlope_integral_le_of_ball_growth «λ» x (R*h) C hy hC hlam
  unfold remoteSecondIntegral
  change (∫ t, h^2/(x+h*u-(t : ℝ))^2 ∂«λ») ≤ _
  calc
    _ ≤ ∫ t, (8*h/R)*poissonSlope x (R*h) t ∂«λ» := hlow
    _ = (8*h/R)*(∫ t, poissonSlope x (R*h) t ∂«λ») := integral_const_mul _ _
    _ ≤ (8*h/R)*(8*C) := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = 64*C*h/R := by ring

/-- At actual minimum points the normalized remote second-derivative tails
are O(1/R), uniformly in all small h and all moving centers |u|≤1. -/
theorem ae_minimum_remote_second_tail (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, x ∉ highPotentialRegion μ →
      ∃ K : ℝ, 0 < K ∧ ∀ᶠ h : ℝ in 𝓝[>] 0,
        0 < (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) ∧
        ∀ R : ℝ, 2 ≤ R → ∀ u : ℝ, |u| ≤ 1 →
          remoteSecondIntegral μ x h R u /
            (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) ≤ K/R := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_positive_CDF_derivative_on_minimum μ,ae_restrict_of_ae (ae_global_sourceBall_growth μ)]
      with x hx hgood hball
  intro hnot
  obtain ⟨hder,hw⟩ := hgood hnot
  obtain ⟨C,hC,hgrowth⟩ := hball
  let w := sourceDensity μ x
  have hw' : 0 < w := hw
  have hf : potentialFloor μ ≠ ⊥ := by
    intro hbot
    apply hnot
    rw [highPotentialRegion_of_floor_bot μ hbot]
    exact hx
  have hmass := tangent_interval_mass μ hf x w (-1) 1 (by norm_num) hder
  have hlarge := hmass.eventually (lt_mem_nhds (by dsimp only [w]; nlinarith : w < w*(1-(-1))))
  refine ⟨64*C/w,by positivity,?_⟩
  filter_upwards [self_mem_nhdsWithin,hlarge] with h hh hm
  have hh0 : 0 < h := hh
  simp only [mul_neg_one,mul_one,← sub_eq_add_neg] at hm
  have hml : w*h < (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) :=
    (lt_div_iff₀ hh).mp hm
  have hm0 : 0 < (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) :=
    (mul_pos hw' hh).trans hml
  refine ⟨hm0,?_⟩
  intro R hR u hu
  have hR0 : 0 < R := by linarith
  have htail := remoteSecondIntegral_le μ x h R u C hh hR hu hC.le hgrowth
  calc
    _ ≤ (64*C*h/R)/(μ : Measure Segment).real (sourceInterval (x-h) (x+h)) :=
      div_le_div_of_nonneg_right htail hm0.le
    _ ≤ (64*C*h/R)/(w*h) := div_le_div_of_nonneg_left (by positivity) (by positivity) hml.le
    _ = (64*C/w)/R := by field_simp [hh0.ne']

end Erdos1152.V4
