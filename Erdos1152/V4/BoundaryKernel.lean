import Erdos1152.V4.DiskHarnack

/-!
# The boundary Poisson derivative and zero-density control

A dyadic majorant reduces the derivative of the *actual* regularized
potential to centered source masses. This module does not assume an abstract
approximate-identity theorem. The constant 8 is deliberately nonoptimal.
-/

open MeasureTheory Set Filter Topology Complex Metric
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def poissonSlope (x y : ℝ) (t : Segment) : ℝ :=
  y / ((x - (t : ℝ)) ^ 2 + y ^ 2)

def sourceBall (x r : ℝ) : Set Segment := {t | |x - (t : ℝ)| < r}

theorem measurable_sourceBall (x r : ℝ) : MeasurableSet (sourceBall x r) :=
  (isOpen_lt ((continuous_const.sub continuous_subtype_val).abs) continuous_const).measurableSet

theorem poissonSlope_nonneg (x y : ℝ) (hy : 0 ≤ y) (t : Segment) :
    0 ≤ poissonSlope x y t := div_nonneg hy (by positivity)

theorem integrable_poissonSlope («λ» : Measure Segment) [IsFiniteMeasure «λ»]
    (x y : ℝ) (hy : 0 < y) : Integrable (poissonSlope x y) «λ» := by
  have hc : Continuous (poissonSlope x y) := by
    unfold poissonSlope
    apply continuous_const.div
      (((continuous_const.sub continuous_subtype_val).pow 2).add continuous_const)
    intro t
    have hh : 0 < (x - (t : ℝ)) ^ 2 + y ^ 2 := by positivity
    exact hh.ne'
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- One of the dyadic balls supplies a single adequate majorizing term. -/
theorem poissonSlope_dyadic_majorant (x y : ℝ) (hy : 0 < y) (t : Segment) :
    ENNReal.ofReal (poissonSlope x y t) ≤
      ∑' k : ℕ, (sourceBall x ((2 : ℝ)^k * y)).indicator
        (fun _ => ENNReal.ofReal ((4 / y) * (1 / 4 : ℝ)^k)) t := by
  let d := |x - (t : ℝ)|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hex : ∃ k : ℕ, d < (2 : ℝ)^k * y := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (d / y) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, (div_lt_iff₀ hy).mp hk⟩
  let k := Nat.find hex
  have hk : t ∈ sourceBall x ((2 : ℝ)^k * y) := Nat.find_spec hex
  have hscalar : poissonSlope x y t ≤ (4 / y) * (1 / 4 : ℝ)^k := by
    cases he : k with
    | zero =>
        have hden : 0 < (x - (t : ℝ))^2 + y^2 := by positivity
        have hsmall : poissonSlope x y t ≤ 1 / y := by
          unfold poissonSlope
          apply (div_le_div_iff₀ hden hy).mpr
          nlinarith [sq_nonneg (x - (t : ℝ))]
        simpa only [he, pow_zero, mul_one] using hsmall.trans
          (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 4) hy.le)
    | succ n =>
        have hnear : (2 : ℝ)^n * y ≤ d := by
          by_contra! hh
          have hmin : Nat.find hex ≤ n := Nat.find_min' hex hh
          have hkval : Nat.find hex = n + 1 := he
          omega
        have hsq : ((2 : ℝ)^n * y)^2 ≤ d^2 :=
          sq_le_sq₀ (by positivity) hd0 |>.mpr hnear
        have hden : 0 < (x - (t : ℝ))^2 + y^2 := by positivity
        have hsmall : poissonSlope x y t ≤ 1 / (y * ((2 : ℝ)^n)^2) := by
          unfold poissonSlope
          apply (div_le_div_iff₀ hden (by positivity)).mpr
          dsimp [d] at hsq
          rw [sq_abs] at hsq
          nlinarith [sq_nonneg y]
        have hpow : ((2 : ℝ)^n)^2 = (4 : ℝ)^n := by
          calc
            ((2 : ℝ)^n)^2 = ((2 : ℝ)^2)^n := by
              rw [← pow_mul, ← pow_mul]
              congr 1
              omega
            _ = (4 : ℝ)^n := by norm_num
        have heq : 1 / (y * ((2 : ℝ)^n)^2) = (4 / y) * (1 / 4 : ℝ)^(n+1) := by
          rw [hpow, pow_succ, one_div_pow]
          field_simp <;> ring
        simpa only [he, Nat.succ_eq_add_one, ← heq] using hsmall
  calc
    ENNReal.ofReal (poissonSlope x y t) ≤
        ENNReal.ofReal ((4 / y) * (1 / 4 : ℝ)^k) := ENNReal.ofReal_le_ofReal hscalar
    _ = (sourceBall x ((2 : ℝ)^k * y)).indicator
        (fun _ => ENNReal.ofReal ((4 / y) * (1 / 4 : ℝ)^k)) t :=
      (Set.indicator_of_mem hk (fun _ : Segment => ENNReal.ofReal ((4 / y) * (1 / 4 : ℝ)^k))).symm
    _ ≤ _ := ENNReal.le_tsum k

/-- Centered linear mass control bounds the actual Poisson derivative. -/
theorem poissonSlope_integral_le_of_ball_growth («λ» : Measure Segment) [IsFiniteMeasure «λ»]
    (x y c : ℝ) (hy : 0 < y) (hc : 0 ≤ c)
    (hball : ∀ r > 0, «λ» (sourceBall x r) ≤ ENNReal.ofReal (c * r)) :
    (∫ t, poissonSlope x y t ∂«λ») ≤ 8 * c := by
  let F : ℕ → Segment → ℝ≥0∞ := fun k =>
    (sourceBall x ((2 : ℝ)^k * y)).indicator
      (fun _ => ENNReal.ofReal ((4 / y) * (1 / 4 : ℝ)^k))
  have hFm (k : ℕ) : Measurable (F k) :=
    measurable_const.indicator (measurable_sourceBall _ _)
  have hs : HasSum (fun k : ℕ => 4 * c * (1 / 2 : ℝ)^k) (8 * c) := by
    have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (4 * c)
    have hv : (4 * c) * (1 - (1 / 2 : ℝ))⁻¹ = 8 * c := by norm_num <;> ring
    rw [hv] at hg
    exact hg
  have hlin : (∫⁻ t, ENNReal.ofReal (poissonSlope x y t) ∂«λ») ≤ ENNReal.ofReal (8 * c) := by
    calc
      _ ≤ ∫⁻ t, ∑' k : ℕ, F k t ∂«λ» :=
        lintegral_mono (poissonSlope_dyadic_majorant x y hy)
      _ = ∑' k : ℕ, ∫⁻ t, F k t ∂«λ» := lintegral_tsum (fun k => (hFm k).aemeasurable)
      _ ≤ ∑' k : ℕ, ENNReal.ofReal (4 * c * (1 / 2 : ℝ)^k) := by
        apply ENNReal.tsum_le_tsum
        intro k
        dsimp [F]
        rw [lintegral_indicator (measurable_sourceBall _ _), lintegral_const,
          Measure.restrict_apply_univ]
        calc
          _ ≤ ENNReal.ofReal ((4 / y) * (1 / 4 : ℝ)^k) *
              ENNReal.ofReal (c * ((2 : ℝ)^k * y)) :=
            mul_le_mul_right (hball _ (by positivity)) _
          _ = ENNReal.ofReal (4 * c * (1 / 2 : ℝ)^k) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            calc
              _ = 4 * c * ((1 / 4 : ℝ)^k * (2 : ℝ)^k) := by field_simp <;> ring
              _ = _ := by rw [← mul_pow]; norm_num
      _ = ENNReal.ofReal (8 * c) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hs.summable, hs.tsum_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonSlope «λ» x y hy)
    (Filter.Eventually.of_forall (poissonSlope_nonneg x y hy.le))] at hlin
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (poissonSlope_nonneg x y hy.le)),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 8 * c)] using h

/-- Restricting a local linear growth estimate makes it a global estimate
for the near-source measure; no bound for the original measure far away is
silently assumed. -/
theorem nearSource_ball_growth (μ : ProbabilityMeasure Segment) (x R c : ℝ)
    (hR : 0 < R) (hc : 0 ≤ c)
    (hg : ∀ r, 0 < r → r ≤ R →
      (μ : Measure Segment) (sourceBall x r) ≤ ENNReal.ofReal (c * r)) :
    ∀ r > 0, ((μ : Measure Segment).restrict (sourceBall x R)) (sourceBall x r)
      ≤ ENNReal.ofReal (c * r) := by
  intro r hr
  rw [Measure.restrict_apply (measurable_sourceBall _ _)]
  by_cases h : r ≤ R
  · exact (measure_mono Set.inter_subset_left).trans (hg r hr h)
  · calc
      _ ≤ (μ : Measure Segment) (sourceBall x R) := measure_mono Set.inter_subset_right
      _ ≤ ENNReal.ofReal (c * R) := hg R hR le_rfl
      _ ≤ ENNReal.ofReal (c * r) := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (le_of_not_ge h) hc)

/-- The remote source contribution is O(y), while local growth contributes
only 8c. All parameters refer to the original source probability measure. -/
theorem poissonSlope_integral_le_local (μ : ProbabilityMeasure Segment) (x y R c : ℝ)
    (hy : 0 < y) (hR : 0 < R) (hc : 0 ≤ c)
    (hg : ∀ r, 0 < r → r ≤ R →
      (μ : Measure Segment) (sourceBall x r) ≤ ENNReal.ofReal (c * r)) :
    (∫ t, poissonSlope x y t ∂(μ : Measure Segment)) ≤ 8 * c + y / R^2 := by
  have hm := measurable_sourceBall x R
  rw [← integral_add_compl hm (integrable_poissonSlope (μ : Measure Segment) x y hy)]
  apply add_le_add
  · exact poissonSlope_integral_le_of_ball_growth _ x y c hy hc
      (nearSource_ball_growth μ x R c hR hc hg)
  · calc
      _ ≤ ∫ _t : Segment in (sourceBall x R)ᶜ, y / R^2 ∂(μ : Measure Segment) := by
        apply integral_mono_ae
          ((integrable_poissonSlope (μ : Measure Segment) x y hy).restrict)
          (integrable_const _)
        filter_upwards [ae_restrict_mem hm.compl] with t ht
        have hd : R ≤ |x - (t : ℝ)| := le_of_not_gt ht
        have hsq : R^2 ≤ (x - (t : ℝ))^2 := by nlinarith [sq_abs (x - (t : ℝ))]
        unfold poissonSlope
        apply div_le_div_of_nonneg_left hy.le (by positivity)
        nlinarith [sq_nonneg y]
      _ = (μ : Measure Segment).real (sourceBall x R)ᶜ * (y / R^2) := by
        simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
      _ ≤ y / R^2 := by
        apply mul_le_of_le_one_left (by positivity)
        exact measureReal_le_one

end Erdos1152.V4
