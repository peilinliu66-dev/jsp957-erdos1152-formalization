import Erdos1152.EquilibriumDensity

/-! A primitive for the density and its exact total mass. -/

open Real Set intervalIntegral MeasureTheory

namespace Erdos1152

noncomputable def densityPrimitive (a b u : ℝ) : ℝ :=
  (u * arccos (b / sqrt (1 - u ^ 2)) + arcsin (b * u / (a * sqrt (1 - u ^ 2))) -
    b * arcsin (u / a)) / π

private theorem primitive_derivative {a b u : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ^ 2 + b ^ 2 = 1) (hu : |u| < a) :
    HasDerivAt (densityPrimitive a b) (arccos (b / sqrt (1 - u ^ 2)) / π) u := by
  have hu2 : u ^ 2 < a ^ 2 := by nlinarith [sq_abs u, abs_nonneg u]
  have hc2 : 0 < 1 - u ^ 2 := by nlinarith
  let c := sqrt (1 - u ^ 2)
  let d := sqrt (a ^ 2 - u ^ 2)
  have hc : 0 < c := sqrt_pos.mpr hc2
  have hd : 0 < d := sqrt_pos.mpr (by linarith)
  have hcsq : c ^ 2 = 1 - u ^ 2 := Real.sq_sqrt hc2.le
  have hdsq : d ^ 2 = a ^ 2 - u ^ 2 := Real.sq_sqrt (by linarith)
  have hbc : b ^ 2 < c ^ 2 := by nlinarith
  have hprod : (a * c) ^ 2 - (b * u) ^ 2 = a ^ 2 - u ^ 2 := by
    calc
      _ = a ^ 2 - (a ^ 2 + b ^ 2) * u ^ 2 := by rw [mul_pow, mul_pow, hcsq]; ring
      _ = _ := by rw [hab]; ring
  have hbc1 : b / c ≠ -1 ∧ b / c ≠ 1 := by
    constructor <;> intro he <;> have he' := (div_eq_iff hc.ne').mp he <;> nlinarith
  have hbu1 : b * u / (a * c) ≠ -1 ∧ b * u / (a * c) ≠ 1 := by
    constructor <;> intro he <;> have he' := (div_eq_iff (mul_ne_zero ha.ne' hc.ne')).mp he
    all_goals
      have heSq : (b * u) ^ 2 = (a * c) ^ 2 := by rw [he']; ring
      rw [heSq] at hprod
      linarith
  have hua1 : u / a ≠ -1 ∧ u / a ≠ 1 := by
    constructor <;> intro he <;> have he' := (div_eq_iff ha.ne').mp he <;> nlinarith
  have hr1 : sqrt (1 - (b / c) ^ 2) = d / c := by
    rw [sqrt_one_sub_div_sq hc hbc.le]
    congr 2
    nlinarith
  have hr2 : sqrt (1 - (b * u / (a * c)) ^ 2) = d / (a * c) := by
    rw [sqrt_one_sub_div_sq (mul_pos ha hc) (by nlinarith)]
    rw [hprod]
  have hr3 : sqrt (1 - (u / a) ^ 2) = d / a := sqrt_one_sub_div_sq ha hu2.le
  have hcd : HasDerivAt (fun v : ℝ => sqrt (1 - v ^ 2)) (-u / c) u := by
    convert! (((hasDerivAt_id u).pow 2).const_sub 1).sqrt hc2.ne' using 1
    dsimp [c]
    ring
  have h1 := (Real.hasDerivAt_arccos hbc1.1 hbc1.2).comp u ((hasDerivAt_const u b).div hcd hc.ne')
  have h2 := (Real.hasDerivAt_arcsin hbu1.1 hbu1.2).comp u
    (((hasDerivAt_id u).const_mul b).div (hcd.const_mul a) (mul_ne_zero ha.ne' hc.ne'))
  have h3 := (Real.hasDerivAt_arcsin hua1.1 hua1.2).comp u ((hasDerivAt_id u).div_const a)
  have hf := (((hasDerivAt_id u).mul h1).add h2 |>.sub (h3.const_mul b)).div_const π
  convert! hf using 1
  simp only [id_eq, Function.comp_apply, Pi.div_apply, mul_one, one_mul, zero_mul, zero_sub]
  change arccos (b / c) / π = _
  simp only [← show c = sqrt (1 - u ^ 2) from rfl]
  rw [hr1, hr2, hr3]
  field_simp
  nlinarith [hcsq]


private theorem primitive_continuousOn {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ^ 2 + b ^ 2 = 1) : ContinuousOn (densityPrimitive a b) (Icc (-a) a) := by
  intro u hu
  have hu2 : u ^ 2 ≤ a ^ 2 := by nlinarith [hu.1, hu.2]
  have hc : sqrt (1 - u ^ 2) ≠ 0 := (sqrt_pos.mpr (by nlinarith : 0 < 1 - u ^ 2)).ne'
  apply ContinuousAt.continuousWithinAt
  unfold densityPrimitive
  fun_prop (disch := positivity)

private theorem primitive_neg (a b u : ℝ) : densityPrimitive a b (-u) = -densityPrimitive a b u := by
  simp only [densityPrimitive, neg_sq, mul_neg, neg_div, Real.arcsin_neg]
  ring

private theorem primitive_endpoint {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a ^ 2 + b ^ 2 = 1) : densityPrimitive a b a = (1 - b) / 2 := by
  have hc : sqrt (1 - a ^ 2) = b := by rw [show 1 - a ^ 2 = b ^ 2 by linarith, sqrt_sq hb.le]
  unfold densityPrimitive
  rw [hc, div_self hb.ne', arccos_one, div_self ha.ne']
  rw [show b * a / (a * b) = 1 by field_simp, arcsin_one]
  field_simp
  ring

/-- The density has mass `t` on its explicit support, including both endpoints. -/
theorem equilibriumDensity_mass_support {t : ℝ} (ht : t ∈ Ioo 0 1) :
    (∫ u in -supportRadius t..supportRadius t, equilibriumDensity t u) = t := by
  let a := supportRadius t
  let b := 1 - t
  have hb : 0 < b := by dsimp [b]; linarith [ht.2]
  have ha : 0 < a := sqrt_pos.mpr (by nlinarith [ht.1, ht.2])
  have hab : a ^ 2 + b ^ 2 = 1 := by
    dsimp [a, b, supportRadius]
    rw [sq_sqrt (by nlinarith [ht.1, ht.2])]
    ring
  have horder : -a ≤ a := by linarith
  have hcont := primitive_continuousOn ha hb hab
  have hd : ∀ u ∈ Ioo (-a) a, HasDerivAt (densityPrimitive a b) (equilibriumDensity t u) u := by
    intro u hu
    have hu' : |u| < a := abs_lt.mpr hu
    have hu0 : |u| < supportRadius t := hu'
    simpa only [equilibriumDensity, if_pos hu0] using primitive_derivative ha hb hab hu'
  have hint : IntervalIntegrable (equilibriumDensity t) volume (-a) a := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    · simpa [uIcc_of_le horder] using hcont
    · simpa [min_eq_left horder, max_eq_right horder] using hd
    · intro u hu; exact equilibriumDensity_nonneg t u
  change (∫ u in -a..a, equilibriumDensity t u) = t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le horder hcont hd hint,
    primitive_neg, primitive_endpoint ha hb hab]
  dsimp [b]
  ring

/-- The integral over the real line agrees with the mass on the support. -/
theorem equilibriumDensity_mass {t : ℝ} (ht : t ∈ Ioo 0 1) :
    (∫ u : ℝ, equilibriumDensity t u) = t := by
  calc
    _ = ∫ u in -supportRadius t..supportRadius t, equilibriumDensity t u := ?_
    _ = t := equilibriumDensity_mass_support ht
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro u hu
  have h : |u| < supportRadius t := by
    by_contra hn
    exact hu (equilibriumDensity_eq_zero (le_of_not_gt hn))
  exact ⟨(abs_lt.mp h).1, (abs_lt.mp h).2.le⟩

end Erdos1152
