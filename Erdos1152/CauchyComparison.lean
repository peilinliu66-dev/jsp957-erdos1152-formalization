import Erdos1152.CauchyIntegral

/-! Strict comparison for a truncated scalar Cauchy integral. -/

open Real Set intervalIntegral MeasureTheory

namespace Erdos1152

/-- Before the support reaches `x`, the truncated integral is strictly below `Q'(x)`. -/
theorem cauchy_integral_lt_artanh {x t : ℝ} (hx : x ∈ Ioo 0 1)
    (ht : 0 ≤ t) (hte : t < entranceTime x) :
    (∫ s in (0 : ℝ)..t, 1 / sqrt (x ^ 2 - supportRadius s ^ 2)) < artanh x := by
  let e := entranceTime x
  let g := fun s : ℝ => 1 / sqrt (x ^ 2 - supportRadius s ^ 2)
  have he : 0 < e := lt_of_le_of_lt ht hte
  have hfull : (∫ s in (0 : ℝ)..e, g s) = artanh x := cauchy_integral_eq_artanh hx
  have hint : IntervalIntegrable g volume 0 e :=
    intervalIntegral.intervalIntegrable_of_integral_ne_zero (by rw [hfull]; exact (artanh_pos hx).ne')
  have hint0t : IntervalIntegrable g volume 0 t := hint.mono_set (by
    rw [uIcc_of_le ht, uIcc_of_le he.le]
    exact Icc_subset_Icc le_rfl hte.le)
  have hintte : IntervalIntegrable g volume t e := hint.mono_set (by
    rw [uIcc_of_le hte.le, uIcc_of_le he.le]
    exact Icc_subset_Icc ht le_rfl)
  have hpos : ∀ s ∈ Ioo t e, 0 < g s := by
    intro s hs
    have hc : 0 < sqrt (1 - x ^ 2) := sqrt_pos.mpr (by nlinarith [hx.1, hx.2])
    have hcsq := sq_sqrt (show 0 ≤ 1 - x ^ 2 by nlinarith [hx.1, hx.2])
    have hs0 : 0 ≤ s := le_trans ht hs.1.le
    have hsc : sqrt (1 - x ^ 2) < 1 - s := by
      have hs' := hs.2
      change s < 1 - sqrt (1 - x ^ 2) at hs'
      linarith
    have hsr : 0 ≤ 1 - (1 - s) ^ 2 := by nlinarith
    have hrad : 0 < x ^ 2 - supportRadius s ^ 2 := by
      unfold supportRadius
      rw [sq_sqrt hsr]
      nlinarith
    exact one_div_pos.mpr (sqrt_pos.mpr hrad)
  have htail := intervalIntegral.intervalIntegral_pos_of_pos_on hintte hpos hte
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint0t hintte
  change (∫ s in (0 : ℝ)..t, g s) < artanh x
  linarith

end Erdos1152
