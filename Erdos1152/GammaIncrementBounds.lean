import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A real-variable Gamma estimate for the explicit auxiliary-grid kernel.
Convexity of log Gamma controls a fractional increment between consecutive
integers; together with factorial Stirling this supplies real Gamma Stirling.
This file formalizes the increment estimate. Build status is recorded by the canonical driver. -/

open Real Set
namespace Erdos1152

private theorem logGamma_add_one (x : ℝ) (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) = Real.log x + Real.log (Real.Gamma x) := by
  rw [Real.Gamma_add_one hx.ne',
    Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']

/-- The log-convexity interpolation sandwich, uniform for the entire fractional
part `t∈[0,1]`, not merely along integer Gamma arguments. -/
theorem logGamma_increment_bounds (x t : ℝ) (hx : 0 < x) (ht : t ∈ Icc 0 1) :
    t * Real.log x ≤ Real.log (Real.Gamma (x + 1 + t)) -
        Real.log (Real.Gamma (x + 1)) ∧
      Real.log (Real.Gamma (x + 1 + t)) - Real.log (Real.Gamma (x + 1)) ≤
        t * Real.log (x + 1) := by
  constructor
  · by_cases ht0 : t = 0
    · subst t
      simp
    · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
      have hs := Real.convexOn_log_Gamma.slope_mono_adjacent
        (show x ∈ Ioi (0 : ℝ) from hx)
        (show x + 1 + t ∈ Ioi (0 : ℝ) from by change 0 < x + 1 + t; linarith)
        (show x < x + 1 by linarith) (show x + 1 < x + 1 + t by linarith)
      simp only [Function.comp_apply] at hs
      rw [show x + 1 - x = 1 by ring,
        show x + 1 + t - (x + 1) = t by ring, div_one] at hs
      have hd : Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) =
          Real.log x := by linarith [logGamma_add_one x hx]
      rw [hd] at hs
      simpa only [mul_comm] using (le_div_iff₀ htpos).mp hs
  · have hc := Real.convexOn_log_Gamma.2
      (show x + 1 ∈ Ioi (0 : ℝ) from by change 0 < x + 1; linarith)
      (show x + 1 + 1 ∈ Ioi (0 : ℝ) from by change 0 < x + 1 + 1; linarith)
      (show 0 ≤ 1 - t by linarith [ht.2]) ht.1
      (show (1 - t) + t = 1 by ring)
    simp only [Function.comp_apply, smul_eq_mul] at hc
    rw [show (1 - t) * (x + 1) + t * (x + 1 + 1) = x + 1 + t by ring] at hc
    have hd := logGamma_add_one (x + 1) (by linarith)
    rw [hd] at hc
    nlinarith

/-- A convenient O(1/x) bound for the fractional interpolation remainder. -/
theorem logGamma_increment_error (x t : ℝ) (hx : 0 < x) (ht : t ∈ Icc 0 1) :
    0 ≤ Real.log (Real.Gamma (x + 1 + t)) - Real.log (Real.Gamma (x + 1)) -
        t * Real.log x ∧
      Real.log (Real.Gamma (x + 1 + t)) - Real.log (Real.Gamma (x + 1)) -
        t * Real.log x ≤ 1 / x := by
  have h := logGamma_increment_bounds x t hx ht
  have hratio : Real.log (x + 1) - Real.log x = Real.log (1 + 1 / x) := by
    rw [← Real.log_div (by linarith : x + 1 ≠ 0) hx.ne']
    congr 1
    field_simp [hx.ne']
  have hlog : Real.log (1 + 1 / x) ≤ 1 / x := by
    simpa using Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / x by positivity)
  refine ⟨by linarith [h.1], ?_⟩
  calc
    _ ≤ t * (Real.log (x + 1) - Real.log x) := by nlinarith [h.2]
    _ = t * Real.log (1 + 1 / x) := by rw [hratio]
    _ ≤ t * (1 / x) := mul_le_mul_of_nonneg_left hlog ht.1
    _ ≤ 1 * (1 / x) := mul_le_mul_of_nonneg_right ht.2 (by positivity)
    _ = _ := one_mul _

end Erdos1152
