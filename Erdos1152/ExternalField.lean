import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The explicit external field and the logarithmic potential of uniform measure. -/

open Real Set intervalIntegral

namespace Erdos1152

noncomputable def externalField (x : ℝ) : ℝ :=
  ((1 + x) * log (1 + x) + (1 - x) * log (1 - x)) / 2

@[simp] theorem externalField_zero : externalField 0 = 0 := by simp [externalField]

theorem externalField_derivative {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt externalField (artanh x) x := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  have h1 := (Real.hasDerivAt_mul_log hp.ne').comp x ((hasDerivAt_id x).const_add 1)
  have h2 := (Real.hasDerivAt_mul_log hm.ne').comp x ((hasDerivAt_id x).const_sub 1)
  convert! (h1.add h2).div_const 2 using 1
  rw [Real.artanh_eq_half_log ⟨hx.1.le,hx.2.le⟩, Real.log_div hp.ne' hm.ne']
  ring

theorem artanh_derivative {x : ℝ} (hx : x ∈ Ioo (-1) 1) :
    HasDerivAt artanh (1 / (1 - x ^ 2)) x := by
  have hp : 0 < 1 + x := by linarith [hx.1]
  have hm : 0 < 1 - x := by linarith [hx.2]
  have hd := ((((hasDerivAt_id x).const_add 1).log hp.ne').sub
    (((hasDerivAt_id x).const_sub 1).log hm.ne')).div_const 2
  have hval : (1 / (1 + x) - -1 / (1 - x)) / 2 = 1 / (1 - x ^ 2) := by
    rw [show 1 - x ^ 2 = (1 + x) * (1 - x) by ring]
    field_simp
    ring
  simp only [id_eq, Pi.sub_apply] at hd
  rw [hval] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
  rw [Real.artanh_eq_half_log ⟨hy.1.le,hy.2.le⟩,
    Real.log_div (by linarith [hy.1]) (by linarith [hy.2])]
  ring

/-- The potential of density `1/2` on `[-1,1]`. -/
noncomputable def uniformPotential (x : ℝ) : ℝ :=
  (∫ u in (-1 : ℝ)..1, log |x - u|) / 2

theorem uniformPotential_eq (x : ℝ) : uniformPotential x = externalField x - 1 := by
  simp only [uniformPotential, Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_left Real.log x, integral_log]
  have he : log (x - 1) = log (1 - x) := by rw [← log_neg_eq_log (x - 1)]; congr 1; ring
  rw [he]
  dsimp [externalField]
  rw [sub_neg_eq_add, add_comm x 1]
  ring

/-- Normalization of the square roots arising from inverse trigonometric derivatives. -/
theorem sqrt_one_sub_div_sq {p q : ℝ} (hq : 0 < q) (hpq : p ^ 2 ≤ q ^ 2) :
    sqrt (1 - (p / q) ^ 2) = sqrt (q ^ 2 - p ^ 2) / q := by
  rw [show 1 - (p / q) ^ 2 = (q ^ 2 - p ^ 2) / q ^ 2 by field_simp,
    Real.sqrt_div (sub_nonneg.mpr hpq), Real.sqrt_sq hq.le]

end Erdos1152
