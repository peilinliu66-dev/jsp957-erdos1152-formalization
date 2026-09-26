import Erdos1152.ExternalField
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! The scalar integral giving the real boundary value in Lemma 4. -/

open Real Set intervalIntegral MeasureTheory

namespace Erdos1152

noncomputable def supportRadius (t : ℝ) : ℝ := sqrt (1 - (1 - t) ^ 2)
noncomputable def entranceTime (x : ℝ) : ℝ := 1 - sqrt (1 - x ^ 2)

/-- A continuous primitive also handles the integrable square-root singularity. -/
theorem integral_inverse_sqrt {c b : ℝ} (hc : 0 < c) (hcb : c ≤ b) :
    (∫ u in c..b, 1 / sqrt (u ^ 2 - c ^ 2)) = arcosh (b / c) := by
  have hcont : ContinuousOn (fun u => arcosh (u / c)) (Icc c b) :=
    Real.continuousOn_arcosh.comp (by fun_prop) (fun u hu => (le_div_iff₀ hc).mpr (by simpa using hu.1))
  have hd : ∀ u ∈ Ioo c b, HasDerivAt (fun u => arcosh (u / c)) (1 / sqrt (u ^ 2 - c ^ 2)) u := by
    intro u hu
    have hp : 0 < u ^ 2 - c ^ 2 := by nlinarith [hu.1]
    have hs : sqrt ((u / c) ^ 2 - 1) = sqrt (u ^ 2 - c ^ 2) / c := by
      rw [show (u / c) ^ 2 - 1 = (u ^ 2 - c ^ 2) / c ^ 2 by field_simp,
        Real.sqrt_div hp.le, Real.sqrt_sq hc.le]
    have h := (Real.hasDerivAt_arcosh ((lt_div_iff₀ hc).mpr (by simpa using hu.1))).comp u
      ((hasDerivAt_id u).div_const c)
    convert! h using 1
    simp only [id_eq] at h ⊢
    rw [hs]
    field_simp
  have hint : IntervalIntegrable (fun u => 1 / sqrt (u ^ 2 - c ^ 2)) volume c b := by
    apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    · simpa [uIcc_of_le hcb] using hcont
    · simpa [min_eq_left hcb, max_eq_right hcb] using hd
    · intro u hu; positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hcb hcont hd hint]
  simp [hc.ne']

/-- The scalar Cauchy integral in Lemma 4, including its endpoint singularity. -/
theorem cauchy_integral_eq_artanh {x : ℝ} (hx : x ∈ Ioo 0 1) :
    (∫ s in (0 : ℝ)..entranceTime x, 1 / sqrt (x ^ 2 - supportRadius s ^ 2)) = artanh x := by
  let c := sqrt (1 - x ^ 2)
  have hc : 0 < c := sqrt_pos.mpr (by nlinarith [hx.1,hx.2])
  have hc1 : c < 1 := by
    apply (sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    nlinarith [sq_pos_of_pos hx.1]
  have hcsq : c ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by nlinarith [hx.1,hx.2])
  have heq : (∫ s in (0 : ℝ)..entranceTime x, 1 / sqrt (x ^ 2 - supportRadius s ^ 2)) =
      ∫ s in (0 : ℝ)..(1 - c), (fun u => 1 / sqrt (u ^ 2 - c ^ 2)) (1 - s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    change s ∈ uIcc 0 (1 - c) at hs
    rw [uIcc_of_le (show 0 ≤ 1 - c by linarith)] at hs
    have hs0 : 0 ≤ 1 - (1 - s) ^ 2 := by nlinarith [hs.1,hs.2]
    dsimp [supportRadius]
    rw [Real.sq_sqrt hs0]
    congr 2
    nlinarith
  rw [heq, intervalIntegral.integral_comp_sub_left (fun u : ℝ => 1 / sqrt (u ^ 2 - c ^ 2)) 1, sub_sub_cancel, sub_zero,
    integral_inverse_sqrt hc hc1.le]
  rw [← Real.cosh_artanh ⟨by linarith [hx.1],hx.2⟩]
  exact Real.arcosh_cosh (Real.artanh_pos hx).le

end Erdos1152
