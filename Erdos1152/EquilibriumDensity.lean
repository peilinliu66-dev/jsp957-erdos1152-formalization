import Erdos1152.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-! The explicit density and its elementary differential identities. -/

open Real Set Filter Topology

namespace Erdos1152

noncomputable def equilibriumDensity (t u : ℝ) : ℝ :=
  if |u| < supportRadius t then arccos ((1 - t) / sqrt (1 - u ^ 2)) / π else 0

private theorem density_parameters {t u : ℝ} (ht : t ∈ Ioo 0 1)
    (hu : |u| < supportRadius t) :
    0 < 1 - u ^ 2 ∧ 0 < 1 - (1 - t) ^ 2 - u ^ 2 ∧
      0 < (1 - t) / sqrt (1 - u ^ 2) ∧ (1 - t) / sqrt (1 - u ^ 2) < 1 := by
  have hat : 0 ≤ 1 - (1 - t) ^ 2 := by nlinarith [ht.1,ht.2]
  have ha := Real.sq_sqrt hat
  change supportRadius t ^ 2 = 1 - (1 - t) ^ 2 at ha
  have hs : u ^ 2 < supportRadius t ^ 2 := by
    nlinarith [sq_abs u, abs_nonneg u, sqrt_nonneg (1 - (1 - t) ^ 2)]
  have hd : 0 < 1 - u ^ 2 := by nlinarith
  have hroot : 1 - t < sqrt (1 - u ^ 2) := by
    nlinarith [Real.sq_sqrt hd.le, Real.sqrt_nonneg (1 - u ^ 2)]
  exact ⟨hd, by nlinarith, div_pos (by linarith [ht.2]) (sqrt_pos.mpr hd),
    (div_lt_one (sqrt_pos.mpr hd)).mpr hroot⟩

theorem equilibriumDensity_nonneg (t u : ℝ) : 0 ≤ equilibriumDensity t u := by
  unfold equilibriumDensity
  split_ifs
  · exact div_nonneg (Real.arccos_nonneg _) Real.pi_pos.le
  · exact le_rfl

theorem equilibriumDensity_even (t u : ℝ) : equilibriumDensity t (-u) = equilibriumDensity t u := by
  simp [equilibriumDensity]

theorem equilibriumDensity_eq_zero {t u : ℝ} (hu : supportRadius t ≤ |u|) :
    equilibriumDensity t u = 0 := by simp [equilibriumDensity, not_lt.mpr hu]

/-- The time derivative in the interior of the support is the arcsine density. -/
theorem equilibriumDensity_time_derivative {t u : ℝ} (ht : t ∈ Ioo 0 1)
    (hu : |u| < supportRadius t) :
    HasDerivAt (fun s => equilibriumDensity s u)
      (1 / (π * sqrt (supportRadius t ^ 2 - u ^ 2))) t := by
  obtain ⟨hd,hgap,hpos,hlt⟩ := density_parameters ht hu
  have hden : 0 < sqrt (1 - u ^ 2) := sqrt_pos.mpr hd
  have hr : 0 < 1 - ((1 - t) / sqrt (1 - u ^ 2)) ^ 2 := by nlinarith
  have hat : 0 ≤ 1 - (1 - t) ^ 2 := by nlinarith [ht.1,ht.2]
  have he : sqrt (1 - ((1 - t) / sqrt (1 - u ^ 2)) ^ 2) * sqrt (1 - u ^ 2) =
      sqrt (supportRadius t ^ 2 - u ^ 2) := by
    apply (sq_eq_sq₀ (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (sqrt_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hr.le, Real.sq_sqrt hd.le,
      Real.sq_sqrt (by simpa [supportRadius, Real.sq_sqrt hat] using hgap.le)]
    dsimp [supportRadius]
    rw [Real.sq_sqrt hat]
    field_simp
    nlinarith [Real.sq_sqrt hd.le]
  have h := ((Real.hasDerivAt_arccos (by linarith : (1 - t) / sqrt (1 - u ^ 2) ≠ -1)
    (ne_of_lt hlt)).comp t (((hasDerivAt_id t).const_sub 1).div_const (sqrt (1 - u ^ 2)))).div_const π
  have hvalue : (-(1 / sqrt (1 - ((1 - t) / sqrt (1 - u ^ 2)) ^ 2)) *
      (-1 / sqrt (1 - u ^ 2))) / π = 1 / (π * sqrt (supportRadius t ^ 2 - u ^ 2)) := by
    rw [← he]
    ring
  rw [hvalue] at h
  apply h.congr_of_eventuallyEq
  have hc : Continuous (supportRadius) := by unfold supportRadius; fun_prop
  filter_upwards [(hc.tendsto t).eventually (lt_mem_nhds hu)] with s hs
  simp only [equilibriumDensity, if_pos hs, Function.comp_apply, id_eq]

end Erdos1152
