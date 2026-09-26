import Erdos1152.V4.RegularizedPotential

/-!
# A quantitative boundary lower bound from the library's disk Poisson formula

This avoids assuming a half-plane Poisson formula at logarithmic singularities.
It does not by itself assert a boundary density theorem. The lower bound is for
an actual integral, proved for every probability measure and every finite floor.
-/

open MeasureTheory Set Filter Topology Complex InnerProductSpace Metric Real
open scoped ENNReal Classical

namespace Erdos1152.V4

/-- The exact disk Harnack inequality needed below, derived from the existing
Poisson formula and its kernel lower bound. -/
theorem disk_harnack_lower (f : ℂ → ℝ) (c w : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : HarmonicOnNhd f (closedBall c R))
    (h0 : ∀ z ∈ closedBall c R, 0 ≤ f z) (hw : w ∈ ball c R) :
    ((R - ‖w - c‖) / (R + ‖w - c‖)) * f c ≤ f w := by
  let l := (R - ‖w - c‖) / (R + ‖w - c‖)
  have hcont : ContinuousOn f (closedBall c R) :=
    fun z hz => (hf z hz).1.continuousAt.continuousWithinAt
  have hsphere : sphere c |R| ⊆ closedBall c R := by
    rw [abs_of_pos hR]
    exact sphere_subset_closedBall
  have hcs : ContinuousOn f (sphere c |R|) := hcont.mono hsphere
  have hkp : ContinuousOn (poissonKernel c w) (sphere c |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hw)
  have hleft : CircleIntegrable (fun z => l * f z) c R :=
    (hcs.const_mul l).circleIntegrable'
  have hright : CircleIntegrable (fun z => poissonKernel c w z * f z) c R :=
    (hkp.mul hcs).circleIntegrable'
  have hm := circleAverage_mono hleft hright (fun z hz => by
    apply mul_le_mul_of_nonneg_right _ (h0 z (hsphere hz))
    change l ≤ poissonKernel c w z
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact le_re_herglotzRieszKernel (by simpa only [abs_of_pos hR] using hz) hw)
  have hmean : circleAverage f c R = f c := by
    apply HarmonicOnNhd.circleAverage_eq
    simpa only [abs_of_pos hR] using hf
  change circleAverage (l • f) c R ≤ circleAverage (poissonKernel c w • f) c R at hm
  rw [circleAverage_smul, hmean, hf.circleAverage_poissonKernel_smul hw,
    smul_eq_mul] at hm
  exact hm

noncomputable def verticalPoint (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * Complex.I

@[simp] theorem verticalPoint_re (x y : ℝ) : (verticalPoint x y).re = x := by
  simp [verticalPoint]

@[simp] theorem verticalPoint_im (x y : ℝ) : (verticalPoint x y).im = y := by
  simp [verticalPoint]

theorem norm_verticalPoint_sub (x y z : ℝ) :
    ‖verticalPoint x y - verticalPoint x z‖ = |y - z| := by
  have he : verticalPoint x y - verticalPoint x z = ((y - z : ℝ) : ℂ) * Complex.I := by
    unfold verticalPoint
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- A uniform linear lower bound as the upper-half-plane point approaches the
real axis. It is strong enough to exclude a zero derivative density once the
boundary approximate-identity estimate is supplied. -/
theorem regularPotential_boundary_lower (μ : ProbabilityMeasure Segment)
    (A : ℝ) (hA : (A : EReal) ≤ potentialFloor μ)
    (x y : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) :
    (Real.log 2 / 16) * y ≤ regularPotential μ (verticalPoint x y) - A := by
  let c := verticalPoint x 4
  let w := verticalPoint x y
  let R : ℝ := 4 - y / 2
  let f : ℂ → ℝ := fun z => regularPotential μ z - A
  have hR : 0 < R := by dsimp [R]; linarith
  have hr : ‖w - c‖ = 4 - y := by
    rw [show w - c = verticalPoint x y - verticalPoint x 4 from rfl,
      norm_verticalPoint_sub, abs_of_nonpos (by linarith : y - 4 ≤ 0)]
    ring
  have hw : w ∈ ball c R := by
    rw [mem_ball, dist_eq_norm, hr]
    dsimp [R]
    linarith
  have hs : closedBall c R ⊆ upperHalf := by
    intro z hz
    have hd : ‖z - c‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hi := (abs_le.mp (Complex.abs_im_le_norm (z - c))).1
    simp only [Complex.sub_im, c, verticalPoint_im] at hi
    change 0 < z.im
    dsimp [R] at hd
    linarith
  have hf : HarmonicOnNhd f (closedBall c R) :=
    (harmonic_regularPotential_sub μ A).mono hs
  have hf0 : ∀ z ∈ closedBall c R, 0 ≤ f z := by
    intro z hz
    exact sub_nonneg.mpr (floor_le_regularPotential μ A hA z (hs hz))
  have hA2 : A ≤ Real.log 2 :=
    EReal.coe_le_coe_iff.mp (hA.trans (potentialFloor_le_log_two μ))
  have hc4 : Real.log 4 ≤ regularPotential μ c := by
    simpa only [c, verticalPoint_im] using
      regularPotential_ge_log_height μ c (by simp [c])
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) * 2) := by norm_num
      _ = Real.log 2 + Real.log 2 := Real.log_mul (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by ring
  have hc : Real.log 2 ≤ f c := by dsimp [f]; rw [hlog4] at hc4; linarith
  have hc0 : 0 ≤ f c := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le.trans hc
  have hk : y / 16 ≤ (R - ‖w - c‖) / (R + ‖w - c‖) := by
    rw [hr]
    dsimp [R]
    apply (le_div_iff₀ (by linarith : 0 < 4 - y / 2 + (4 - y))).mpr
    nlinarith [sq_nonneg y]
  calc
    (Real.log 2 / 16) * y = (y / 16) * Real.log 2 := by ring
    _ ≤ (y / 16) * f c := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ ((R - ‖w - c‖) / (R + ‖w - c‖)) * f c :=
      mul_le_mul_of_nonneg_right hk hc0
    _ ≤ f w := disk_harnack_lower f c w R hR hf hf0 hw

end Erdos1152.V4
