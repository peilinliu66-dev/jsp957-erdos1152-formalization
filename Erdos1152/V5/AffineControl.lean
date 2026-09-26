import Erdos1152.V5.TangentIntegration
import Erdos1152.V4.LimitFieldRegularity
import Erdos1152.ExternalField

/-!
# Uniform C² control with the residual affine term retained

The first two estimates explicitly contain beta_h.  They are never used
as an assertion that second derivative convergence already implies C² convergence.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V5
open V4

noncomputable def affineSlope (μ : ProbabilityMeasure Segment) (x h : ℝ) : ℝ :=
  limitFieldJet μ 1 x h 0

noncomputable def affineRemainder (μ : ProbabilityMeasure Segment) (x h u : ℝ) : ℝ :=
  limitFieldJet μ 0 x h u-externalField u-affineSlope μ x h*u

@[simp] theorem limitField_zero (μ : ProbabilityMeasure Segment) (x h : ℝ) :
    limitFieldJet μ 0 x h 0 = 0 := by
  simp [limitFieldJet,rawFieldJet]

@[simp] theorem affineRemainder_zero (μ : ProbabilityMeasure Segment) (x h : ℝ) :
    affineRemainder μ x h 0=0 := by
  simp [affineRemainder]

/-- Two applications of the mean value inequality on the fixed compact
interval.  The derivative at zero is not presumed small. -/
theorem field_affine_error (μ : ProbabilityMeasure Segment) (x h b δ : ℝ)
    (hh : 0 < h) (hb0 : 0 ≤ b) (hb1 : b < 1) (hδ : 0 ≤ δ)
    (hsecond : ∀ u,|u| ≤ b → |limitFieldJet μ 2 x h u-1/(1-u^2)| ≤ δ) :
    (∀ u,|u| ≤ b →
      |limitFieldJet μ 1 x h u-Real.artanh u-affineSlope μ x h| ≤ δ*b) ∧
    (∀ u,|u| ≤ b → |affineRemainder μ x h u| ≤ δ*b^2) := by
  let I : Set ℝ := Icc (-b) b
  have hz : (0 : ℝ) ∈ I := ⟨by linarith, hb0⟩
  have hin (u : ℝ) (hu : u ∈ I) : |u| < 1 := (abs_le.mpr hu).trans_lt hb1
  let D : ℝ → ℝ := fun u => limitFieldJet μ 1 x h u-Real.artanh u
  have hD (u : ℝ) (hu : u ∈ I) :
      HasDerivAt D (limitFieldJet μ 2 x h u-1/(1-u^2)) u :=
    (hasDerivAt_limitFieldFirst μ x h u hh (hin u hu)).sub
      (artanh_derivative (abs_lt.mp (hin u hu)))
  have hfirst (u : ℝ) (hu : |u| ≤ b) :
      |limitFieldJet μ 1 x h u-Real.artanh u-affineSlope μ x h| ≤ δ*b := by
    have hM := (convex_Icc (-b) b).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v hv => (hD v hv).hasDerivWithinAt)
      (fun v hv => by simpa only [Real.norm_eq_abs] using hsecond v (abs_le.mpr hv)) hz (abs_le.mp hu)
    have hzero : D 0=affineSlope μ x h := by simp [D,affineSlope]
    rw [hzero] at hM
    simp only [Real.norm_eq_abs,sub_zero] at hM
    exact hM.trans (mul_le_mul_of_nonneg_left hu hδ)
  refine ⟨hfirst,?_⟩
  intro u hu
  have hE (v : ℝ) (hv : v ∈ I) :
      HasDerivAt (affineRemainder μ x h)
        (limitFieldJet μ 1 x h v-Real.artanh v-affineSlope μ x h) v := by
    exact ((hasDerivAt_limitField μ x h v hh (hin v hv)).sub
      (externalField_derivative (abs_lt.mp (hin v hv)))).sub
      (hasDerivAt_const_mul (affineSlope μ x h))
  have hM := (convex_Icc (-b) b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun v hv => (hE v hv).hasDerivWithinAt)
    (fun v hv => by simpa only [Real.norm_eq_abs] using hfirst v (abs_le.mpr hv)) hz (abs_le.mp hu)
  simp only [affineRemainder_zero,sub_zero,Real.norm_eq_abs] at hM
  have ht := mul_le_mul_of_nonneg_left hu (mul_nonneg hδ hb0)
  nlinarith

/-- Two separated samples bound the residual slope. The four actual error
terms occur in the identity, so no pointwise limit of the tangent potential
at its logarithmic center is required. -/
theorem slope_bound_two_samples (β u v eu ev du dv δ τ d : ℝ)
    (hd : 0 < d) (hsep : d ≤ v-u) (hδ : 0 ≤ δ) (hτ : 0 ≤ τ)
    (heu : |eu| ≤ δ) (hev : |ev| ≤ δ) (hdu : |du| ≤ τ) (hdv : |dv| ≤ τ)
    (heq : β*(v-u)=dv-du-ev+eu) :
    |β| ≤ (2*τ+2*δ)/d := by
  have hdiff : 0 < v-u := hd.trans_le hsep
  have hab : |β| * (v-u) ≤ 2*τ+2*δ := by
    have h1 := abs_add_le (dv-du-ev) eu
    have h2 := abs_sub (dv-du) ev
    have h3 := abs_sub dv du
    rw [← heq,abs_mul,abs_of_pos hdiff] at h1
    linarith
  apply (le_div_iff₀ hd).mpr
  exact (mul_le_mul_of_nonneg_left hsep (abs_nonneg β)).trans hab

/-- For two actual minimum-level source points the common central local
potential cancels exactly. -/
theorem minimum_sample_slope_identity (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x h u v : ℝ)
    (hh : 0 < h) (hu : |u| < 1) (hv : |v| < 1) (hm : 0 < localMass μ x h)
    (hi0 : Integrable (fun t : Segment => logProfile (x-(t : ℝ))) (μ : Measure Segment))
    (hiu : Integrable (fun t : Segment => logProfile (x+h*u-(t : ℝ))) (μ : Measure Segment))
    (hiv : Integrable (fun t : Segment => logProfile (x+h*v-(t : ℝ))) (μ : Measure Segment))
    (hval : potential μ (x+h*u)=potential μ (x+h*v)) :
    affineSlope μ x h*(v-u) =
      (potential (tangentProbability μ x h) v-(externalField v-1))-
      (potential (tangentProbability μ x h) u-(externalField u-1))-
      affineRemainder μ x h v+affineRemainder μ x h u := by
  have hu' := inner_outer_potential_identity μ hfloor x h u hh hu hm hi0 hiu
  have hv' := inner_outer_potential_identity μ hfloor x h v hh hv hm hi0 hiv
  have he : potential (tangentProbability μ x h) v-potential (tangentProbability μ x h) u =
      limitFieldJet μ 0 x h v-limitFieldJet μ 0 x h u := by
    rw [hval] at hu'
    have hs : localMass μ x h *
        (potential (tangentProbability μ x h) v-potential (tangentProbability μ x h) u-
          (limitFieldJet μ 0 x h v-limitFieldJet μ 0 x h u))=0 := by nlinarith
    have := (mul_eq_zero.mp hs).resolve_left hm.ne'
    linarith
  unfold affineRemainder
  nlinarith

end Erdos1152.V5
