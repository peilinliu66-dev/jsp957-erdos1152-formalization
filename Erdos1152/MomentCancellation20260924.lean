import Mathlib

/-!
# Finite identities for the moment-cancelled weighted-kernel construction

Research continuation of the recovered JSP957 project.  These are actual proof
scripts, not added mathematical axioms.  Their elaboration status is recorded
separately in the build log.  No theorem in this file claims LocalAmplificationMinimal.
-/

noncomputable section

namespace Erdos1152.Continuation20260924

/-- The two correction weights cancel the zeroth and first signed moments. -/
theorem two_moment_corrector (a b M₀ M₁ : ℝ) (hab : a ≠ b) :
    let da := (b * M₀ - M₁) / (a - b)
    let db := (M₁ - a * M₀) / (a - b)
    (da + db = -M₀) ∧ (a * da + b * db = -M₁) := by
  dsimp
  have hden : a - b ≠ 0 := sub_ne_zero.mpr hab
  constructor <;> field_simp [hden] <;> ring

/-- Exact second-order resolvent expansion, with both denominators explicit. -/
theorem reciprocal_second_order (x v : ℝ) (hx : x ≠ 0) (hxv : x - v ≠ 0) :
    1 / (x - v) = 1 / x + v / x ^ 2 + v ^ 2 / (x ^ 2 * (x - v)) := by
  field_simp [hx, hxv] <;> ring

/-- Weighted form in the arrangement used before summing over the finite grid. -/
theorem weighted_reciprocal_second_order (x v c : ℝ)
    (hx : x ≠ 0) (hxv : x - v ≠ 0) :
    c / (x - v) = c / x + (c * v) / x ^ 2 +
      ((c * v ^ 2) / (x - v)) / x ^ 2 := by
  field_simp [hx, hxv] <;> ring

/-- After two exact moment cancellations, the finite Cauchy sum has a quadratic
factor in front.  Bounding the remaining denominator yields the cubic tail. -/
theorem finite_resolvent_of_two_zero_moments
    {ι : Type*} (s : Finset ι) (c v : ι → ℝ) (x : ℝ)
    (hx : x ≠ 0) (hxv : ∀ i ∈ s, x - v i ≠ 0)
    (h₀ : (∑ i ∈ s, c i) = 0)
    (h₁ : (∑ i ∈ s, c i * v i) = 0) :
    (∑ i ∈ s, c i / (x - v i)) =
      (∑ i ∈ s, (c i * v i ^ 2) / (x - v i)) / x ^ 2 := by
  calc
    (∑ i ∈ s, c i / (x - v i)) =
        ∑ i ∈ s, (c i / x + (c i * v i) / x ^ 2 +
          ((c i * v i ^ 2) / (x - v i)) / x ^ 2) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact weighted_reciprocal_second_order x (v i) (c i) hx (hxv i hi)
    _ = (∑ i ∈ s, c i) / x + (∑ i ∈ s, c i * v i) / x ^ 2 +
          (∑ i ∈ s, (c i * v i ^ 2) / (x - v i)) / x ^ 2 := by
      simp only [Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
    _ = (∑ i ∈ s, (c i * v i ^ 2) / (x - v i)) / x ^ 2 := by
      rw [h₀, h₁]
      simp

/-- Two separated near-zero probes bound the slope of an affine function.
This is the finite scalar step used after controlling the second derivative of
the actual external field.  It does not assume exponential weights are close. -/
theorem affine_slope_bound_of_two_probes
    (α β u v ε d : ℝ) (hd : 0 < d) (hsep : d ≤ v - u)
    (hu : |α * u + β| ≤ ε) (hv : |α * v + β| ≤ ε) :
    |α| ≤ 2 * ε / d := by
  rcases abs_le.mp hu with ⟨hu₁, hu₂⟩
  rcases abs_le.mp hv with ⟨hv₁, hv₂⟩
  have hgap : 0 ≤ v - u - d := by linarith
  by_cases hα : 0 ≤ α
  · rw [abs_of_nonneg hα]
    apply (le_div_iff₀ hd).mpr
    have hm := mul_nonneg hα hgap
    nlinarith
  · have hα' : α ≤ 0 := by linarith
    rw [abs_of_nonpos hα']
    apply (le_div_iff₀ hd).mpr
    have hm := mul_nonneg (neg_nonneg.mpr hα') hgap
    nlinarith

end Erdos1152.Continuation20260924
