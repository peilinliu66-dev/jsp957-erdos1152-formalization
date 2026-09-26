import Erdos1152.CardinalLocal

/-!
# Elementary logarithmic estimates used by the V3 analytic modules

These statements are proved here to keep the V3 entrypoint independent of the
uncompiled V1/V2 analytic candidate modules. The positive truncation level and
all nonzero evaluations needed for logarithms are explicit.
-/

open Polynomial Set
open scoped Classical

namespace Erdos1152.V3

noncomputable def truncatedLogKernel (ε x y : ℝ) : ℝ :=
  Real.log (max ε |x - y|)

theorem continuous_truncatedLogKernel (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℝ => truncatedLogKernel ε p.1 p.2) := by
  unfold truncatedLogKernel
  apply Continuous.log
  · exact continuous_const.max ((continuous_fst.sub continuous_snd).abs)
  · intro p
    exact (lt_of_lt_of_le hε (le_max_left ε |p.1 - p.2|)).ne'

theorem log_abs_nodePolynomial_eval (U : Finset ℝ) (z : ℝ)
    (hz : ∀ y ∈ U, z ≠ y) :
    Real.log |(nodePolynomial U).eval z| = ∑ y ∈ U, Real.log |z - y| := by
  rw [nodePolynomial_eval, Finset.abs_prod]
  exact Real.log_prod (fun y hy => abs_ne_zero.mpr (sub_ne_zero.mpr (hz y hy)))

/-- Finite deletion estimate with an explicit diagonal-removal budget. -/
theorem log_node_product_le_truncated_sum_of_card_bound
    (Y U : Finset ℝ) (hUY : U ⊆ Y) (z ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hz : ∀ y ∈ U, z ≠ y)
    (D : ℕ) (hcard : Y.card ≤ U.card + D) :
    Real.log |(nodePolynomial U).eval z| ≤
      (∑ y ∈ Y, truncatedLogKernel ε z y) + (D : ℝ) * (-Real.log ε) := by
  classical
  rw [log_abs_nodePolynomial_eval U z hz]
  have hterm : ∀ y : ℝ, 0 ≤ truncatedLogKernel ε z y - Real.log ε := by
    intro y
    exact sub_nonneg.mpr (Real.log_le_log hε (le_max_left ε |z - y|))
  have hsubset := Finset.sum_le_sum_of_subset_of_nonneg hUY
    (fun y _ _ => hterm y)
  change (∑ y ∈ U, (truncatedLogKernel ε z y - Real.log ε)) ≤
    ∑ y ∈ Y, (truncatedLogKernel ε z y - Real.log ε) at hsubset
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsubset
  have hlog : (∑ y ∈ U, Real.log |z - y|) ≤
      ∑ y ∈ U, truncatedLogKernel ε z y := by
    apply Finset.sum_le_sum
    intro y hy
    exact Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr (hz y hy)))
      (le_max_right ε |z - y|)
  have hεlog : 0 ≤ -Real.log ε := neg_nonneg.mpr (Real.log_nonpos hε.le hε1)
  have hc : (Y.card : ℝ) ≤ (U.card : ℝ) + (D : ℝ) := by exact_mod_cast hcard
  have hcost := mul_le_mul_of_nonneg_right hc hεlog
  nlinarith

end Erdos1152.V3
