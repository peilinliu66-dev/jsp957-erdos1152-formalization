import Erdos1152.RemezAmplification
import Erdos1152.ExternalField

/-! Elementary pieces of the logarithmic-potential route. These statements do
not assert weak compactness or CardinalGrowthCover. Source candidate only;
no compiler was available. -/
open Real Polynomial MeasureTheory Set intervalIntegral
namespace Erdos1152

noncomputable def truncatedLogKernel (ε x y : ℝ) : ℝ :=
  Real.log (max ε |x - y|)

/-- Truncate the DISTANCE before applying `log`. This treats the diagonal
correctly, unlike `max (Real.log |x-y|) (log ε)` with Lean's `Real.log 0=0`. -/
theorem continuous_truncatedLogKernel (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun p : ℝ × ℝ => truncatedLogKernel ε p.1 p.2) := by
  have hc : Continuous (fun p : ℝ × ℝ => max ε |p.1 - p.2|) :=
    continuous_const.max ((continuous_fst.sub continuous_snd).abs)
  exact hc.log (fun p => (hε.trans_le (le_max_left _ _)).ne')

theorem truncatedLogKernel_of_large_distance (ε x y : ℝ) (h : ε ≤ |x - y|) :
    truncatedLogKernel ε x y = Real.log |x - y| := by
  simp [truncatedLogKernel, max_eq_right h]

theorem truncatedLogKernel_of_small_distance (ε x y : ℝ) (h : |x - y| ≤ ε) :
    truncatedLogKernel ε x y = Real.log ε := by
  simp [truncatedLogKernel, max_eq_left h]

/-- The exact mass of the one-dimensional logarithmic singularity removed
by truncation. The value of `log` at zero has no effect on this integral. -/
theorem integral_log_truncation_window (ε : ℝ) :
    (∫ u in -ε..ε, (Real.log ε - Real.log |u|)) = 2 * ε := by
  simp only [Real.log_abs]
  rw [intervalIntegral.integral_sub intervalIntegrable_const intervalIntegrable_log',
    intervalIntegral.integral_const, integral_log, Real.log_neg_eq_log]
  simp only [smul_eq_mul]
  ring

/-- A genuine logarithmic gap gives cardinal-polynomial growth. The zero-set
exception is explicit; it must be removed before using real logarithms. -/
theorem cardinal_growth_of_log_gap (Y : Finset ℝ) (z x λ : ℝ)
    (hnum : (nodePolynomial (Y.erase z)).eval x ≠ 0)
    (hgap : λ + Real.log |(nodePolynomial (Y.erase z)).eval z| ≤
      Real.log |(nodePolynomial (Y.erase z)).eval x|) :
    Real.exp λ ≤ |(cardinalPolynomial Y z).eval x| := by
  classical
  have hden : (nodePolynomial (Y.erase z)).eval z ≠ 0 := by
    rw [nodePolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm
  have ha : 0 < |(nodePolynomial (Y.erase z)).eval x| := abs_pos.mpr hnum
  have hb : 0 < |(nodePolynomial (Y.erase z)).eval z| := abs_pos.mpr hden
  have he := Real.exp_le_exp.mpr hgap
  rw [Real.exp_add, Real.exp_log hb, Real.exp_log ha] at he
  have hrepr : |(cardinalPolynomial Y z).eval x| =
      |(nodePolynomial (Y.erase z)).eval x| /
        |(nodePolynomial (Y.erase z)).eval z| := by
    simp [cardinalPolynomial, eval_mul, eval_C, abs_mul, abs_inv, div_eq_mul_inv]
  rw [hrepr]
  exact (le_div_iff₀ hb).mpr he

/-- The `3η` separation in the manuscript pays for one numerator and one
denominator error, leaving an exponential rate `η`. -/
theorem normalized_log_gap (u v V a η N : ℝ) (hN : 0 < N)
    (hnum : V - η ≤ u / N) (hden : v / N ≤ a + η)
    (hregion : a + 3 * η ≤ V) : η * N + v ≤ u := by
  have hn := (le_div_iff₀ hN).mp hnum
  have hd := (div_le_iff₀ hN).mp hden
  have hr := mul_le_mul_of_nonneg_right hregion hN.le
  nlinarith


/-- Logarithmic node products may be expanded only after excluding zero factors. -/
theorem log_abs_nodePolynomial_eval (U : Finset ℝ) (z : ℝ)
    (hz : ∀ y ∈ U, z ≠ y) :
    Real.log |(nodePolynomial U).eval z| = ∑ y ∈ U, Real.log |z - y| := by
  rw [nodePolynomial_eval, Real.log_abs, Real.log_prod
    (fun y hy => sub_ne_zero.mpr (hz y hy))]
  simp only [Real.log_abs]

/-- Finite deletion costs at most one truncation level per deleted node.
The formula also pays for removal of the distinguished derivative node.
Unlike a potential limit assumption, this is a finite inequality proved here. -/
theorem log_node_product_le_truncated_sum (Y U : Finset ℝ) (hUY : U ⊆ Y)
    (z ε : ℝ) (hε : 0 < ε) (hz : ∀ y ∈ U, z ≠ y) :
    Real.log |(nodePolynomial U).eval z| ≤
      (∑ y ∈ Y, truncatedLogKernel ε z y) +
        ((Y.card : ℝ) - U.card) * (-Real.log ε) := by
  have hlo (y : ℝ) : Real.log ε ≤ truncatedLogKernel ε z y :=
    Real.log_le_log hε (le_max_left _ _)
  have hup (y : ℝ) (hy : y ∈ U) : Real.log |z - y| ≤ truncatedLogKernel ε z y :=
    Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr (hz y hy))) (le_max_right _ _)
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hUY
    (f := fun y => truncatedLogKernel ε z y - Real.log ε)
    (fun y _ _ => sub_nonneg.mpr (hlo y))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hsum
  have hpoint := Finset.sum_le_sum hup
  rw [log_abs_nodePolynomial_eval U z hz]
  linarith

/-- The cardinal-growth upper bound with a prescribed finite deletion budget. -/
theorem log_node_product_le_truncated_sum_of_card_bound
    (Y U : Finset ℝ) (hUY : U ⊆ Y) (z ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hz : ∀ y ∈ U, z ≠ y) (D : ℕ) (hcard : Y.card ≤ U.card + D) :
    Real.log |(nodePolynomial U).eval z| ≤
      (∑ y ∈ Y, truncatedLogKernel ε z y) + D * (-Real.log ε) := by
  have hbase := log_node_product_le_truncated_sum Y U hUY z ε hε hz
  have hcount' : (Y.card : ℝ) ≤ (U.card : ℝ) + D := by exact_mod_cast hcard
  have hcount : (Y.card : ℝ) - U.card ≤ D := by linarith
  have hlog : 0 ≤ -Real.log ε := by
    have h := Real.log_nonpos hε.le hε1
    linarith
  exact hbase.trans (add_le_add_left (mul_le_mul_of_nonneg_right hcount hlog) _)

end Erdos1152
