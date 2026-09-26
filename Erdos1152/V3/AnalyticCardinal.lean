import Erdos1152.V3.LogKernel

/-!
# Finite analytic cardinal growth: actual source, actual polynomial, actual exceptional set

This file proves finite inequalities from quantitative finite data. In particular,
`finite_cardinal_growth_with_error_bound` does not assume `CardinalGrowthOn`.
The analytic weak-limit construction supplying its finite hypotheses is not
asserted here. Build status is recorded by the canonical driver.
-/

open Polynomial MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V3

/-- Normalize by the original row size, not the number of surviving nodes. -/
noncomputable def finiteLogPotential (Y : Finset ℝ) (N x : ℝ) : ℝ :=
  (∑ y ∈ Y, Real.log |x - y|) / N

theorem measurable_finiteLogPotential (Y : Finset ℝ) (N : ℝ) :
    Measurable (finiteLogPotential Y N) := by
  unfold finiteLogPotential
  fun_prop

/-- No separation lower bound on the original nodes is assumed. -/
theorem exists_surviving_node (X D : Finset ℝ) (V : Set ℝ)
    (hcount : D.card < (X.filter fun x => x ∈ V).card) :
    ∃ z ∈ X \ D, z ∈ V := by
  classical
  by_contra! h
  have hsub : X.filter (fun x => x ∈ V) ⊆ D := by
    intro z hz
    obtain ⟨hzX, hzV⟩ := Finset.mem_filter.mp hz
    by_contra hzD
    exact h z (Finset.mem_sdiff.mpr ⟨hzX, hzD⟩) hzV
  exact (not_le_of_gt hcount) (Finset.card_le_card hsub)

/-- Deletion and removal of the distinguished diagonal term cost `D.card+1`
truncation levels. This selects a concrete surviving source. -/
theorem exists_source_log_bound
    (X D : Finset ℝ) (V : Set ℝ) (N ε b δ : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hcount : D.card < (X.filter fun x => x ∈ V).card)
    (htrunc : ∀ z ∈ X, z ∈ V →
      (∑ y ∈ X, truncatedLogKernel ε z y) ≤ N * (b - δ))
    (hcost : ((D.card : ℝ) + 1) * (-Real.log ε) ≤ N * δ) :
    ∃ z ∈ X \ D, z ∈ V ∧
      Real.log |(nodePolynomial ((X \ D).erase z)).eval z| ≤ N * b := by
  classical
  obtain ⟨z, hz, hzV⟩ := exists_surviving_node X D V hcount
  refine ⟨z, hz, hzV, ?_⟩
  have hcard : X.card ≤ ((X \ D).erase z).card + (D.card + 1) := by
    have h₁ := Finset.card_le_card_sdiff_add_card (s := X) (t := D)
    have h₂ := Finset.card_erase_of_mem hz
    omega
  have hlog := log_node_product_le_truncated_sum_of_card_bound
    X ((X \ D).erase z)
    ((Finset.erase_subset _ _).trans Finset.sdiff_subset)
    z ε hε hε1
    (fun y hy => (Finset.ne_of_mem_erase hy).symm) (D.card + 1) hcard
  have ht := htrunc z (Finset.mem_sdiff.mp hz).1 hzV
  push_cast at hlog
  nlinarith

/-- Only points off the finite node set are used in logarithmic identities. -/
theorem log_numerator_eq (Y : Finset ℝ) (z x N : ℝ)
    (hz : z ∈ Y) (hx : x ∉ Y) (hN : N ≠ 0) :
    Real.log |(nodePolynomial (Y.erase z)).eval x| =
      N * finiteLogPotential Y N x - Real.log |x - z| := by
  have hn : ∀ y ∈ Y.erase z, x ≠ y := by
    intro y hy hxy
    exact hx (hxy.symm ▸ Finset.mem_of_mem_erase hy)
  rw [log_abs_nodePolynomial_eval _ _ hn]
  have hs := Finset.add_sum_erase Y (fun y => Real.log |x - y|) hz
  have hc : N * finiteLogPotential Y N x = ∑ y ∈ Y, Real.log |x - y| := by
    dsimp [finiteLogPotential]
    field_simp [hN]
  rw [hc]
  linarith

/-- Pay the bounded factor `|x-z|≤2` with half of the exponential gap. -/
theorem cardinal_growth_of_potential_bounds
    (Y : Finset ℝ) (z x N b η : ℝ)
    (hY : ∀ y ∈ Y, y ∈ Segment) (hz : z ∈ Y)
    (hx : x ∈ Segment) (hxY : x ∉ Y) (hN : 0 < N)
    (hden : Real.log |(nodePolynomial (Y.erase z)).eval z| ≤ N * b)
    (hnum : b + 2 * η ≤ finiteLogPotential Y N x)
    (hpay : Real.log 2 ≤ η * N) :
    Real.exp (η * N) ≤ |(cardinalPolynomial Y z).eval x| := by
  have hneq : x ≠ z := fun h => hxY (h.symm ▸ hz)
  have hzseg := hY z hz
  have hdist : |x - z| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2, hzseg.1, hzseg.2]
  have hlogdist : Real.log |x - z| ≤ Real.log 2 :=
    Real.log_le_log (abs_pos.mpr (sub_ne_zero.mpr hneq)) hdist
  have hid := log_numerator_eq Y z x N hz hxY hN.ne'
  have hnum' := mul_le_mul_of_nonneg_left hnum hN.le
  have hnonzero : (nodePolynomial (Y.erase z)).eval x ≠ 0 := by
    rw [nodePolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    apply sub_ne_zero.mpr
    intro hxy
    exact hxY (hxy.symm ▸ Finset.mem_of_mem_erase hy)
  have hdenzero : (nodePolynomial (Y.erase z)).eval z ≠ 0 := by
    rw [nodePolynomial_eval]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm
  have hgap : η * N + Real.log |(nodePolynomial (Y.erase z)).eval z| ≤
      Real.log |(nodePolynomial (Y.erase z)).eval x| := by nlinarith
  have he := Real.exp_le_exp.mpr hgap
  rw [Real.exp_add, Real.exp_log (abs_pos.mpr hdenzero),
    Real.exp_log (abs_pos.mpr hnonzero)] at he
  have hratio : Real.exp (η * N) ≤
      |(nodePolynomial (Y.erase z)).eval x| /
        |(nodePolynomial (Y.erase z)).eval z| :=
    (le_div_iff₀ (abs_pos.mpr hdenzero)).mpr he
  simpa only [cardinalPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    abs_mul, abs_inv, div_eq_mul_inv, mul_comm] using hratio

/-- A fixed region, independent of the finite deletion. -/
def highRegion (U : ℝ → ℝ) (c : ℝ) : Set ℝ :=
  Segment ∩ {x | c ≤ U x}

/-- Finite node exceptions are explicitly removed, including the source itself. -/
def cardinalGoodSet (U : ℝ → ℝ) (c η : ℝ) (Y : Finset ℝ) (N : ℝ) : Set ℝ :=
  {x ∈ highRegion U c | |finiteLogPotential Y N x - U x| ≤ η} \ (Y : Set ℝ)

theorem measurable_highRegion (U : ℝ → ℝ) (hU : Measurable U) (c : ℝ) :
    MeasurableSet (highRegion U c) :=
  measurableSet_Icc.inter (measurableSet_le measurable_const hU)

theorem measurable_cardinalGoodSet (U : ℝ → ℝ) (hU : Measurable U)
    (c η : ℝ) (Y : Finset ℝ) (N : ℝ) :
    MeasurableSet (cardinalGoodSet U c η Y N) := by
  exact ((measurable_highRegion U hU c).inter
    (measurableSet_le (continuous_abs.measurable.comp
      ((measurable_finiteLogPotential Y N).sub hU))
      measurable_const)).diff Y.finite_toSet.measurableSet

theorem cardinalGoodSet_subset (U : ℝ → ℝ) (c η : ℝ) (Y : Finset ℝ) (N : ℝ) :
    cardinalGoodSet U c η Y N ⊆ highRegion U c :=
  fun _ hx => hx.1.1

/-- Explicit exceptional-measure bound. Integrability is not hidden: the
inequality is also valid when its displayed error integral is infinite. -/
theorem cardinalGoodSet_error_measure
    (U : ℝ → ℝ) (hU : Measurable U) (c η : ℝ)
    (Y : Finset ℝ) (N : ℝ) :
    ENNReal.ofReal η * volume (highRegion U c \ cardinalGoodSet U c η Y N) ≤
      ∫⁻ x in Segment, ENNReal.ofReal |finiteLogPotential Y N x - U x| := by
  classical
  let F : ℝ → ℝ≥0∞ := fun x =>
    ENNReal.ofReal |finiteLogPotential Y N x - U x|
  let Z : Set ℝ := {x | ENNReal.ofReal η ≤ F x}
  have hF : Measurable F :=
    ENNReal.continuous_ofReal.measurable.comp
      (continuous_abs.measurable.comp ((measurable_finiteLogPotential Y N).sub hU))
  have hZ : MeasurableSet Z := measurableSet_le measurable_const hF
  have hcover : highRegion U c \ cardinalGoodSet U c η Y N ⊆
      (Y : Set ℝ) ∪ (Z ∩ Segment) := by
    intro x hx
    by_cases hxy : x ∈ Y
    · exact Or.inl hxy
    · apply Or.inr
      have herr : η < |finiteLogPotential Y N x - U x| := by
        by_contra! he
        exact hx.2 ⟨⟨hx.1, he⟩, hxy⟩
      exact ⟨ENNReal.ofReal_le_ofReal herr.le, hx.1.1⟩
  have hmeasure : volume (highRegion U c \ cardinalGoodSet U c η Y N) ≤
      (volume.restrict Segment) Z := by
    calc
      _ ≤ volume ((Y : Set ℝ) ∪ (Z ∩ Segment)) := measure_mono hcover
      _ ≤ volume (Y : Set ℝ) + volume (Z ∩ Segment) := measure_union_le _ _
      _ = (volume.restrict Segment) Z := by
        rw [Y.measure_zero volume, zero_add, Measure.restrict_apply hZ]
  exact (mul_le_mul_right hmeasure (ENNReal.ofReal η)).trans
    (mul_meas_ge_le_lintegral (μ := volume.restrict Segment) hF (ENNReal.ofReal η))

/-- The complete finite analytic step: a surviving source, its actual cardinal
polynomial, and an explicit bad-set estimate. No abstract cardinal-growth
hypothesis or Remez hypothesis occurs in this statement. -/
theorem finite_cardinal_growth_with_error_bound
    (X D : Finset ℝ) (V : Set ℝ) (U : ℝ → ℝ)
    (N ε b δ η : ℝ) (hN : 0 < N) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hU : Measurable U) (hX : ∀ x ∈ X, x ∈ Segment)
    (hcount : D.card < (X.filter fun x => x ∈ V).card)
    (htrunc : ∀ z ∈ X, z ∈ V →
      (∑ y ∈ X, truncatedLogKernel ε z y) ≤ N * (b - δ))
    (hcost : ((D.card : ℝ) + 1) * (-Real.log ε) ≤ N * δ)
    (hpay : Real.log 2 ≤ η * N) :
    ∃ z ∈ X \ D, z ∈ V ∧
      (∀ x ∈ cardinalGoodSet U (b + 3 * η) η (X \ D) N,
        Real.exp (η * N) ≤ |(cardinalPolynomial (X \ D) z).eval x|) ∧
      ENNReal.ofReal η *
          volume (highRegion U (b + 3 * η) \
            cardinalGoodSet U (b + 3 * η) η (X \ D) N) ≤
        ∫⁻ x in Segment,
          ENNReal.ofReal |finiteLogPotential (X \ D) N x - U x| := by
  obtain ⟨z, hz, hzV, hden⟩ :=
    exists_source_log_bound X D V N ε b δ hε hε1 hcount htrunc hcost
  refine ⟨z, hz, hzV, ?_, cardinalGoodSet_error_measure U hU _ _ _ _⟩
  intro x hx
  apply cardinal_growth_of_potential_bounds (X \ D) z x N b η
    (fun y hy => hX y (Finset.mem_sdiff.mp hy).1) hz
    hx.1.1.1 hx.2 hN hden ?_ hpay
  have hhigh : b + 3 * η ≤ U x := hx.1.1.2
  have he := (abs_le.mp hx.1.2).1
  linarith

/-- High-region multiplicative budget: the extra +1 is necessary. -/
theorem high_multiplier_degree (X D : Finset ℝ) (z : ℝ) (p : ℝ[X])
    (r : ℕ) (hz : z ∈ X \ D) (hp : p.natDegree ≤ X.card + r)
    (hpz : p.eval z = 1)
    (hpzero : ∀ y ∈ (X \ D).erase z, p.eval y = 0) :
    ∃ R : ℝ[X], p = cardinalPolynomial (X \ D) z * R ∧
      R.eval z = 1 ∧ R.natDegree ≤ r + D.card + 1 := by
  have hcount := Finset.card_le_card_sdiff_add_card (s := X) (t := D)
  have hp' : p.natDegree ≤ (X \ D).card + (r + D.card) := by omega
  exact cardinal_factorization (X \ D) z hz p (r + D.card) hp' hpz hpzero

/-- Minimum-region additive budget: there is no extra +1. -/
theorem minimal_quotient_degree (X D : Finset ℝ) (F p : ℝ[X]) (r : ℕ)
    (hF : F.natDegree ≤ (X \ D).card - 1)
    (hp : p.natDegree ≤ X.card + r)
    (hvalues : ∀ y ∈ X \ D, p.eval y = F.eval y) :
    ∃ q : ℝ[X], p = F + nodePolynomial (X \ D) * q ∧
      q.natDegree ≤ r + D.card := by
  have hcount := Finset.card_le_card_sdiff_add_card (s := X) (t := D)
  apply interpolation_correction (X \ D) F p (r + D.card)
  · omega
  · omega
  · exact hvalues

end Erdos1152.V3
