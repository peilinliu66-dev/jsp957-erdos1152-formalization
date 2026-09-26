import Erdos1152.Interpolation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Polynomial

/-! The Remez step above the minimum-potential set (Section 6.1).
The classical inequality is kept separate from the polynomial factorization and
its application. This module does not assume the local amplification conclusion. -/

open Polynomial MeasureTheory Set Filter Topology

namespace Erdos1152

/-- The standard exponential consequence of Remez's inequality on `[-1,1]`.
Remez, Comm. Inst. Sci. Math. Méc. Kharkoff 13 (1936), p. 93, (3)--(4):
the Chebyshev bound implies the factor `(8 / |E|)^degree` used here.
The reduction from the Chebyshev form is proved below. -/
def RemezInequality : Prop :=
  ∀ (p : ℝ[X]) (E : Set ℝ) (H : ℝ), MeasurableSet E → E ⊆ Icc (-1) 1 →
    0 < volume.real E → 0 ≤ H → (∀ x ∈ E, |p.eval x| ≤ H) →
    ∀ z ∈ Icc (-1) 1, |p.eval z| ≤ H * (8 / volume.real E) ^ p.natDegree

/-- Remez's classical Chebyshev bound, on the interval `[-1,1]`.
Reference: Remes (1936), p. 93, (3)--(4), with interval length `2` and `λ = |E|`.
This published inequality is the external hypothesis of the Remez step. -/
def RemezChebyshevInequality : Prop :=
  ∀ (p : ℝ[X]) (E : Set ℝ) (H : ℝ), MeasurableSet E → E ⊆ Icc (-1) 1 →
    0 < volume.real E → 0 ≤ H → (∀ x ∈ E, |p.eval x| ≤ H) →
    ∀ z ∈ Icc (-1) 1, |p.eval z| ≤
      H * (Polynomial.Chebyshev.T ℝ (p.natDegree : ℤ)).eval (4 / volume.real E - 1)

private lemma chebyshev_le_two_mul_pow (n : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x ≤ (2 * x) ^ n := by
  have ht : 0 ≤ (n : ℝ) * Real.arcosh x := mul_nonneg (Nat.cast_nonneg _) (Real.arcosh_nonneg hx)
  have he : Real.exp (Real.arcosh x) ≤ 2 * x := by
    rw [Real.exp_arcosh hx]
    have hs : Real.sqrt (x ^ 2 - 1) ≤ x := by
      apply (Real.sqrt_le_left (by linarith)).mpr
      linarith
    linarith
  calc
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval x = Real.cosh ((n : ℝ) * Real.arcosh x) := by
      conv_lhs => rw [← Real.cosh_arcosh hx]
      simp only [Polynomial.Chebyshev.T_real_cosh, Int.cast_natCast]
    _ ≤ Real.exp ((n : ℝ) * Real.arcosh x) := by
      rw [Real.cosh_eq]
      have := Real.exp_le_exp.mpr (show -((n : ℝ) * Real.arcosh x) ≤ (n : ℝ) * Real.arcosh x by linarith)
      linarith
    _ = Real.exp (Real.arcosh x) ^ n := Real.exp_nat_mul _ _
    _ ≤ (2 * x) ^ n := pow_le_pow_left₀ (Real.exp_pos _).le he _

/-- The exact classical input implies the exponential estimate used in Section 6.1. -/
theorem remezInequality_of_chebyshev (hR : RemezChebyshevInequality) : RemezInequality := by
  intro p E H hE hEsub hEpos hH hp z hz
  have hE2 : volume.real E ≤ 2 := by
    convert measureReal_mono (μ := volume) hEsub (by simp) using 1
    norm_num
  have hx : 1 ≤ 4 / volume.real E - 1 := by
    have : 2 ≤ 4 / volume.real E := (le_div_iff₀ hEpos).mpr (by linarith)
    linarith
  have hb := chebyshev_le_two_mul_pow p.natDegree hx
  have hc : 2 * (4 / volume.real E - 1) ≤ 8 / volume.real E := by ring_nf; linarith
  exact (hR p E H hE hEsub hEpos hH hp z hz).trans
    (mul_le_mul_of_nonneg_left (hb.trans (pow_le_pow_left₀ (by linarith) hc _)) hH)

/-- The cardinal polynomial for the distinguished node `z`. -/
noncomputable def cardinalPolynomial (Y : Finset ℝ) (z : ℝ) : ℝ[X] :=
  nodePolynomial (Y.erase z) * C ((nodePolynomial (Y.erase z)).eval z)⁻¹

private lemma nodePolynomial_erase_eval_ne_zero (Y : Finset ℝ) (z : ℝ) :
    (nodePolynomial (Y.erase z)).eval z ≠ 0 := by
  classical
  rw [nodePolynomial_eval]
  apply Finset.prod_ne_zero_iff.mpr
  intro y hy
  exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm

/-- All interpolants of one-at-`z`, zero-at-the-other-nodes data have the
factorization used in (6.2), with the excess-degree budget explicit. -/
theorem cardinal_factorization (Y : Finset ℝ) (z : ℝ) (hz : z ∈ Y)
    (p : ℝ[X]) (d : ℕ) (hp : p.natDegree ≤ Y.card + d)
    (hpz : p.eval z = 1) (hzero : ∀ y ∈ Y.erase z, p.eval y = 0) :
    ∃ T : ℝ[X], p = cardinalPolynomial Y z * T ∧ T.eval z = 1 ∧ T.natDegree ≤ d + 1 := by
  classical
  obtain ⟨q, hq⟩ := (nodePolynomial_dvd_iff (Y.erase z) p).mpr hzero
  let c := (nodePolynomial (Y.erase z)).eval z
  have hc : c ≠ 0 := nodePolynomial_erase_eval_ne_zero Y z
  have hq0 : q ≠ 0 := by
    intro h
    simp [hq, h] at hpz
  refine ⟨C c * q, ?_, ?_, ?_⟩
  · change p = (nodePolynomial (Y.erase z) * C c⁻¹) * (C c * q)
    rw [mul_assoc, ← mul_assoc (C c⁻¹), ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul]
    exact hq
  · rw [eval_mul, eval_C]
    simpa only [hq, eval_mul] using hpz
  · have hdeg : p.natDegree = (Y.erase z).card + q.natDegree := by
      rw [hq, (nodePolynomial_monic _).natDegree_mul' hq0, nodePolynomial_natDegree]
    have hcY : (Y.erase z).card + 1 = Y.card := Finset.card_erase_add_one hz
    calc
      (C c * q).natDegree ≤ q.natDegree := natDegree_C_mul_le _ _
      _ ≤ d + 1 := by omega

/-- Exponential growth of a cardinal factor makes every corrected interpolant
large except on a set of small measure. The Remez assumption is used only on `T`. -/
theorem low_set_measure_lt_of_remez (hR : RemezInequality)
    (b T : ℝ[X]) (E : Set ℝ) (z H B μ : ℝ)
    (hE : MeasurableSet E) (hEsub : E ⊆ Icc (-1) 1)
    (hz : z ∈ Icc (-1) 1) (hTz : T.eval z = 1)
    (hH : 0 ≤ H) (hB : 0 < B) (hμ : 0 < μ)
    (hgrowth : ∀ x ∈ E, B ≤ |b.eval x|)
    (hsmall : H / B * (8 / μ) ^ T.natDegree < 1) :
    volume.real {x ∈ E | |(b * T).eval x| ≤ H} < μ := by
  let L := {x ∈ E | |(b * T).eval x| ≤ H}
  have hpmeas : MeasurableSet {x : ℝ | |(b * T).eval x| ≤ H} :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hLm : MeasurableSet L := hE.inter hpmeas
  have hLs : L ⊆ Icc (-1) 1 := fun x hx => hEsub hx.1
  by_contra h
  have hlarge : μ ≤ volume.real L := le_of_not_gt h
  have hlpos : 0 < volume.real L := hμ.trans_le hlarge
  have hbound : ∀ x ∈ L, |T.eval x| ≤ H / B := by
    intro x hx
    apply (le_div_iff₀ hB).mpr
    have hp : |b.eval x| * |T.eval x| ≤ H := by simpa [eval_mul, abs_mul] using hx.2
    nlinarith [hgrowth x hx.1, abs_nonneg (T.eval x)]
  have hr := hR T L (H / B) hLm hLs hlpos (div_nonneg hH hB.le) hbound z hz
  rw [hTz, abs_one] at hr
  have hpow : (8 / volume.real L) ^ T.natDegree ≤ (8 / μ) ^ T.natDegree := by
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_left (by norm_num) hμ hlarge) _
  have := mul_le_mul_of_nonneg_left hpow (div_nonneg hH hB.le)
  linarith

/-- A sublinear correction degree cannot cancel a fixed exponential gain. -/
theorem eventually_remez_factor_lt_one (d : ℕ → ℕ) (H C η : ℝ)
    (hH : 0 < H) (hC : 0 < C) (hη : 0 < η)
    (hd : Tendsto (fun n => (d n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, H / Real.exp (η * (n + 1)) * C ^ d n < 1 := by
  have hlim : Tendsto (fun n => (d n : ℝ) / (n + 1 : ℝ) * Real.log C) atTop (𝓝 0) := by
    simpa using hd.mul_const (Real.log C)
  have he := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η / 2))
  have ht1 : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun n : ℕ => (η / 2) * (n + 1 : ℝ)) atTop atTop :=
    ht1.const_mul_atTop (by positivity)
  filter_upwards [he, ht.eventually (eventually_gt_atTop (Real.log H))] with n hn hlog
  have hnpos : (0 : ℝ) < n + 1 := by positivity
  have hdn : (d n : ℝ) * Real.log C < (η / 2) * (n + 1) := by
    apply (div_lt_iff₀ hnpos).mp
    simpa [div_mul_eq_mul_div] using hn
  have hl : Real.log H - η * (n + 1) + (d n : ℝ) * Real.log C < 0 := by linarith
  rw [← Real.exp_log hH, ← Real.exp_log hC, ← Real.exp_nat_mul,
    ← Real.exp_sub, ← Real.exp_add, Real.exp_lt_one_iff]
  exact hl

/-- Section 6.1 after the potential-theoretic growth estimate: every admissible
interpolant is large on all but an arbitrarily small measure of `E`. -/
theorem eventually_cardinal_amplification (hR : RemezChebyshevInequality)
    (rows : ℕ → ℕ) (hrows : Tendsto rows atTop atTop)
    (Y : ℕ → Finset ℝ) (z : ℕ → ℝ) (d : ℕ → ℕ) (E : ℕ → Set ℝ)
    (hzY : ∀ n, z n ∈ Y n) (hz : ∀ n, z n ∈ Icc (-1) 1)
    (hE : ∀ n, MeasurableSet (E n)) (hEsub : ∀ n, E n ⊆ Icc (-1) 1)
    (H η μ : ℝ) (hH : 0 < H) (hη : 0 < η) (hμ : 0 < μ) (hμ2 : μ ≤ 2)
    (hd : Tendsto (fun n => (d n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (hgrowth : ∀ᶠ n : ℕ in atTop, ∀ x ∈ E n,
      Real.exp (η * (rows n + 1)) ≤ |(cardinalPolynomial (Y n) (z n)).eval x|) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ[X], p.natDegree ≤ (Y n).card + d (rows n) →
      p.eval (z n) = 1 → (∀ y ∈ (Y n).erase (z n), p.eval y = 0) →
      volume.real {x ∈ E n | |p.eval x| ≤ H} < μ := by
  have ht : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hd1 : Tendsto (fun n => ((d n + 1 : ℕ) : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [add_div, one_div] using hd.add (tendsto_inv_atTop_zero.comp ht)
  have hsmall := eventually_remez_factor_lt_one (fun n => d n + 1) H (8 / μ) η
    hH (by positivity) hη hd1
  filter_upwards [hgrowth, hrows.eventually hsmall] with n hgn hsn
  intro p hp hpz hpzero
  obtain ⟨T, hfactor, hTz, hTd⟩ := cardinal_factorization (Y n) (z n) (hzY n) p (d (rows n)) hp hpz hpzero
  rw [hfactor]
  apply low_set_measure_lt_of_remez (remezInequality_of_chebyshev hR) _ T (E n) (z n) H (Real.exp (η * (rows n + 1))) μ
    (hE n) (hEsub n) (hz n) hTz hH.le (Real.exp_pos _) hμ hgn
  have hC : 1 ≤ 8 / μ := (le_div_iff₀ hμ).mpr (by linarith)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hTd)
    (by positivity)) hsn

/-- The exceptional sets in (6.1) may vary with the row. If their measures tend
to zero, so do the low-set measures, uniformly over all corrected interpolants. -/
theorem eventually_cardinal_amplification_of_measure_convergence
    (hR : RemezChebyshevInequality)
    (rows : ℕ → ℕ) (hrows : Tendsto rows atTop atTop)
    (Y : ℕ → Finset ℝ) (z : ℕ → ℝ) (d : ℕ → ℕ) (A : Set ℝ) (E : ℕ → Set ℝ)
    (hzY : ∀ n, z n ∈ Y n) (hz : ∀ n, z n ∈ Icc (-1) 1)
    (hAsub : A ⊆ Icc (-1) 1)
    (hE : ∀ n, MeasurableSet (E n)) (hEsub : ∀ n, E n ⊆ A)
    (H η : ℝ) (hH : 0 < H) (hη : 0 < η)
    (hd : Tendsto (fun n => (d n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (hbad : Tendsto (fun n => volume.real (A \ E n)) atTop (𝓝 0))
    (hgrowth : ∀ᶠ n : ℕ in atTop, ∀ x ∈ E n,
      Real.exp (η * (rows n + 1)) ≤ |(cardinalPolynomial (Y n) (z n)).eval x|)
    (μ : ℝ) (hμ : 0 < μ) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℝ[X], p.natDegree ≤ (Y n).card + d (rows n) →
      p.eval (z n) = 1 → (∀ y ∈ (Y n).erase (z n), p.eval y = 0) →
      volume.real {x ∈ A | |p.eval x| ≤ H} < μ := by
  let ε := min (μ / 2) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  have he := eventually_cardinal_amplification hR rows hrows Y z d E hzY hz hE
    (fun n => (hEsub n).trans hAsub) H η ε hH hη hε
    ((min_le_right _ _).trans (by norm_num)) hd hgrowth
  filter_upwards [he, hbad.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < μ / 2))]
    with n hn hbn
  intro p hp hpz hpzero
  have hsmall := hn p hp hpz hpzero
  have hcover : {x ∈ A | |p.eval x| ≤ H} ⊆
      {x ∈ E n | |p.eval x| ≤ H} ∪ (A \ E n) := by
    intro x hx
    by_cases he : x ∈ E n
    · exact Or.inl ⟨he, hx.2⟩
    · exact Or.inr ⟨hx.1, he⟩
  have hfinite : volume ({x ∈ E n | |p.eval x| ≤ H} ∪ (A \ E n)) ≠ ⊤ :=
    measure_ne_top_of_subset (show _ ⊆ Icc (-1) 1 from
      fun x hx => hx.elim (fun h => hAsub (hEsub n h.1)) (fun h => hAsub h.1)) (by simp)
  have hb := (measureReal_mono hcover hfinite).trans (measureReal_union_le _ _)
  have heμ : ε ≤ μ / 2 := min_le_left _ _
  linarith

end Erdos1152
