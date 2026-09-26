import Erdos1152.CoarseRemez
import Erdos1152.RemezAmplification

/-! Adaptation of the supplied upstream RemezAmplification proofs to the
new elementary constant. Original polynomial factorization and the sublinear
exponential lemma are reused, not reproved. The Remez hypothesis is removed;
build status for the resulting source is recorded by the canonical driver. -/

open Polynomial MeasureTheory Set Filter Topology
namespace Erdos1152

theorem low_set_measure_lt_of_coarse_remez
    (b T : ℝ[X]) (E : Set ℝ) (z H B μ : ℝ)
    (hE : MeasurableSet E) (hEsub : E ⊆ Icc (-1) 1)
    (hz : z ∈ Icc (-1) 1) (hTz : T.eval z = 1)
    (hH : 0 ≤ H) (hB : 0 < B) (hμ : 0 < μ)
    (hgrowth : ∀ x ∈ E, B ≤ |b.eval x|)
    (hsmall : H / B * (coarseRemezConstant / μ) ^ T.natDegree < 1) :
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
  have hr := coarse_remez T L (H / B) hLm hLs hlpos (div_nonneg hH hB.le) hbound z hz
  rw [hTz, abs_one] at hr
  have hpow : (coarseRemezConstant / volume.real L) ^ T.natDegree ≤ (coarseRemezConstant / μ) ^ T.natDegree := by
    exact pow_le_pow_left₀ (div_nonneg coarseRemezConstant_pos.le hlpos.le) (div_le_div_of_nonneg_left coarseRemezConstant_pos.le hμ hlarge) _
  have := mul_le_mul_of_nonneg_left hpow (div_nonneg hH hB.le)
  linarith


theorem eventually_cardinal_amplification_coarse
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
  have hsmall := eventually_remez_factor_lt_one (fun n => d n + 1) H (coarseRemezConstant / μ) η
    hH (div_pos coarseRemezConstant_pos hμ) hη hd1
  filter_upwards [hgrowth, hrows.eventually hsmall] with n hgn hsn
  intro p hp hpz hpzero
  obtain ⟨T, hfactor, hTz, hTd⟩ := cardinal_factorization (Y n) (z n) (hzY n) p (d (rows n)) hp hpz hpzero
  rw [hfactor]
  apply low_set_measure_lt_of_coarse_remez _ T (E n) (z n) H (Real.exp (η * (rows n + 1))) μ
    (hE n) (hEsub n) (hz n) hTz hH.le (Real.exp_pos _) hμ hgn
  have hC : 1 ≤ coarseRemezConstant / μ :=
    (le_div_iff₀ hμ).mpr (by linarith [two_le_coarseRemezConstant])
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hC hTd)
    (by positivity)) hsn

/-- The exceptional sets in (6.1) may vary with the row. If their measures tend
to zero, so do the low-set measures, uniformly over all corrected interpolants. -/
theorem eventually_cardinal_amplification_of_measure_convergence_coarse
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
  have he := eventually_cardinal_amplification_coarse rows hrows Y z d E hzY hz hE
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
