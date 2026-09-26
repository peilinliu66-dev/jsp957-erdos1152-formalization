import Erdos1152.CoarseAmplification
import Erdos1152.CardinalLocal

/-! Adaptation of upstream CardinalLocal: the coarse Remez theorem is supplied
by proof rather than a caller. CardinalGrowthCover is STILL an explicit,
unproved analytic input at the terminal theorem. Build status is recorded by the canonical driver. -/
open Polynomial MeasureTheory Set Filter Topology Metric
open scoped ENNReal
namespace Erdos1152

private theorem coarse_sublinear_add_const (r : ℕ → ℕ) (C : ℕ)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ((r n + C : ℕ) : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  simpa [add_div, div_eq_mul_inv, add_mul] using
    hr.add ((tendsto_inv_atTop_zero.comp ht).const_mul (C : ℝ))

/-- Once a region occupies at least three quarters of an interval, the Remez
deduction gives local data forcing large values on half of that interval. -/
theorem localIntervalData_of_cardinalGrowth_coarse (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (A : Set ℝ) (hAsub : A ⊆ Segment) (hg : CardinalGrowthOn X A)
    (H a b : ℝ) (hH : 0 < H) (hab : a < b)
    (hfill : volume.real (Ioo a b \ A) ≤ volume.real (Ioo a b) / 4) :
    LocalIntervalData X r H (1 / 2) a b := by
  classical
  intro S N
  obtain ⟨rows, hrows, z, hz, η, hη, E, hE, hbad, hgrowth⟩ := hg S
  have hzseg (n : ℕ) : z n ∈ Segment := by
    obtain ⟨i, _, he⟩ := (mem_unassignedNodes X S (rows n) (z n)).mp (hz n)
    exact he ▸ (X.node (rows n) i).property
  have hlen : 0 < volume.real (Ioo a b) := by
    rw [Real.volume_real_Ioo_of_le hab.le]
    exact sub_pos.mpr hab
  have he := eventually_cardinal_amplification_of_measure_convergence_coarse rows hrows
    (fun n => unassignedNodes X S (rows n)) z (fun n => r n + S.card) A E hz hzseg
    hAsub (fun n => (hE n).1) (fun n => (hE n).2) H η hH hη
    (coarse_sublinear_add_const r S.card hr) hbad hgrowth (volume.real (Ioo a b) / 4) (by positivity)
  obtain ⟨j, hj, hjN⟩ := (he.and (hrows.eventually (eventually_ge_atTop N))).exists
  let v : Segment → ℝ := fun x => if (x : ℝ) = z j then 1 else 0
  refine ⟨rows j, hjN, v, ?_, ?_⟩
  · intro i hi
    dsimp [v]
    split_ifs <;> norm_num
  · intro p hp hv
    have hdeg : p.natDegree ≤ (unassignedNodes X S (rows j)).card + (r (rows j) + S.card) := by
      have := unassignedNodes_card X S (rows j)
      omega
    have hpz : p.eval (z j) = 1 := by
      obtain ⟨i, hi, hiZ⟩ := (mem_unassignedNodes X S (rows j) (z j)).mp (hz j)
      simpa [v, hiZ] using hv i hi
    have hpzero : ∀ y ∈ (unassignedNodes X S (rows j)).erase (z j), p.eval y = 0 := by
      intro y hy
      obtain ⟨i, hi, hiy⟩ := (mem_unassignedNodes X S (rows j) y).mp (Finset.mem_of_mem_erase hy)
      simpa [v, hiy, Finset.ne_of_mem_erase hy] using hv i hi
    have hlow := hj p hdeg hpz hpzero
    have hcover : {x | |p.eval x| ≤ H} ∩ Ioo a b ⊆
        {x ∈ A | |p.eval x| ≤ H} ∪ (Ioo a b \ A) := by
      intro x hx
      by_cases hxa : x ∈ A
      · exact Or.inl ⟨hxa, hx.1⟩
      · exact Or.inr ⟨hx.2, hxa⟩
    have hf1 : volume {x ∈ A | |p.eval x| ≤ H} ≠ ⊤ :=
      measure_ne_top_of_subset (fun _ hx => hAsub hx.1) (by simp [Segment])
    have hf2 : volume (Ioo a b \ A) ≠ ⊤ := measure_ne_top_of_subset sdiff_subset (by simp)
    have hb := (measureReal_mono hcover (measure_union_lt_top hf1.lt_top hf2.lt_top).ne).trans
      (measureReal_union_le _ _)
    linarith

theorem localAmplificationAbove_of_cardinalGrowthCover_coarse (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (A : Set ℝ) (hg : CardinalGrowthCover X A) : LocalAmplificationAbove X r A := by
  obtain ⟨B, hB, hcover⟩ := hg
  have hd (j : ℕ) : ∀ᵐ x ∂volume, x ∈ B j → ∀ ε > (0 : ℝ),
      ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧
        volume.real (Ioo (x - h) (x + h) \ B j) ≤
          volume.real (Ioo (x - h) (x + h)) / 4 :=
    ae_imp_of_ae_restrict (ae_small_interval_complement (B j) (hB j).1)
  have hdall := ae_all_iff.mpr hd
  intro H hH
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hcover, ae_restrict_of_ae hdall] with x hx hdx
  intro hxa ε hε
  obtain ⟨j, hxj⟩ := hx hxa
  obtain ⟨h, hh, hhe, hfill⟩ := hdx j hxj ε hε
  refine ⟨h, hh, hhe, ?_⟩
  exact localIntervalData_of_cardinalGrowth_coarse X r hr (B j) (hB j).2.1 (hB j).2.2
    H (x - h) (x + h) (by linarith) (by linarith) hfill


end Erdos1152
