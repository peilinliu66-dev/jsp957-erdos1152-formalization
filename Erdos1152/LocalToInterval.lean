import Erdos1152.LocalData
import Erdos1152.Vitali
import Erdos1152.Batches

/-! From local amplification to the interval estimate used by the finite construction. -/

open Polynomial MeasureTheory Set
open scoped ENNReal

namespace Erdos1152

private theorem finite_interval_loss {ι : Type*} (s : Finset ι) (a b : ι → ℝ)
    (J K : Set ℝ) (hJfin : volume J ≠ ⊤) (hKm : MeasurableSet K)
    (hsub : ∀ i ∈ s, Ioo (a i) (b i) ⊆ J)
    (hd : PairwiseDisjoint (s : Set ι) (fun i => Ioo (a i) (b i))) (c : ℝ)
    (hlow : ∀ i ∈ s, volume.real (K ∩ Ioo (a i) (b i)) ≤
      (1 - c) * volume.real (Ioo (a i) (b i))) :
    volume.real (K ∩ J) ≤ volume.real J - c * ∑ i ∈ s, volume.real (Ioo (a i) (b i)) := by
  let E := ⋃ i ∈ s, Ioo (a i) (b i) \ K
  have hEsub : E ⊆ J \ K := by
    rintro x hx
    obtain ⟨i, hi, hxI, hxK⟩ := mem_iUnion₂.mp hx
    exact ⟨hsub i hi hxI, hxK⟩
  have hE : volume.real E = ∑ i ∈ s, volume.real (Ioo (a i) (b i) \ K) :=
    measureReal_biUnion_finset
      (fun i hi j hj hij => (hd hi hj hij).mono sdiff_subset sdiff_subset)
      (fun _ _ => measurableSet_Ioo.diff hKm)
      (fun _ _ => measure_ne_top_of_subset sdiff_subset (by simp))
  have hremove : c * ∑ i ∈ s, volume.real (Ioo (a i) (b i)) ≤ volume.real E := by
    rw [hE, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hsum := measureReal_inter_add_sdiff (μ := volume) (s := Ioo (a i) (b i)) hKm (by simp)
    rw [inter_comm] at hsum
    linarith [hlow i hi]
  have hupper := measureReal_mono hEsub (measure_ne_top_of_subset sdiff_subset hJfin)
  have htotal := measureReal_inter_add_sdiff (μ := volume) (s := J) hKm hJfin
  rw [inter_comm] at htotal
  linarith

theorem intervalAmplification_of_localData (X : NodeArray) (r : ℕ → ℕ) (H c : ℝ)
    (hc : 0 ≤ c)
    (hlocal : ∀ᵐ x ∂volume.restrict (Ioo (-1) 1), ∀ ε > (0 : ℝ),
      ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧ LocalIntervalData X r H c (x - h) (x + h))
    (N : ℕ) : IntervalAmplification X r H (c / 2) N := by
  intro S hS a b ha hab hb
  have hJsub : Ioo a b ⊆ Ioo (-1 : ℝ) 1 := Ioo_subset_Ioo ha hb
  have hlocalJ := ae_restrict_of_ae_restrict_of_subset hJsub hlocal
  obtain ⟨s, hs, hd, hlength⟩ := finite_disjoint_intervals hab
    (fun x h => LocalIntervalData X r H c (x - h) (x + h)) hlocalJ
  have hstep : ∀ T : Stage X, T.Above N → ∀ z ∈ s,
      ∃ U : Stage X, T.Extends U ∧ U.Above N ∧
        ∀ p : ℕ → ℝ[X], U.Fits r p →
          volume.real (commonLowSet U.rows p H ∩ Ioo (z.1 - z.2) (z.1 + z.2)) ≤
            (1 - c) * volume.real (Ioo (z.1 - z.2) (z.1 + z.2)) := by
    intro T hT z hz
    exact LocalIntervalData.extend X r H c _ _ (hs z hz).2.1 N T hT
  have hbuild (F : Finset (ℝ × ℝ)) (hF : F ⊆ s) :
      ∃ T : Stage X, S.Extends T ∧ T.Above N ∧
        ∀ p : ℕ → ℝ[X], T.Fits r p → ∀ z ∈ F,
          volume.real (commonLowSet T.rows p H ∩ Ioo (z.1 - z.2) (z.1 + z.2)) ≤
            (1 - c) * volume.real (Ioo (z.1 - z.2) (z.1 + z.2)) := by
    classical
    induction F using Finset.induction_on with
    | empty => exact ⟨S, Stage.Extends.refl S, hS, by simp⟩
    | @insert z F hz ih =>
      obtain ⟨T, hST, hT, hpT⟩ := ih (Finset.Subset.trans (Finset.subset_insert _ _) hF)
      obtain ⟨U, hTU, hU, hpU⟩ := hstep T hT z (hF (Finset.mem_insert_self _ _))
      refine ⟨U, hST.trans hTU, hU, fun p hp w hw => ?_⟩
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hpU p hp
      · apply le_trans (measureReal_mono (inter_subset_inter_left _ (hTU.lowSet_subset p H))
          (measure_ne_top_of_subset inter_subset_right (by simp)))
        exact hpT p (hp.restrict hTU) w hw
  obtain ⟨T, hST, hT, hpT⟩ := hbuild s (Finset.Subset.refl _)
  refine ⟨T, hST, hT, fun p hp => ?_⟩
  have hbound := finite_interval_loss s (fun z => z.1 - z.2) (fun z => z.1 + z.2)
    (Ioo a b) (commonLowSet T.rows p H) (by simp) (commonLowSet_measurable _ _ _)
    (fun z hz => Ioo_subset_Icc_self.trans (hs z hz).2.2)
    (fun z hz w hw hzw => (hd hz hw hzw).mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
    c (hpT p hp)
  have hsum : (∑ z ∈ s, volume.real (Ioo (z.1 - z.2) (z.1 + z.2))) =
      ∑ z ∈ s, 2 * z.2 := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [Real.volume_real_Ioo_of_le (by linarith [(hs z hz).1])]
    ring
  rw [hsum] at hbound
  rw [Real.volume_real_Ioo_of_le hab.le] at hbound ⊢
  have := mul_le_mul_of_nonneg_left hlength.le hc
  nlinarith

end Erdos1152
