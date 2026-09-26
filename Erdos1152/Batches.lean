import Erdos1152.Stage
import Erdos1152.Contraction

/-! The finite construction for common low sets in Proposition 11. -/

open Set MeasureTheory Polynomial

namespace Erdos1152

/-- The interval conclusion obtained by applying Vitali covering to local amplification. -/
def IntervalAmplification (X : NodeArray) (r : ℕ → ℕ) (H c : ℝ) (N : ℕ) : Prop :=
  ∀ S : Stage X, S.Above N → ∀ a b : ℝ, -1 ≤ a → a < b → b ≤ 1 →
    ∃ T : Stage X, S.Extends T ∧ T.Above N ∧
      ∀ p : ℕ → ℝ[X], T.Fits r p →
        volume.real (commonLowSet T.rows p H ∩ Ioo a b) ≤
          (1 - c) * volume.real (Ioo a b)

theorem extend_over_intervals {ι : Type*} (X : NodeArray) (r : ℕ → ℕ) (H c : ℝ) (N : ℕ)
    (hamp : IntervalAmplification X r H c N) (S : Stage X) (hS : S.Above N)
    (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, -1 ≤ a i ∧ a i < b i ∧ b i ≤ 1) :
    ∃ T : Stage X, S.Extends T ∧ T.Above N ∧
      ∀ p : ℕ → ℝ[X], T.Fits r p → ∀ i ∈ s,
        volume.real (commonLowSet T.rows p H ∩ Ioo (a i) (b i)) ≤
          (1 - c) * volume.real (Ioo (a i) (b i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, Stage.Extends.refl S, hS, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨T, hST, hT, hTp⟩ := ih (fun j hj => hab j (Finset.mem_insert_of_mem hj))
    have hi' := hab i (Finset.mem_insert_self i s)
    obtain ⟨U, hTU, hU, hUp⟩ := hamp T hT (a i) (b i) hi'.1 hi'.2.1 hi'.2.2
    refine ⟨U, hST.trans hTU, hU, fun p hp j hj => ?_⟩
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hUp p hp
    · apply le_trans (measureReal_mono (inter_subset_inter_left _ (hTU.lowSet_subset p H))
        (measure_ne_top_of_subset inter_subset_right (by simp)))
      exact hTp p (hp.restrict hTU) j hj

theorem one_batch (X : NodeArray) (r : ℕ → ℕ) (H c δ : ℝ) (N : ℕ)
    (hc : 0 ≤ c) (hδ : 0 < δ) (hamp : IntervalAmplification X r H c N)
    (S : Stage X) (hS : S.Above N) :
    ∃ T : Stage X, S.Extends T ∧ T.Above N ∧
      ∀ p : ℕ → ℝ[X], T.Fits r p → δ ≤ volume.real (commonLowSet S.rows p H) →
        volume.real (commonLowSet T.rows p H) ≤
          (1 - 3 * c / 4) * volume.real (commonLowSet S.rows p H) := by
  obtain ⟨m, a, hm, ha, hleft, hright, hpart⟩ :=
    exists_uniform_partition (2 + 2 * ∑ n ∈ S.rows, (n + 1 + r n)) (δ / 4) (by positivity)
  obtain ⟨T, hST, hT, hcells⟩ := extend_over_intervals X r H c N hamp S hS (Finset.range m)
    a (fun i => a (i + 1)) (by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      refine ⟨?_, ha (Nat.lt_succ_self i), ?_⟩
      · rw [← hleft]
        exact ha.monotone (Nat.zero_le i)
      · rw [← hright]
        exact ha.monotone (by omega))
  refine ⟨T, hST, hT, fun p hp hsize => ?_⟩
  have hcover := hpart (commonLowSet S.rows p H) inter_subset_left
    (S.boundary_cover r p (hp.restrict hST) H)
  apply partition_contraction m a ha (commonLowSet S.rows p H) (commonLowSet T.rows p H)
    inter_subset_left (hST.lowSet_subset p H) (commonLowSet_measurable _ _ _) c hc
    (fun i hi => hcells p hp i (Finset.mem_range.mpr hi))
  linarith

end Erdos1152
