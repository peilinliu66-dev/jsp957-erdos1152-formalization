import Erdos1152.Stage
import Mathlib.MeasureTheory.Measure.Real

/-! The local analytic input, stated on the nodes whose values have not yet been assigned. -/

open Polynomial MeasureTheory Set

namespace Erdos1152

/-- Local amplification on a fixed interval, after removing any finite set of assigned nodes. -/
def LocalIntervalData (X : NodeArray) (r : ℕ → ℕ) (H c a b : ℝ) : Prop :=
  ∀ S : Finset Segment, ∀ N : ℕ, ∃ n ≥ N, ∃ v : Segment → ℝ,
    (∀ i, X.node n i ∉ S → |v (X.node n i)| ≤ 1) ∧
    ∀ p : ℝ[X], p.natDegree ≤ n + 1 + r n →
      (∀ i, X.node n i ∉ S → p.eval (X.node n i : ℝ) = v (X.node n i)) →
      volume.real ({x | |p.eval x| ≤ H} ∩ Ioo a b) ≤ (1 - c) * volume.real (Ioo a b)

/-- The local conclusion of Sections 4--6, before the finite construction. -/
def LocalAmplification (X : NodeArray) (r : ℕ → ℕ) : Prop :=
  ∀ H : ℝ, 1 < H → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1), ∀ ε > (0 : ℝ),
      ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧ LocalIntervalData X r H c (x - h) (x + h)

theorem LocalIntervalData.extend (X : NodeArray) (r : ℕ → ℕ) (H c a b : ℝ)
    (hlocal : LocalIntervalData X r H c a b) (N : ℕ) (S : Stage X) (hS : S.Above N) :
    ∃ T : Stage X, S.Extends T ∧ T.Above N ∧
      ∀ p : ℕ → ℝ[X], T.Fits r p →
        volume.real (commonLowSet T.rows p H ∩ Ioo a b) ≤ (1 - c) * volume.real (Ioo a b) := by
  classical
  obtain ⟨n, hn, v, hv, hforce⟩ := hlocal S.data.domain N
  let Y := Finset.univ.image (X.node n)
  have hv' : ∀ x ∈ Y \ S.data.domain, |v x| ≤ 1 := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hx).1
    exact hv i (Finset.mem_sdiff.mp hx).2
  let D := S.data.append Y v hv'
  let T : Stage X := {
    rows := insert n S.rows
    data := D
    nodes_mem := by
      intro m hm i
      rcases Finset.mem_insert.mp hm with rfl | hm
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      · exact Finset.mem_union.mpr (Or.inl (S.nodes_mem m hm i)) }
  have hST : S.Extends T := ⟨Finset.subset_insert _ _, S.data.extends_append Y v hv'⟩
  refine ⟨T, hST, ?_, fun p hp => ?_⟩
  · intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact hn
    · exact hS m hm
  · have hpn := hp n (Finset.mem_insert_self _ _)
    have hnvalues : ∀ i, X.node n i ∉ S.data.domain →
        (p n).eval (X.node n i : ℝ) = v (X.node n i) := by
      intro i hi
      rw [hpn.2 i]
      exact S.data.append_new_value Y v hv' hi
    apply le_trans (measureReal_mono ?_ (measure_ne_top_of_subset inter_subset_right (by simp)))
      (hforce (p n) hpn.1 hnvalues)
    rintro x ⟨hx, hxab⟩
    exact ⟨hx.2 n (Finset.mem_insert_self _ _), hxab⟩

end Erdos1152
