import Erdos1152.Nodes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Order.Interval.Set.Union
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! A fixed partition approximates every set with a prescribed finite boundary bound. -/

open Set MeasureTheory
open scoped ENNReal
open Classical

namespace Erdos1152

theorem preconnected_subset_or_frontier {J L : Set ℝ} (hJ : IsPreconnected J)
    (hJL : (J ∩ L).Nonempty) : J ⊆ L ∨ (J ∩ frontier L).Nonempty := by
  by_cases h : (J ∩ frontier L).Nonempty
  · exact Or.inr h
  · left
    have hc : J ⊆ interior L ∪ interior Lᶜ := by
      rw [← compl_frontier_eq_union_interior]
      intro x hx hxf
      exact h ⟨x, hx, hxf⟩
    have hd : Disjoint (interior L) (interior Lᶜ) :=
      disjoint_compl_right.mono interior_subset interior_subset
    rcases hJ.subset_or_subset isOpen_interior isOpen_interior hd hc with hleft | hright
    · exact hleft.trans interior_subset
    · obtain ⟨x, hxJ, hxL⟩ := hJL
      exact ((interior_subset (hright hxJ)) hxL).elim

/-- The cells contained in `L` lose at most two mesh lengths per boundary point. -/
theorem partition_boundary_loss (m : ℕ) (a : ℕ → ℝ)
    (hleft : a 0 = -1) (hright : a m = 1) (ε : ℝ) (hε : 0 ≤ ε)
    (hmesh : ∀ i < m, a (i + 1) - a i ≤ ε)
    (L : Set ℝ) (hL : L ⊆ Segment) (B : Finset ℝ)
    (hB : frontier L ⊆ (B : Set ℝ)) :
    volume.real L ≤
      volume.real (⋃ i ∈ (Finset.range m).filter
        (fun i => Ioo (a i) (a (i + 1)) ⊆ L), Ioo (a i) (a (i + 1))) +
      2 * B.card * ε := by
  classical
  let G := (Finset.range m).filter fun i => Ioo (a i) (a (i + 1)) ⊆ L
  let U := ⋃ i ∈ G, Ioo (a i) (a (i + 1))
  let Z := (Finset.range (m + 1)).image a
  let V := ⋃ b ∈ B, Icc (b - ε) (b + ε)
  have hU : U ⊆ Segment := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    exact hL ((Finset.mem_filter.mp hi).2 hxi)
  have hVfin : volume V ≠ ⊤ := by
    apply ne_of_lt
    apply (measure_biUnion_finset_le B _).trans_lt
    exact ENNReal.sum_lt_top.mpr (fun b _ => by simp)
  have hZfin : volume (Z : Set ℝ) = 0 := Z.finite_toSet.measure_zero volume
  have hsub : L ⊆ U ∪ (V ∪ (Z : Set ℝ)) := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · exact Or.inr (Or.inr hxZ)
    have hxm : x ∈ Ioc (a 0) (a m) := by
      have hbounds := hL hx
      rw [hleft, hright]
      refine ⟨lt_of_le_of_ne hbounds.1 ?_, hbounds.2⟩
      intro he
      apply hxZ
      exact Finset.mem_image.mpr ⟨0, by simp, by simpa [hleft] using he⟩
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc m a hxm)
    have hi' := Finset.mem_range.mp hi
    have hxi' : x ∈ Ioo (a i) (a (i + 1)) := by
      refine ⟨hxi.1, lt_of_le_of_ne hxi.2 ?_⟩
      intro he
      apply hxZ
      exact Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr (by omega), he.symm⟩
    rcases preconnected_subset_or_frontier isPreconnected_Ioo ⟨x, hxi', hx⟩ with hgood | hbad
    · exact Or.inl (mem_iUnion₂.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hgood⟩, hxi'⟩)
    · obtain ⟨b, hb, hbL⟩ := hbad
      refine Or.inr (Or.inl (mem_iUnion₂.mpr ⟨b, hB hbL, ?_⟩))
      have hm := hmesh i hi'
      constructor <;> linarith [hxi'.1, hxi'.2, hb.1, hb.2]
  have hVbound : volume.real V ≤ 2 * B.card * ε := by
    have hvlen (b : ℝ) : volume.real (Icc (b - ε) (b + ε)) = 2 * ε := by
      rw [Real.volume_real_Icc_of_le (by linarith)]
      ring
    calc
      _ ≤ ∑ b ∈ B, volume.real (Icc (b - ε) (b + ε)) := measureReal_biUnion_finset_le _ _
      _ = _ := by simp only [hvlen, Finset.sum_const, nsmul_eq_mul]; ring
  have hUfin : volume U ≠ ⊤ := measure_ne_top_of_subset hU (by simp [Segment])
  have hVUfin : volume (V ∪ (Z : Set ℝ)) ≠ ⊤ :=
    measure_union_ne_top hVfin (by rw [hZfin]; exact ENNReal.zero_ne_top)
  have htotalfin := measure_union_ne_top hUfin hVUfin
  have hmeasure := measureReal_mono hsub htotalfin
  have hu := measureReal_union_le U (V ∪ (Z : Set ℝ)) (μ := volume)
  have hv := measureReal_union_le V (Z : Set ℝ) (μ := volume)
  have hZreal : volume.real (Z : Set ℝ) = 0 := by simp [measureReal_def, hZfin]
  change volume.real L ≤ volume.real U + _
  linarith

theorem ordered_cells_disjoint (a : ℕ → ℝ) (ha : StrictMono a) :
    _root_.Pairwise (fun i j => Disjoint (Ioo (a i) (a (i + 1))) (Ioo (a j) (a (j + 1)))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have := ha.monotone (Nat.succ_le_of_lt h)
    linarith [hxi.2, hxj.1]
  · have := ha.monotone (Nat.succ_le_of_lt h)
    linarith [hxj.2, hxi.1]

/-- The partition is chosen using a boundary bound, before the set `L` is known. -/
theorem exists_uniform_partition (B : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ m : ℕ, ∃ a : ℕ → ℝ, 0 < m ∧ StrictMono a ∧ a 0 = -1 ∧ a m = 1 ∧
      ∀ L : Set ℝ, L ⊆ Segment →
        (∃ T : Finset ℝ, frontier L ⊆ (T : Set ℝ) ∧ T.card ≤ B) →
        volume.real L <
          volume.real (⋃ i ∈ (Finset.range m).filter
            (fun i => Ioo (a i) (a (i + 1)) ⊆ L), Ioo (a i) (a (i + 1))) + δ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < δ / (4 * (B + 1 : ℝ)) by positivity)
  let m := n + 1
  let a := fun i : ℕ => -1 + 2 * i / (m : ℝ)
  have hm : 0 < (m : ℝ) := by dsimp [m]; positivity
  have ha : StrictMono a := by
    intro i j hij
    dsimp [a]
    have ht : (2 : ℝ) * i / m < 2 * j / m :=
      div_lt_div_of_pos_right (by exact_mod_cast Nat.mul_lt_mul_of_pos_left hij (by decide : 0 < 2)) hm
    linarith
  have hleft : a 0 = -1 := by simp [a]
  have hright : a m = 1 := by dsimp [a]; field_simp; ring
  refine ⟨m, a, by omega, ha, hleft, hright, fun L hL hB => ?_⟩
  obtain ⟨T, hT, hTB⟩ := hB
  have hmesh (i : ℕ) (_ : i < m) : a (i + 1) - a i ≤ 2 / (m : ℝ) := by
    dsimp [a]
    push_cast
    apply le_of_eq
    ring
  have hb := partition_boundary_loss m a hleft hright (2 / m) (by positivity) hmesh L hL T hT
  have hsmall : 2 * (T.card : ℝ) * (2 / (m : ℝ)) < δ := by
    have hcast : (T.card : ℝ) ≤ B := by exact_mod_cast hTB
    have hn' : 1 / (m : ℝ) < δ / (4 * (B + 1 : ℝ)) := by simpa [m] using hn
    have hmul := (lt_div_iff₀ (show 0 < 4 * (B + 1 : ℝ) by positivity)).mp hn'
    have hpos : 0 < 1 / (m : ℝ) := by positivity
    rw [show (2 : ℝ) / m = 2 * (1 / m) by ring]
    nlinarith
  linarith

end Erdos1152
