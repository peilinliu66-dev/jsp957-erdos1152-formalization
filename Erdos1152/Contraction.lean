import Erdos1152.Partition

/-! The measure contraction supplied by one batch of rows. -/

open Set MeasureTheory
open scoped ENNReal
open Classical

namespace Erdos1152

theorem partition_contraction (m : ℕ) (a : ℕ → ℝ) (ha : StrictMono a)
    (L K : Set ℝ) (hL : L ⊆ Segment) (hK : K ⊆ L) (hKm : MeasurableSet K)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hcell : ∀ i < m, volume.real (K ∩ Ioo (a i) (a (i + 1))) ≤
      (1 - θ) * volume.real (Ioo (a i) (a (i + 1))))
    (hcover : 3 / 4 * volume.real L ≤
      volume.real (⋃ i ∈ (Finset.range m).filter
        (fun i => Ioo (a i) (a (i + 1)) ⊆ L), Ioo (a i) (a (i + 1)))) :
    volume.real K ≤ (1 - 3 * θ / 4) * volume.real L := by
  let G := (Finset.range m).filter fun i => Ioo (a i) (a (i + 1)) ⊆ L
  let J := fun i => Ioo (a i) (a (i + 1))
  let E := ⋃ i ∈ G, J i \ K
  have hJfin (i : ℕ) : volume (J i) ≠ ⊤ := by simp [J]
  have hdis : PairwiseDisjoint (G : Set ℕ) J := by
    intro i _ j _ hij
    exact ordered_cells_disjoint a ha hij
  have hdisE : PairwiseDisjoint (G : Set ℕ) (fun i => J i \ K) := by
    intro i hi j hj hij
    exact (hdis hi hj hij).mono sdiff_subset sdiff_subset
  have hEsum : volume.real E = ∑ i ∈ G, volume.real (J i \ K) := by
    exact measureReal_biUnion_finset hdisE (fun i _ => measurableSet_Ioo.diff hKm)
      (fun i _ => measure_ne_top_of_subset sdiff_subset (hJfin i))
  have hJsum : volume.real (⋃ i ∈ G, J i) = ∑ i ∈ G, volume.real (J i) :=
    measureReal_biUnion_finset hdis (fun _ _ => measurableSet_Ioo) (fun i _ => hJfin i)
  have hremove : θ * volume.real (⋃ i ∈ G, J i) ≤ volume.real E := by
    rw [hEsum, hJsum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hci := hcell i (Finset.mem_range.mp (Finset.mem_filter.mp hi).1)
    have heq := measureReal_inter_add_sdiff (μ := volume) (s := J i) hKm (hJfin i)
    rw [inter_comm] at heq
    dsimp [J] at heq ⊢
    linarith
  have hLfin : volume L ≠ ⊤ := measure_ne_top_of_subset hL (by simp [Segment])
  have hsub : E ⊆ L \ K := by
    intro x hx
    obtain ⟨i, hi, hxJ, hxK⟩ := mem_iUnion₂.mp hx
    exact ⟨(Finset.mem_filter.mp hi).2 hxJ, hxK⟩
  have hupper := measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hLfin)
  rw [measureReal_sdiff hK hKm hLfin] at hupper
  have hcov : 3 / 4 * volume.real L ≤ volume.real (⋃ i ∈ G, J i) := hcover
  have := mul_le_mul_of_nonneg_left hcov hθ
  nlinarith

end Erdos1152
