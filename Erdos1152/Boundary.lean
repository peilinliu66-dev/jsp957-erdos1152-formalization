import Erdos1152.FiniteObstruction

/-! Degree bounds for the boundaries of common low sets. -/

open Polynomial Set

namespace Erdos1152

noncomputable def lowBoundaryCover (p : ℝ[X]) (H : ℝ) : Finset ℝ :=
  if p.natDegree = 0 then ∅
  else (p - C H).roots.toFinset ∪ (p - C (-H)).roots.toFinset

theorem lowBoundaryCover_card (p : ℝ[X]) (H : ℝ) :
    (lowBoundaryCover p H).card ≤ 2 * p.natDegree := by
  classical
  unfold lowBoundaryCover
  split_ifs with hp
  · simp
  · calc
      _ ≤ (p - C H).roots.toFinset.card + (p - C (-H)).roots.toFinset.card :=
        Finset.card_union_le _ _
      _ ≤ (p - C H).natDegree + (p - C (-H)).natDegree :=
        add_le_add
          ((p - C H).roots.toFinset_card_le.trans (p - C H).card_roots')
          ((p - C (-H)).roots.toFinset_card_le.trans (p - C (-H)).card_roots')
      _ = _ := by simp; omega

theorem low_frontier_subset (p : ℝ[X]) (H : ℝ) :
    frontier {x : ℝ | |p.eval x| ≤ H} ⊆ (lowBoundaryCover p H : Set ℝ) := by
  classical
  by_cases hp : p.natDegree = 0
  · have he := eq_C_of_natDegree_eq_zero hp
    rw [he]
    by_cases h : |p.coeff 0| ≤ H <;> simp [h]
  · intro x hx
    have hlevel : |p.eval x| = H := by
      have := p.continuous.abs.frontier_preimage_subset (Iic H) hx
      simpa only [frontier_Iic, mem_preimage, mem_singleton_iff] using this
    have hpC (a : ℝ) : p - C a ≠ 0 := by
      intro h
      have := sub_eq_zero.mp h
      apply hp
      rw [this, natDegree_C]
    simp only [lowBoundaryCover, if_neg hp, Finset.coe_union, mem_union,
      Finset.mem_coe, Multiset.mem_toFinset, mem_roots (hpC H), mem_roots (hpC (-H)),
      IsRoot, eval_sub, eval_C, sub_eq_zero]
    by_cases h : 0 ≤ p.eval x
    · left
      simpa [abs_of_nonneg h] using hlevel
    · right
      rw [abs_of_neg (lt_of_not_ge h)] at hlevel
      linarith

/-- Every common low set has a boundary cover depending only on the row degrees. -/
theorem commonLowSet_boundary_cover (s : Finset ℕ) (p : ℕ → ℝ[X]) (H : ℝ) :
    ∃ B : Finset ℝ, frontier (commonLowSet s p H) ⊆ (B : Set ℝ) ∧
      B.card ≤ 2 + 2 * ∑ n ∈ s, (p n).natDegree := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨{-1, 1}, ?_, ?_⟩
    · simp only [commonLowSet, Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
        ofPred_true, inter_univ]
      rw [frontier_Icc]
      · simp
      · norm_num
    · norm_num
  | @insert n s hn ih =>
    obtain ⟨B, hB, hc⟩ := ih
    refine ⟨B ∪ lowBoundaryCover (p n) H, ?_, ?_⟩
    · have he : commonLowSet (insert n s) p H =
          commonLowSet s p H ∩ {x | |(p n).eval x| ≤ H} := by
        ext x
        simp [commonLowSet]
        tauto
      rw [he]
      intro x hx
      rcases frontier_inter_subset _ _ hx with hx | hx
      · exact Finset.mem_union.mpr (Or.inl (hB hx.1))
      · exact Finset.mem_union.mpr (Or.inr (low_frontier_subset (p n) H hx.2))
    · have hb := lowBoundaryCover_card (p n) H
      have hu := Finset.card_union_le B (lowBoundaryCover (p n) H)
      rw [Finset.sum_insert hn]
      omega

end Erdos1152
