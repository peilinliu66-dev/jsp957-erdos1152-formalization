import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-! Alternating samples of a real polynomial and the number of low intervals. -/

open Polynomial Finset
open Set (Ioo)

namespace Erdos1152

/-- Adjacent retained positions account for all but the deleted sign changes. -/
theorem retained_positions (K : ℕ) (S : Finset ℕ) (hS : S ⊆ range K) :
    2 * S.card ≤ K + 1 + (S.filter fun i => i + 1 ∈ S).card := by
  let T := S.image Nat.succ
  have hT : T.card = S.card := card_image_of_injective _ Nat.succ_injective
  have hu : S ∪ T ⊆ range (K + 1) := by
    intro i hi
    rcases mem_union.mp hi with hi | hi
    · have := mem_range.mp (hS hi)
      simp only [mem_range]
      omega
    · obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
      have := mem_range.mp (hS hj)
      simp only [mem_range]
      omega
  have hi : S ∩ T = (S.filter fun i => i + 1 ∈ S).image Nat.succ := by
    ext i
    simp only [mem_inter, T, mem_image, mem_filter]
    constructor
    · rintro ⟨hi, j, hj, rfl⟩
      exact ⟨j, ⟨hj, hi⟩, rfl⟩
    · rintro ⟨j, ⟨hj, hj'⟩, rfl⟩
      exact ⟨hj', j, hj, rfl⟩
  have hc := card_union_add_card_inter S T
  have hb := card_le_card hu
  rw [hi, card_image_of_injective _ Nat.succ_injective, hT] at hc
  simp only [card_range] at hb
  omega

theorem exists_root_between (q : ℝ[X]) {a b : ℝ} (hab : a < b)
    (h : q.eval a * q.eval b < 0) :
    ∃ z ∈ Ioo a b, q.eval z = 0 := by
  rcases mul_neg_iff.mp h with h | h
  · exact intermediate_value_Ioo' hab.le q.continuous.continuousOn ⟨h.2, h.1⟩
  · exact intermediate_value_Ioo hab.le q.continuous.continuousOn h

/-- Opposite signs on disjoint ordered gaps give distinct roots. -/
theorem sign_changes_le_degree (q : ℝ[X]) (x : ℕ → ℝ)
    (K : ℕ) (hx : StrictMonoOn x (Set.Iio K)) (S : Finset ℕ)
    (hS : ∀ i ∈ S, i + 1 < K)
    (hs : ∀ i ∈ S, q.eval (x i) * q.eval (x (i + 1)) < 0) :
    S.card ≤ q.natDegree := by
  classical
  by_cases hnonempty : S.Nonempty
  · have hq : q ≠ 0 := by
      obtain ⟨i, hi⟩ := hnonempty
      intro hq
      simpa [hq] using hs i hi
    have hmem (i : S) : i.val < K := by have := hS i.val i.property; omega
    choose z hz hzq using fun i : S =>
      exists_root_between q
        (hx (hmem i) (hS i.val i.property) (Nat.lt_succ_self i.val))
        (hs i.val i.property)
    have hz_inj : Function.Injective z := by
      intro i j hij
      apply Subtype.ext
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := (hz i).2.trans_le
          (hx.monotoneOn (hS i.val i.property) (hmem j) (Nat.succ_le_of_lt h))
        have := this.trans (hz j).1
        exact (lt_irrefl _ (hij ▸ this))
      · have := (hz j).2.trans_le
          (hx.monotoneOn (hS j.val j.property) (hmem i) (Nat.succ_le_of_lt h))
        have := this.trans (hz i).1
        exact (lt_irrefl _ (hij ▸ this))
    have hroot : ∀ i : S, z i ∈ q.roots := by
      intro i
      exact (mem_roots hq).2 (hzq i)
    have hc : Fintype.card S ≤ q.roots.toFinset.card := by
      simpa using Fintype.card_le_of_injective
        (fun i => (⟨z i, by simpa using hroot i⟩ : q.roots.toFinset))
        (fun i j h => hz_inj (congrArg Subtype.val h))
    simpa using hc.trans (q.roots.toFinset_card_le.trans q.card_roots')
  · simp [not_nonempty_iff_eq_empty.mp hnonempty]

/-- The low-sample estimate in Lemma 3, with all quantities integral. -/
theorem alternating_sample_bound (q : ℝ[X]) (x : ℕ → ℝ)
    (K : ℕ) (hx : StrictMonoOn x (Set.Iio K))
    (S : Finset ℕ) (hS : S ⊆ range K)
    (hs : ∀ i ∈ S, 0 < (-1 : ℝ) ^ i * q.eval (x i)) :
    2 * S.card ≤ K + q.natDegree + 1 := by
  have hr := retained_positions K S hS
  have hc := sign_changes_le_degree q x K hx (S.filter fun i => i + 1 ∈ S)
    (fun i hi => mem_range.mp (hS (mem_filter.mp hi).2)) (by
    intro i hi
    obtain ⟨hi, hi'⟩ := mem_filter.mp hi
    have h := mul_pos (hs i hi) (hs (i + 1) hi')
    have he : (-1 : ℝ) ^ i * (-1 : ℝ) ^ (i + 1) = -1 := by
      rw [pow_succ]
      have : ((-1 : ℝ) ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm i 2, pow_mul]; simp
      nlinarith
    have : ((-1 : ℝ) ^ i * q.eval (x i)) *
        ((-1 : ℝ) ^ (i + 1) * q.eval (x (i + 1))) =
        -(q.eval (x i) * q.eval (x (i + 1))) := by
      calc
        _ = ((-1 : ℝ) ^ i * (-1 : ℝ) ^ (i + 1)) *
          (q.eval (x i) * q.eval (x (i + 1))) := by ring
        _ = _ := by rw [he]; ring
    linarith)
  omega

end Erdos1152
