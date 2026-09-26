import Erdos1152.Interpolation
import Erdos1152.SignCount

/-! The interval form of the alternating-sign lemma. -/

open Polynomial Finset
open Set (Ioo)
open Classical

namespace Erdos1152

private theorem correction_sign {a b q H σ : ℝ} (ha : a ≠ 0)
    (hb : H < |b|) (hp : |b + a * q| ≤ H)
    (hσ : σ ^ 2 = 1) (hsgn : 0 < σ * (b / a)) : σ * q < 0 := by
  have hab := abs_le.mp hp
  have hprod : b * (a * q) < 0 := by
    rcases le_or_gt 0 b with h | h
    · rw [abs_of_nonneg h] at hb
      have hb0 : 0 < b := by have := abs_nonneg (b + a * q); linarith
      exact mul_neg_of_pos_of_neg hb0 (by linarith)
    · rw [abs_of_neg h] at hb
      exact mul_neg_of_neg_of_pos h (by linarith)
  have he : (σ * (b / a)) * (σ * q) * a ^ 2 = b * (a * q) := by
    field_simp
    rw [hσ]
    ring
  have : (σ * (b / a)) * a ^ 2 > 0 := mul_pos hsgn (sq_pos_of_ne_zero ha)
  nlinarith

/-- The sign-change bound in Lemma 3: at least `(K - d - 1) / 2` intervals remain uniformly above `H`.
The conclusion is written without division or truncated natural subtraction. -/
theorem alternating_interval_bound (Y : Finset ℝ) (b p q : ℝ[X])
    (K d : ℕ) (a c : ℕ → ℝ) (H : ℝ)
    (hac : ∀ i < K, a i < c i)
    (horder : ∀ i < K, ∀ j < K, i < j → c i ≤ a j)
    (hnode : ∀ i < K, ∀ x ∈ Ioo (a i) (c i), (nodePolynomial Y).eval x ≠ 0)
    (hb : ∀ i < K, ∀ x ∈ Ioo (a i) (c i), H < |b.eval x|)
    (hs : ∀ i < K, ∀ x ∈ Ioo (a i) (c i),
      0 < (-1 : ℝ) ^ i * (b.eval x / (nodePolynomial Y).eval x))
    (hp : p = b + nodePolynomial Y * q) (hq : q.natDegree ≤ d) :
    K ≤ 2 * ((range K).filter fun i =>
      ∀ x ∈ Ioo (a i) (c i), H < |p.eval x|).card + d + 1 := by
  classical
  let L := (range K).filter fun i => ∃ x ∈ Ioo (a i) (c i), |p.eval x| ≤ H
  have hsample (i : ℕ) : ∃ x : ℝ, i < K →
      x ∈ Ioo (a i) (c i) ∧ (i ∈ L → |p.eval x| ≤ H) := by
    by_cases hi : i < K
    · by_cases hl : i ∈ L
      · obtain ⟨x, hx, hpx⟩ := (mem_filter.mp hl).2
        exact ⟨x, fun _ => ⟨hx, fun _ => hpx⟩⟩
      · exact ⟨(a i + c i) / 2, fun _ =>
          ⟨by constructor <;> linarith [hac i hi], fun h => (hl h).elim⟩⟩
    · exact ⟨0, fun h => (hi h).elim⟩
  choose x hx using hsample
  have hxmono : StrictMonoOn x (Set.Iio K) := by
    intro i hi j hj hij
    exact ((hx i hi).1.2.trans_le (horder i hi j hj hij)).trans (hx j hj).1.1
  have hc := alternating_sample_bound (-q) x K hxmono L (filter_subset _ _) (by
    intro i hi
    have hiK := mem_range.mp (mem_filter.mp hi).1
    have hsign := correction_sign (hnode i hiK _ (hx i hiK).1)
      (hb i hiK _ (hx i hiK).1) (by
        simpa [hp] using (hx i hiK).2 hi)
      (show ((-1 : ℝ) ^ i) ^ 2 = 1 by
        rw [← pow_mul, mul_comm i 2, pow_mul]; simp)
      (hs i hiK _ (hx i hiK).1)
    simpa using neg_pos.mpr hsign)
  have hcard := card_filter_add_card_filter_not (s := range K)
    (fun i => ∃ x ∈ Ioo (a i) (c i), |p.eval x| ≤ H)
  simp only [not_exists, not_and, not_le, card_range] at hcard
  simp only [natDegree_neg] at hc
  change L.card + _ = K at hcard
  omega

end Erdos1152
