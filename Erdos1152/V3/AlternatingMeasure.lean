import Erdos1152.Intervals
import Erdos1152.LocalData

/-!
# From alternating polynomial peaks to a positive-measure forcing estimate

The input is an actual polynomial and actual ordered node-free intervals.
The result concerns all interpolants, not merely a sup-norm lower bound.
No Bernstein/kernel existence is assumed implicitly or declared as an axiom.
Build status is recorded by the canonical driver.
-/

open Polynomial MeasureTheory Set Finset
open scoped ENNReal Classical

namespace Erdos1152.V3

private def intervalUnion (a b : ℕ → ℝ) (S : Finset ℕ) : Set ℝ :=
  ⋃ i ∈ S, Ioo (a i) (b i)

private theorem intervalUnion_measurable (a b : ℕ → ℝ) (S : Finset ℕ) :
    MeasurableSet (intervalUnion a b S) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_Ioo

private theorem intervalUnion_insert (a b : ℕ → ℝ) (i : ℕ) (S : Finset ℕ) :
    intervalUnion a b (insert i S) = Ioo (a i) (b i) ∪ intervalUnion a b S := by
  ext x
  simp only [intervalUnion, Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
  aesop

private theorem volume_intervalUnion (a b : ℕ → ℝ) (S : Finset ℕ)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) :
    volume (intervalUnion a b S) = ∑ i ∈ S, volume (Ioo (a i) (b i)) := by
  revert hd
  induction S using Finset.induction_on with
  | empty => simp [intervalUnion]
  | @insert i S hi ih =>
    intro hd
    have hds : ∀ j ∈ S, ∀ k ∈ S, j ≠ k →
        Disjoint (Ioo (a j) (b j)) (Ioo (a k) (b k)) :=
      fun j hj k hk hjk => hd j (mem_insert_of_mem hj) k (mem_insert_of_mem hk) hjk
    have hdu : Disjoint (Ioo (a i) (b i)) (intervalUnion a b S) := by
      apply Set.disjoint_left.mpr
      intro x hx hxU
      obtain ⟨j, hj, hxj⟩ : ∃ j ∈ S, x ∈ Ioo (a j) (b j) := by
        simpa only [intervalUnion, Set.mem_iUnion, exists_prop] using hxU
      have hij : i ≠ j := fun h => hi (h.symm ▸ hj)
      exact Set.disjoint_left.mp
        (hd i (mem_insert_self i S) j (mem_insert_of_mem hj) hij) hx hxj
    rw [intervalUnion_insert, measure_union hdu (intervalUnion_measurable a b S),
      ih hds, Finset.sum_insert hi]

private theorem volumeReal_intervalUnion (a b : ℕ → ℝ) (S : Finset ℕ)
    (hab : ∀ i ∈ S, a i < b i)
    (hd : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))) :
    volume.real (intervalUnion a b S) = ∑ i ∈ S, (b i - a i) := by
  change (volume (intervalUnion a b S)).toReal = _
  rw [volume_intervalUnion a b S hd,
    ENNReal.toReal_sum (fun i _ => by simp)]
  apply Finset.sum_congr rfl
  intro i hi
  exact Real.volume_real_Ioo_of_le (hab i hi).le

/-- Quantitative high-set measure from the actual alternating intervals.
Written without division so that the finite combinatorics remains exact. -/
theorem alternating_high_measure
    (Y : Finset ℝ) (F p q : ℝ[X]) (K d : ℕ)
    (a b : ℕ → ℝ) (α β H ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hab : ∀ i < K, a i < b i)
    (horder : ∀ i < K, ∀ j < K, i < j → b i ≤ a j)
    (hinside : ∀ i < K, Ioo (a i) (b i) ⊆ Ioo α β)
    (hlength : ∀ i < K, ℓ ≤ b i - a i)
    (hnode : ∀ i < K, ∀ x ∈ Ioo (a i) (b i), (nodePolynomial Y).eval x ≠ 0)
    (hpeak : ∀ i < K, ∀ x ∈ Ioo (a i) (b i), H < |F.eval x|)
    (hsign : ∀ i < K, ∀ x ∈ Ioo (a i) (b i),
      0 < (-1 : ℝ) ^ i * (F.eval x / (nodePolynomial Y).eval x))
    (hfactor : p = F + nodePolynomial Y * q) (hq : q.natDegree ≤ d) :
    (K : ℝ) * ℓ ≤
      2 * volume.real ({x | H < |p.eval x|} ∩ Ioo α β) + ((d : ℝ) + 1) * ℓ := by
  classical
  let G := (range K).filter fun i => ∀ x ∈ Ioo (a i) (b i), H < |p.eval x|
  have hG (i : ℕ) (hi : i ∈ G) : i < K := mem_range.mp (mem_filter.mp hi).1
  have hd : ∀ i ∈ G, ∀ j ∈ G, i ≠ j →
      Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)) := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with hij | hji
    · have h := horder i (hG i hi) j (hG j hj) hij
      linarith [hxi.2, hxj.1]
    · have h := horder j (hG j hj) i (hG i hi) hji
      linarith [hxj.2, hxi.1]
  have hu : intervalUnion a b G ⊆ {x | H < |p.eval x|} ∩ Ioo α β := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ : ∃ i ∈ G, x ∈ Ioo (a i) (b i) := by
      simpa only [intervalUnion, Set.mem_iUnion, exists_prop] using hx
    exact ⟨(mem_filter.mp hi).2 x hxi, hinside i (hG i hi) hxi⟩
  have hm := measureReal_mono (μ := volume) hu
    (measure_ne_top_of_subset inter_subset_right (by simp))
  rw [volumeReal_intervalUnion a b G (fun i hi => hab i (hG i hi)) hd] at hm
  have hlengthSum : (G.card : ℝ) * ℓ ≤ ∑ i ∈ G, (b i - a i) := by
    simpa only [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_le_sum (s := G) (fun i hi => hlength i (hG i hi)))
  have hc := alternating_interval_bound Y F p q K d a b H
    hab horder hnode hpeak hsign hfactor hq
  change K ≤ 2 * G.card + d + 1 at hc
  have hcr : (K : ℝ) ≤ 2 * (G.card : ℝ) + (d : ℝ) + 1 := by exact_mod_cast hc
  have hcr' := mul_le_mul_of_nonneg_right hcr hℓ
  nlinarith

/-- Turn the previous estimate into the precise low-set inequality used by
LocalIntervalData, uniformly over every interpolant of the prescribed data. -/
theorem low_measure_of_alternating_polynomial
    (Y : Finset ℝ) (F : ℝ[X]) (K d : ℕ)
    (a b : ℕ → ℝ) (α β H ℓ c : ℝ) (hαβ : α < β) (hℓ : 0 ≤ ℓ)
    (hFdegree : F.natDegree ≤ Y.card + d)
    (hab : ∀ i < K, a i < b i)
    (horder : ∀ i < K, ∀ j < K, i < j → b i ≤ a j)
    (hinside : ∀ i < K, Ioo (a i) (b i) ⊆ Ioo α β)
    (hlength : ∀ i < K, ℓ ≤ b i - a i)
    (hnode : ∀ i < K, ∀ x ∈ Ioo (a i) (b i), (nodePolynomial Y).eval x ≠ 0)
    (hpeak : ∀ i < K, ∀ x ∈ Ioo (a i) (b i), H < |F.eval x|)
    (hsign : ∀ i < K, ∀ x ∈ Ioo (a i) (b i),
      0 < (-1 : ℝ) ^ i * (F.eval x / (nodePolynomial Y).eval x))
    (hbudget : 2 * c * (β - α) ≤ ((K : ℝ) - d - 1) * ℓ) :
    ∀ p : ℝ[X], p.natDegree ≤ Y.card + d →
      (∀ y ∈ Y, p.eval y = F.eval y) →
      volume.real ({x | |p.eval x| ≤ H} ∩ Ioo α β) ≤
        (1 - c) * volume.real (Ioo α β) := by
  intro p hp hvalues
  obtain ⟨q, hfactor, hq⟩ := interpolation_correction Y F p d hFdegree hp hvalues
  have hh := alternating_high_measure Y F p q K d a b α β H ℓ hℓ
    hab horder hinside hlength hnode hpeak hsign hfactor hq
  have hlow : MeasurableSet {x | |p.eval x| ≤ H} :=
    (isClosed_le p.continuous.abs continuous_const).measurableSet
  have hpartition := measureReal_inter_add_sdiff (μ := volume)
    (s := Ioo α β) hlow (by simp)
  have hdiff : Ioo α β \ {x | |p.eval x| ≤ H} =
      {x | H < |p.eval x|} ∩ Ioo α β := by
    ext x
    simp only [mem_sdiff, mem_ofPred_eq, not_le, mem_inter_iff, and_comm]
  rw [hdiff, inter_comm] at hpartition
  rw [Real.volume_real_Ioo_of_le hαβ.le] at hpartition ⊢
  nlinarith

end Erdos1152.V3
