import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Aesop

/-! New proof candidate: measure-to-sampling for the coarse Remez estimate.
No compiler was available when this source was written. -/
open MeasureTheory Set Finset
open scoped Classical
namespace Erdos1152

private def intervalUnion (s : Finset ℝ) (δ : ℝ) : Set ℝ :=
  ⋃ y ∈ s, Ioo (y - δ) (y + δ)

private theorem intervalUnion_insert (s : Finset ℝ) (a δ : ℝ) :
    intervalUnion (insert a s) δ = Ioo (a - δ) (a + δ) ∪ intervalUnion s δ := by
  ext x
  simp only [intervalUnion, mem_iUnion, mem_union]
  aesop

private theorem intervalUnion_measure (s : Finset ℝ) (δ : ℝ) (hδ : 0 ≤ δ) :
    volume (intervalUnion s δ) ≠ ⊤ ∧
      volume.real (intervalUnion s δ) ≤ 2 * δ * s.card := by
  induction s using Finset.induction_on with
  | empty => simp [intervalUnion]
  | @insert a s ha ih =>
      rw [intervalUnion_insert]
      refine ⟨(measure_union_lt_top (by simp) ih.1.lt_top).ne, ?_⟩
      have hlen : volume.real (Ioo (a - δ) (a + δ)) = 2 * δ := by
        rw [Real.volume_real_Ioo_of_le (by linarith)]
        ring
      calc
        volume.real (Ioo (a - δ) (a + δ) ∪ intervalUnion s δ)
            ≤ volume.real (Ioo (a - δ) (a + δ)) +
                volume.real (intervalUnion s δ) := measureReal_union_le _ _
        _ ≤ 2 * δ * (insert a s).card := by
          rw [hlen, Finset.card_insert_of_notMem ha]
          push_cast
          nlinarith [ih.2]

/-- The argument does not assume that the measurable set has an interior. -/
theorem exists_separated_samples (E : Set ℝ) (δ : ℝ) (hδ : 0 < δ) (n : ℕ) :
    2 * δ * n < volume.real E →
      ∃ s : Finset ℝ, s.card = n ∧ (↑s : Set ℝ) ⊆ E ∧
        (↑s : Set ℝ).Pairwise (fun x y => δ ≤ |x - y|) := by
  classical
  induction n with
  | zero =>
      intro _
      exact ⟨∅, by simp, by simp, by simp⟩
  | succ n ih =>
      intro hbudget
      have hbudget' : 2 * δ * n < volume.real E := by
        push_cast at hbudget
        nlinarith
      obtain ⟨s, hs, hsE, hsep⟩ := ih hbudget'
      have hU := intervalUnion_measure s δ hδ.le
      have hex : ∃ x ∈ E, x ∉ intervalUnion s δ := by
        by_contra! hcover
        have hm := measureReal_mono hcover hU.1
        have hb := hU.2
        rw [hs] at hb
        linarith
      obtain ⟨x, hxE, hxU⟩ := hex
      have hdist (y : ℝ) (hy : y ∈ s) : δ ≤ |x - y| := by
        by_contra h
        have habs := abs_lt.mp (lt_of_not_ge h)
        apply hxU
        simp only [intervalUnion, mem_iUnion]
        exact ⟨y, hy, by constructor <;> linarith⟩
      have hxs : x ∉ s := by
        intro hx
        have h := hdist x hx
        simp only [sub_self, abs_zero] at h
        linarith
      refine ⟨insert x s, by simp [hxs, hs], ?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hxE
        · exact hsE hy
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl | haS
        · rcases Finset.mem_insert.mp hb with rfl | hbS
          · exact (hab rfl).elim
          · exact hdist b hbS
        · rcases Finset.mem_insert.mp hb with rfl | hbS
          · simpa only [abs_sub_comm] using hdist a haS
          · exact hsep haS hbS hab

/-- Consecutive gaps telescope after subtracting the linear function `δ*i`. -/
theorem separated_mono_gap {d : ℕ} (x : Fin (d + 1) → ℝ) (δ : ℝ)
    (hmono : StrictMono x) (hsep : ∀ i j, i ≠ j → δ ≤ |x i - x j|) :
    ∀ i j, δ * |(i.val : ℝ) - j.val| ≤ |x i - x j| := by
  have hm : Monotone (fun i => x i - δ * i.val) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hi : i.castSucc < i.succ := by simp
    have hs := hsep i.succ i.castSucc (ne_of_gt hi)
    rw [abs_of_pos (sub_pos.mpr (hmono hi))] at hs
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    linarith
  intro i j
  rcases le_total i j with hij | hji
  · have hx := hmono.monotone hij
    have hv : (i.val : ℝ) ≤ j.val := by exact_mod_cast hij
    have hh := hm hij
    rw [abs_of_nonpos (sub_nonpos.mpr hx), abs_of_nonpos (sub_nonpos.mpr hv)]
    dsimp at hh
    nlinarith
  · have hx := hmono.monotone hji
    have hv : (j.val : ℝ) ≤ i.val := by exact_mod_cast hji
    have hh := hm hji
    rw [abs_of_nonneg (sub_nonneg.mpr hx), abs_of_nonneg (sub_nonneg.mpr hv)]
    dsimp at hh
    nlinarith

/-- This deliberately uses the nonoptimal radius `mu / (4*(d+1))`. -/
theorem exists_sorted_samples (E : Set ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hmeasure : volume.real E = μ) (d : ℕ) :
    ∃ x : Fin (d + 1) → ℝ, StrictMono x ∧ (∀ i, x i ∈ E) ∧
      ∀ i j, (μ / (4 * (d + 1 : ℝ))) * |(i.val : ℝ) - j.val| ≤ |x i - x j| := by
  classical
  let δ : ℝ := μ / (4 * (d + 1 : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hcancel : 2 * δ * (d + 1 : ℕ) = μ / 2 := by
    dsimp [δ]
    push_cast
    field_simp
    ring
  have hbudget : 2 * δ * (d + 1 : ℕ) < volume.real E := by
    rw [hcancel, hmeasure]
    linarith
  obtain ⟨s, hs, hsE, hsep⟩ := exists_separated_samples E δ hδ (d + 1) hbudget
  let x : Fin (d + 1) → ℝ := s.orderEmbOfFin hs
  have hxmem (i : Fin (d + 1)) : x i ∈ s := s.orderEmbOfFin_mem hs i
  have hxmono : StrictMono x := (s.orderEmbOfFin hs).strictMono
  refine ⟨x, hxmono, fun i => hsE (hxmem i), ?_⟩
  exact separated_mono_gap x δ hxmono
    (fun i j hij => hsep (hxmem i) (hxmem j) (hxmono.injective.ne hij))
end Erdos1152
