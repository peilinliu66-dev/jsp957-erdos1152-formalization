import Erdos1152.RemezAmplification
import Erdos1152.LocalRegions
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! From cardinal-polynomial growth to local interval data at density points. -/

open Polynomial MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace Erdos1152

/-- The real nodes of row `n` whose values have not yet been assigned. -/
noncomputable def unassignedNodes (X : NodeArray) (S : Finset Segment) (n : ℕ) : Finset ℝ :=
  ((Finset.univ.image (X.node n)) \ S).image Subtype.val

theorem mem_unassignedNodes (X : NodeArray) (S : Finset Segment) (n : ℕ) (y : ℝ) :
    y ∈ unassignedNodes X S n ↔ ∃ i, X.node n i ∉ S ∧ (X.node n i : ℝ) = y := by
  classical
  simp only [unassignedNodes, Finset.mem_image, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, ⟨⟨i, rfl⟩, hi⟩, he⟩
    exact ⟨i, hi, he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨X.node n i, ⟨⟨i, rfl⟩, hi⟩, he⟩

theorem unassignedNodes_card (X : NodeArray) (S : Finset Segment) (n : ℕ) :
    n + 1 ≤ (unassignedNodes X S n).card + S.card := by
  classical
  have h := Finset.card_le_card_sdiff_add_card
    (s := Finset.univ.image (X.node n)) (t := S)
  simpa [unassignedNodes, Finset.card_image_of_injective, X.injective n,
    Subtype.val_injective] using h

/-- The exponential growth estimate of Section 6.1, along a row subsequence.
The region `A` is fixed before the finite assigned-node set is chosen. -/
def CardinalGrowthOn (X : NodeArray) (A : Set ℝ) : Prop :=
  ∀ S : Finset Segment, ∃ rows : ℕ → ℕ, Tendsto rows atTop atTop ∧
    ∃ z : ℕ → ℝ, (∀ n, z n ∈ unassignedNodes X S (rows n)) ∧
    ∃ η : ℝ, 0 < η ∧ ∃ E : ℕ → Set ℝ,
      (∀ n, MeasurableSet (E n) ∧ E n ⊆ A) ∧
      Tendsto (fun n => volume.real (A \ E n)) atTop (𝓝 0) ∧
      ∀ᶠ n : ℕ in atTop, ∀ x ∈ E n,
        Real.exp (η * (rows n + 1)) ≤
          |(cardinalPolynomial (unassignedNodes X S (rows n)) (z n)).eval x|

/-- A countable family of growth regions covering the above-minimum region almost everywhere. -/
def CardinalGrowthCover (X : NodeArray) (A : Set ℝ) : Prop :=
  ∃ B : ℕ → Set ℝ, (∀ j, MeasurableSet (B j) ∧ B j ⊆ Segment ∧ CardinalGrowthOn X (B j)) ∧
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1), x ∈ A → ∃ j, x ∈ B j

private theorem sublinear_add_const (r : ℕ → ℕ) (C : ℕ)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ((r n + C : ℕ) : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  simpa [add_div, div_eq_mul_inv, add_mul] using
    hr.add ((tendsto_inv_atTop_zero.comp ht).const_mul (C : ℝ))

/-- Once a region occupies at least three quarters of an interval, the Remez
deduction gives local data forcing large values on half of that interval. -/
theorem localIntervalData_of_cardinalGrowth (X : NodeArray) (r : ℕ → ℕ)
    (hR : RemezChebyshevInequality)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (A : Set ℝ) (hAsub : A ⊆ Segment) (hg : CardinalGrowthOn X A)
    (H a b : ℝ) (hH : 0 < H) (hab : a < b)
    (hfill : volume.real (Ioo a b \ A) ≤ volume.real (Ioo a b) / 4) :
    LocalIntervalData X r H (1 / 2) a b := by
  classical
  intro S N
  obtain ⟨rows, hrows, z, hz, η, hη, E, hE, hbad, hgrowth⟩ := hg S
  have hzseg (n : ℕ) : z n ∈ Segment := by
    obtain ⟨i, _, he⟩ := (mem_unassignedNodes X S (rows n) (z n)).mp (hz n)
    exact he ▸ (X.node (rows n) i).property
  have hlen : 0 < volume.real (Ioo a b) := by
    rw [Real.volume_real_Ioo_of_le hab.le]
    exact sub_pos.mpr hab
  have he := eventually_cardinal_amplification_of_measure_convergence hR rows hrows
    (fun n => unassignedNodes X S (rows n)) z (fun n => r n + S.card) A E hz hzseg
    hAsub (fun n => (hE n).1) (fun n => (hE n).2) H η hH hη
    (sublinear_add_const r S.card hr) hbad hgrowth (volume.real (Ioo a b) / 4) (by positivity)
  obtain ⟨j, hj, hjN⟩ := (he.and (hrows.eventually (eventually_ge_atTop N))).exists
  let v : Segment → ℝ := fun x => if (x : ℝ) = z j then 1 else 0
  refine ⟨rows j, hjN, v, ?_, ?_⟩
  · intro i hi
    dsimp [v]
    split_ifs <;> norm_num
  · intro p hp hv
    have hdeg : p.natDegree ≤ (unassignedNodes X S (rows j)).card + (r (rows j) + S.card) := by
      have := unassignedNodes_card X S (rows j)
      omega
    have hpz : p.eval (z j) = 1 := by
      obtain ⟨i, hi, hiZ⟩ := (mem_unassignedNodes X S (rows j) (z j)).mp (hz j)
      simpa [v, hiZ] using hv i hi
    have hpzero : ∀ y ∈ (unassignedNodes X S (rows j)).erase (z j), p.eval y = 0 := by
      intro y hy
      obtain ⟨i, hi, hiy⟩ := (mem_unassignedNodes X S (rows j) y).mp (Finset.mem_of_mem_erase hy)
      simpa [v, hiy, Finset.ne_of_mem_erase hy] using hv i hi
    have hlow := hj p hdeg hpz hpzero
    have hcover : {x | |p.eval x| ≤ H} ∩ Ioo a b ⊆
        {x ∈ A | |p.eval x| ≤ H} ∪ (Ioo a b \ A) := by
      intro x hx
      by_cases hxa : x ∈ A
      · exact Or.inl ⟨hxa, hx.1⟩
      · exact Or.inr ⟨hx.2, hxa⟩
    have hf1 : volume {x ∈ A | |p.eval x| ≤ H} ≠ ⊤ :=
      measure_ne_top_of_subset (fun _ hx => hAsub hx.1) (by simp [Segment])
    have hf2 : volume (Ioo a b \ A) ≠ ⊤ := measure_ne_top_of_subset sdiff_subset (by simp)
    have hb := (measureReal_mono hcover (measure_union_lt_top hf1.lt_top hf2.lt_top).ne).trans
      (measureReal_union_le _ _)
    linarith

/-- Almost every point of a measurable set admits arbitrarily small intervals
whose complement in the set has relative measure at most one quarter. -/
theorem ae_small_interval_complement (A : Set ℝ) (hA : MeasurableSet A) :
    ∀ᵐ x ∂volume.restrict A, ∀ ε > (0 : ℝ),
      ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧
        volume.real (Ioo (x - h) (x + h) \ A) ≤
          volume.real (Ioo (x - h) (x + h)) / 4 := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_measure_inter_div volume A 1] with x hx
  have hden := hx (fun _ : ℝ => x) id tendsto_id
    (by
      filter_upwards [self_mem_nhdsWithin] with h hh
      exact mem_closedBall_self (by simpa using le_of_lt hh))
  have hr := (ENNReal.continuousAt_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hden
  simp only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_one] at hr
  intro ε hε
  have hgt := hr.eventually (lt_mem_nhds (by norm_num : (3 / 4 : ℝ) < 1))
  have hlt : ∀ᶠ h : ℝ in 𝓝[>] 0, h < ε :=
    eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hε)
  have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  obtain ⟨h, hratio, hh, hhe⟩ := (hgt.and (hpos.and hlt)).exists
  have hh' : 0 < h := hh
  refine ⟨h, hh', hhe.le, ?_⟩
  have hball : (volume (closedBall x h)).toReal = 2 * h := by
    rw [Real.volume_closedBall, ENNReal.toReal_ofReal (by positivity)]
  have hae : (A ∩ Ioo (x - h) (x + h) : Set ℝ) =ᵐ[volume]
      (A ∩ closedBall x h : Set ℝ) := by
    filter_upwards [Ioo_ae_eq_Icc (μ := volume) (a := x - h) (b := x + h)] with y hy
    rw [Real.closedBall_eq_Icc]
    apply propext
    constructor
    · rintro ⟨hyA, hyI⟩
      exact ⟨hyA, Eq.mp hy hyI⟩
    · rintro ⟨hyA, hyI⟩
      exact ⟨hyA, Eq.mpr hy hyI⟩
  have hinter : volume.real (A ∩ Ioo (x - h) (x + h)) =
      (volume (A ∩ closedBall x h)).toReal := congrArg ENNReal.toReal (measure_congr hae)
  simp only [id_eq] at hratio
  rw [hball, ← hinter] at hratio
  have hlower := (lt_div_iff₀ (by positivity : 0 < 2 * h)).mp hratio
  have hsum := measureReal_inter_add_sdiff (μ := volume)
    (s := Ioo (x - h) (x + h)) hA (by simp)
  rw [inter_comm, Real.volume_real_Ioo_of_le (by linarith)] at hsum
  rw [Real.volume_real_Ioo_of_le (by linarith)]
  linarith

/-- Density points turn the Remez estimate into the local interval conclusion.
The interval is chosen before `S` and `N`, as required by `LocalIntervalData`. -/
theorem localAmplificationAbove_of_cardinalGrowthCover (X : NodeArray) (r : ℕ → ℕ)
    (hR : RemezChebyshevInequality)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (A : Set ℝ) (hg : CardinalGrowthCover X A) : LocalAmplificationAbove X r A := by
  obtain ⟨B, hB, hcover⟩ := hg
  have hd (j : ℕ) : ∀ᵐ x ∂volume, x ∈ B j → ∀ ε > (0 : ℝ),
      ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧
        volume.real (Ioo (x - h) (x + h) \ B j) ≤
          volume.real (Ioo (x - h) (x + h)) / 4 :=
    ae_imp_of_ae_restrict (ae_small_interval_complement (B j) (hB j).1)
  have hdall := ae_all_iff.mpr hd
  intro H hH
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  filter_upwards [hcover, ae_restrict_of_ae hdall] with x hx hdx
  intro hxa ε hε
  obtain ⟨j, hxj⟩ := hx hxa
  obtain ⟨h, hh, hhe, hfill⟩ := hdx j hxj ε hε
  refine ⟨h, hh, hhe, ?_⟩
  exact localIntervalData_of_cardinalGrowth X r hR hr (B j) (hB j).2.1 (hB j).2.2
    H (x - h) (x + h) (by linarith) (by linarith) hfill

end Erdos1152
