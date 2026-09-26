import Erdos1152.LocalData

/-! Combining the above-minimum and minimum-potential regions. -/

open MeasureTheory Set

namespace Erdos1152

/-- The local conclusion restricted to a region of the interval. -/
def LocalAmplificationOn (X : NodeArray) (r : ℕ → ℕ) (A : Set ℝ) : Prop :=
  ∀ H : ℝ, 1 < H → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∀ᵐ x ∂volume.restrict (Ioo (-1) 1), x ∈ A → ∀ ε > (0 : ℝ),
      ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧ LocalIntervalData X r H c (x - h) (x + h)

abbrev LocalAmplificationAbove (X : NodeArray) (r : ℕ → ℕ) (A : Set ℝ) :=
  LocalAmplificationOn X r A

abbrev LocalAmplificationMinimal (X : NodeArray) (r : ℕ → ℕ) (A : Set ℝ) :=
  LocalAmplificationOn X r Aᶜ

theorem LocalIntervalData.mono_fraction {X : NodeArray} {r : ℕ → ℕ} {H c c' a b : ℝ}
    (h : LocalIntervalData X r H c a b) (hc : c' ≤ c) :
    LocalIntervalData X r H c' a b := by
  intro S N
  obtain ⟨n, hn, v, hv, hp⟩ := h S N
  refine ⟨n, hn, v, hv, fun p hd he => (hp p hd he).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (measureReal_nonneg)

/-- One uniform fraction works on both regions, by taking their minimum. -/
theorem localAmplification_of_above_minimal (X : NodeArray) (r : ℕ → ℕ) (A : Set ℝ)
    (ha : LocalAmplificationAbove X r A) (hm : LocalAmplificationMinimal X r A) :
    LocalAmplification X r := by
  intro H hH
  obtain ⟨ca, hca, hca1, hla⟩ := ha H hH
  obtain ⟨cm, hcm, hcm1, hlm⟩ := hm H hH
  refine ⟨min ca cm, lt_min hca hcm, (min_le_left _ _).trans hca1, ?_⟩
  filter_upwards [hla, hlm] with x hxa hxm
  intro ε hε
  by_cases hx : x ∈ A
  · obtain ⟨h, hh, hhe, hd⟩ := hxa hx ε hε
    exact ⟨h, hh, hhe, hd.mono_fraction (min_le_left _ _)⟩
  · obtain ⟨h, hh, hhe, hd⟩ := hxm hx ε hε
    exact ⟨h, hh, hhe, hd.mono_fraction (min_le_right _ _)⟩

end Erdos1152
