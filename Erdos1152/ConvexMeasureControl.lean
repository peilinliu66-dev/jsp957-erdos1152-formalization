import Mathlib

/-! Quantitative real-variable step for the paper's minimum-potential argument.
A convex function which is close to a continuous target off a small set is
uniformly close in an interior window. This is not the weighted-peak theorem.
New proof candidate, NOT compiler checked in the current environment. -/

open MeasureTheory Set

namespace Erdos1152

private theorem exists_good_interval_point (B : Set ℝ) (hB : volume B ≠ ⊤)
    (a b κ : ℝ) (hab : a < b) (hlen : b - a = κ)
    (hbad : volume.real B < κ) : ∃ y ∈ Ioo a b, y ∉ B := by
  by_contra! h
  have hm := measureReal_mono h hB
  rw [Real.volume_real_Ioo_of_le hab.le, hlen] at hm
  linarith

/-- Three good samples force a quantitative bound for a convex function.
The near-left sample is at distance at most twice its distance to the far-left
sample. This prevents the lower estimate from degenerating. -/
theorem convex_three_sample_control (D : Set ℝ) (f : ℝ → ℝ)
    (hf : ConvexOn ℝ D f) (l m x r G C : ℝ)
    (hlD : l ∈ D) (hmD : m ∈ D) (hxD : x ∈ D) (hrD : r ∈ D)
    (hlm : l < m) (hmx : m < x) (hxr : x < r)
    (hratio : x - m ≤ 2 * (m - l)) (hC : 0 ≤ C)
    (hl : |f l - G| ≤ C) (hm : |f m - G| ≤ C) (hr : |f r - G| ≤ C) :
    |f x - G| ≤ 5 * C := by
  obtain ⟨hll, hlu⟩ := abs_le.mp hl
  obtain ⟨hml, hmu⟩ := abs_le.mp hm
  obtain ⟨hrl, hru⟩ := abs_le.mp hr
  have hupper : f x ≤ G + C := by
    by_contra h
    have hfx : G + C < f x := lt_of_not_ge h
    have hs := hf.slope_mono_adjacent hmD hrD hmx hxr
    have hp : 0 < (f x - f m) / (x - m) :=
      div_pos (by linarith) (sub_pos.mpr hmx)
    have hn : (f r - f x) / (r - x) < 0 :=
      div_neg_of_neg_of_pos (by linarith) (sub_pos.mpr hxr)
    linarith
  have hlower : G - 5 * C ≤ f x := by
    by_contra h
    have hfx : f x < G - 5 * C := lt_of_not_ge h
    have hs := hf.slope_mono_adjacent hlD hxD hlm hmx
    have hcross := (div_le_div_iff₀ (sub_pos.mpr hlm) (sub_pos.mpr hmx)).mp hs
    have hc : (f m - f x) * (m - l) ≤ (f l - f m) * (x - m) := by
      nlinarith [hcross]
    have hleft : 4 * C * (m - l) < (f m - f x) * (m - l) :=
      mul_lt_mul_of_pos_right (by linarith) (sub_pos.mpr hlm)
    have hright : (f l - f m) * (x - m) ≤ 4 * C * (m - l) := by
      calc
        _ ≤ (2 * C) * (x - m) :=
          mul_le_mul_of_nonneg_right (by linarith) (sub_pos.mpr hmx).le
        _ ≤ (2 * C) * (2 * (m - l)) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = _ := by ring
    linarith
  apply abs_le.mpr
  constructor <;> linarith

/-- If the bad set has measure less than `κ`, three disjoint sampling windows
of length `κ` all contain good points. The resulting estimate is uniform in
`x`, in the convex function, and in the geometry of the bad set. -/
theorem convex_deviation_of_small_bad_set (D B : Set ℝ) (f g : ℝ → ℝ)
    (hf : ConvexOn ℝ D f) (hB : volume B ≠ ⊤)
    (x κ ε ω : ℝ) (hκ : 0 < κ) (hε : 0 ≤ ε) (hω : 0 ≤ ω)
    (hbad : volume.real B < κ)
    (hwindow : Icc (x - 4 * κ) (x + 2 * κ) ⊆ D)
    (hgood : ∀ y ∈ D, y ∉ B → |f y - g y| ≤ ε)
    (hosc : ∀ y ∈ Icc (x - 4 * κ) (x + 2 * κ), |g y - g x| ≤ ω) :
    |f x - g x| ≤ 5 * (ε + ω) := by
  obtain ⟨l, hl, hlB⟩ := exists_good_interval_point B hB
    (x - 4 * κ) (x - 3 * κ) κ (by linarith) (by ring) hbad
  obtain ⟨m, hm, hmB⟩ := exists_good_interval_point B hB
    (x - 2 * κ) (x - κ) κ (by linarith) (by ring) hbad
  obtain ⟨r, hr, hrB⟩ := exists_good_interval_point B hB
    (x + κ) (x + 2 * κ) κ (by linarith) (by ring) hbad
  have hlW : l ∈ Icc (x - 4 * κ) (x + 2 * κ) := by
    constructor <;> linarith [hl.1, hl.2]
  have hmW : m ∈ Icc (x - 4 * κ) (x + 2 * κ) := by
    constructor <;> linarith [hm.1, hm.2]
  have hrW : r ∈ Icc (x - 4 * κ) (x + 2 * κ) := by
    constructor <;> linarith [hr.1, hr.2]
  have hxW : x ∈ Icc (x - 4 * κ) (x + 2 * κ) := by
    constructor <;> linarith
  have hval (y : ℝ) (hy : y ∈ Icc (x - 4 * κ) (x + 2 * κ)) (hyB : y ∉ B) :
      |f y - g x| ≤ ε + ω := by
    calc
      _ = |(f y - g y) + (g y - g x)| := by congr 1; ring
      _ ≤ |f y - g y| + |g y - g x| := abs_add _ _
      _ ≤ ε + ω := add_le_add (hgood y (hwindow hy) hyB) (hosc y hy)
  apply convex_three_sample_control D f hf l m x r (g x) (ε + ω)
    (hwindow hlW) (hwindow hmW) (hwindow hxW) (hwindow hrW)
    (by linarith [hl.2, hm.1]) (by linarith [hm.2]) (by linarith [hr.1])
    (by linarith [hl.2, hm.1, hm.2]) (add_nonneg hε hω)
    (hval l hlW hlB) (hval m hmW hmB) (hval r hrW hrB)

end Erdos1152
