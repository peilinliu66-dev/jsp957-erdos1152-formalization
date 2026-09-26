import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Finite disjoint subfamilies of the local intervals used in Proposition 11. -/

open Set MeasureTheory Metric Filter
open scoped ENNReal

namespace Erdos1152

theorem finite_disjoint_intervals {a b : ℝ} (hab : a < b) (P : ℝ → ℝ → Prop)
    (hP : ∀ᵐ x ∂volume.restrict (Ioo a b), ∀ ε > (0 : ℝ),
      ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ P x r) :
    ∃ s : Finset (ℝ × ℝ),
      (∀ z ∈ s, 0 < z.2 ∧ P z.1 z.2 ∧ Icc (z.1 - z.2) (z.1 + z.2) ⊆ Ioo a b) ∧
      (s : Set (ℝ × ℝ)).Pairwise (fun z w => Disjoint (Icc (z.1 - z.2) (z.1 + z.2))
        (Icc (w.1 - w.2) (w.1 + w.2))) ∧
      (b - a) / 2 < ∑ z ∈ s, 2 * z.2 := by
  classical
  let good := {x : ℝ | ∀ ε > (0 : ℝ), ∃ r : ℝ, 0 < r ∧ r ≤ ε ∧ P x r}
  let t := {z : ℝ × ℝ | 0 < z.2 ∧ P z.1 z.2 ∧ closedBall z.1 z.2 ⊆ Ioo a b}
  have hcover : ∀ x ∈ Ioo a b ∩ good, ∀ ε > (0 : ℝ),
      ∃ z ∈ t, z.2 ≤ ε ∧ z.1 = x := by
    rintro x ⟨hx, hg⟩ ε hε
    let d := min ε (min (x - a) (b - x) / 2)
    have hxa : 0 < x - a := sub_pos.mpr hx.1
    have hbx : 0 < b - x := sub_pos.mpr hx.2
    have hd : 0 < d := by dsimp [d]; positivity
    obtain ⟨r, hr, hrd, hpr⟩ := hg d hd
    refine ⟨(x, r), ⟨hr, hpr, ?_⟩, hrd.trans (min_le_left _ _), rfl⟩
    intro y hy
    rw [Real.closedBall_eq_Icc] at hy
    have hdx : d ≤ (x - a) / 2 := (min_le_right _ _).trans (by gcongr; exact min_le_left _ _)
    have hdy : d ≤ (b - x) / 2 := (min_le_right _ _).trans (by gcongr; exact min_le_right _ _)
    constructor <;> linarith [hy.1, hy.2, hx.1, hx.2]
  obtain ⟨u, hut, huc, hud, hucover⟩ := Vitali.exists_disjoint_covering_ae volume
    (Ioo a b ∩ good) t 3 Prod.snd Prod.fst (fun z => closedBall z.1 z.2)
    (fun _ _ => Subset.rfl) (by
      intro z hz
      rw [Real.volume_closedBall, Real.volume_closedBall]
      norm_num only [ENNReal.coe_ofNat]
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
      apply le_of_eq
      congr 1
      ring) (by
      intro z hz
      rw [Real.closedBall_eq_Icc, interior_Icc]
      exact nonempty_Ioo.mpr (by linarith [hz.1]))
    (fun _ _ => isClosed_closedBall) hcover
  let : Countable u := huc.to_subtype
  let B := fun z : u => closedBall z.val.1 z.val.2
  have hJ : volume (Ioo a b) ≤ ∑' z : u, volume (B z) := by
    have hgood : ∀ᵐ x ∂volume, x ∈ Ioo a b → x ∈ good := ae_imp_of_ae_restrict hP
    have hucov : ∀ᵐ x ∂volume, x ∈ Ioo a b ∩ good → x ∈ ⋃ z ∈ u, closedBall z.1 z.2 := by
      apply ae_iff.mpr
      convert hucover using 1
      congr 1
      ext x
      simp [and_assoc]
    have hle : Ioo a b ≤ᵐ[volume] ⋃ z ∈ u, closedBall z.1 z.2 := by
      filter_upwards [hgood, hucov] with x hg hu hx
      exact hu ⟨hx, hg hx⟩
    apply (measure_mono_ae hle).trans
    rw [biUnion_eq_iUnion]
    exact measure_iUnion_le _
  have hhalf : ENNReal.ofReal ((b - a) / 2) < volume (Ioo a b) := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith)
  have hsum := hhalf.trans_le hJ
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hsum
  obtain ⟨F, hF⟩ := hsum
  refine ⟨F.image Subtype.val, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    simpa only [t, mem_ofPred_eq, Real.closedBall_eq_Icc] using hut w.property
  · intro z hz w hw hzw
    obtain ⟨z', _, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨w', _, rfl⟩ := Finset.mem_image.mp hw
    simpa only [Real.closedBall_eq_Icc] using hud z'.property w'.property hzw
  · rw [Finset.sum_image (fun _ _ _ _ h => Subtype.val_injective h)]
    have hBfin (z : u) : volume (B z) ≠ ⊤ := by
      change volume (closedBall z.val.1 z.val.2) ≠ ⊤
      rw [Real.volume_closedBall]
      exact ENNReal.ofReal_ne_top
    have hsumfin : (∑ z ∈ F, volume (B z)) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr (fun z _ => hBfin z)
    have hr := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hsumfin).mpr hF
    rw [ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_sum (fun z _ => hBfin z)] at hr
    have hBreal (z : u) : (volume (B z)).toReal = 2 * z.val.2 := by
      change (volume (closedBall z.val.1 z.val.2)).toReal = _
      rw [Real.volume_closedBall, ENNReal.toReal_ofReal]
      have := (hut z.property).1
      positivity
    simpa only [hBreal] using hr

end Erdos1152
