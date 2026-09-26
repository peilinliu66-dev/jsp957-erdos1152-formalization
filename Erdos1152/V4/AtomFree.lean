import Erdos1152.V4.PositiveDensity

/-!
# A finite logarithmic floor excludes every source atom

The proof bounds the atom's contribution by its mass times log(cutoff),
while the remaining source integral is at most log 2. In particular, all
endpoints of a local interval are continuity points for the limiting measure.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

theorem truncProfile_source_le_log_two (k : ℕ) (t z : Segment) :
    truncProfile k ((t : ℝ) - (z : ℝ)) ≤ Real.log 2 := by
  apply Real.log_le_log (lt_of_lt_of_le (cutoff_pos k) (le_max_left _ _))
  apply max_le
  · exact (cutoff_le_one k).trans (by norm_num)
  · apply abs_le.mpr
    constructor <;> linarith [t.property.1, t.property.2, z.property.1, z.property.2]

theorem truncPotential_atom_upper (μ : ProbabilityMeasure Segment) (t : Segment) (k : ℕ) :
    truncPotential μ k t ≤
      (μ : Measure Segment).real {t} * Real.log (cutoff k) + Real.log 2 := by
  let f : Segment → ℝ := fun z => truncProfile k ((t : ℝ) - (z : ℝ))
  have hi : Integrable f (μ : Measure Segment) := integrable_trunc_section μ k t
  have hs : MeasurableSet ({t} : Set Segment) := measurableSet_singleton _
  have hatom : (∫ z in ({t} : Set Segment), f z ∂(μ : Measure Segment)) =
      (μ : Measure Segment).real {t} * Real.log (cutoff k) := by
    calc
      _ = ∫ _z in ({t} : Set Segment), Real.log (cutoff k) ∂(μ : Measure Segment) := by
        apply setIntegral_congr_fun hs
        intro z hz
        have he : z = t := Set.mem_singleton_iff.mp hz
        subst z
        simp only [f, sub_self, truncProfile, abs_zero, max_eq_left (cutoff_pos k).le]
      _ = _ := by simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
  have hrest : (∫ z in ({t} : Set Segment)ᶜ, f z ∂(μ : Measure Segment)) ≤ Real.log 2 := by
    calc
      _ ≤ ∫ _z in ({t} : Set Segment)ᶜ, Real.log 2 ∂(μ : Measure Segment) := by
        apply integral_mono_ae hi.restrict (integrable_const _)
        exact Filter.Eventually.of_forall (truncProfile_source_le_log_two k t)
      _ = (μ : Measure Segment).real ({t} : Set Segment)ᶜ * Real.log 2 := by
        simp only [integral_const, measureReal_restrict_apply_univ, smul_eq_mul]
      _ ≤ Real.log 2 := by
        apply mul_le_of_le_one_left (Real.log_nonneg (by norm_num))
        exact measureReal_le_one
  have hadd := integral_add_compl hs hi
  change (∫ z, f z ∂(μ : Measure Segment)) ≤ _
  rw [← hadd, hatom]
  linarith

theorem potentialFloor_bot_of_atom (μ : ProbabilityMeasure Segment) (t : Segment)
    (ht : 0 < (μ : Measure Segment) {t}) : potentialFloor μ = ⊥ := by
  have hα : 0 < (μ : Measure Segment).real {t} :=
    ENNReal.toReal_pos ht.ne' (measure_ne_top _ _)
  have hlevel (c : ℝ) : SourceLevel μ c := by
    let α := (μ : Measure Segment).real {t}
    obtain ⟨k, hk⟩ := exists_nat_gt (Real.exp ((Real.log 2 - c + 1) / α))
    have hk' : Real.exp ((Real.log 2 - c + 1) / α) < (k + 1 : ℝ) := by
      exact hk.trans (by exact_mod_cast Nat.lt_succ_self k)
    have hh := Real.log_lt_log (Real.exp_pos _) hk'
    rw [Real.log_exp] at hh
    have hmul := (div_lt_iff₀ hα).mp hh
    have hclip : truncPotential μ k t < c := by
      have hb := truncPotential_atom_upper μ t k
      rw [cutoff, Real.log_inv] at hb
      change truncPotential μ k t ≤ α * -Real.log (k + 1 : ℝ) + Real.log 2 at hb
      nlinarith
    refine ⟨k, ht.trans_le (measure_mono ?_)⟩
    intro z hz
    have he : z = t := Set.mem_singleton_iff.mp hz
    change truncPotential μ k (z : ℝ) < c
    simpa only [he] using hclip
  apply le_antisymm _ bot_le
  by_contra! h
  obtain ⟨c, _, hc⟩ := EReal.exists_between_coe_real h
  exact (not_le_of_gt hc) (sInf_le ⟨c, hlevel c, rfl⟩)

theorem source_singleton_zero_of_floor_ne_bot (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (t : Segment) : (μ : Measure Segment) {t} = 0 := by
  by_contra hn
  exact hfloor (potentialFloor_bot_of_atom μ t (bot_lt_iff_ne_bot.mpr hn))

theorem source_nullSingletonClass (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) : NullSingletonClass (μ : Measure Segment) :=
  ⟨source_singleton_zero_of_floor_ne_bot μ hfloor⟩

theorem realSource_singleton_zero_of_floor_ne_bot (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x : ℝ) : realSource μ {x} = 0 := by
  rw [realSource_apply μ _ (measurableSet_singleton x)]
  by_cases hx : x ∈ Segment
  · let t : Segment := ⟨x, hx⟩
    have he : (Subtype.val ⁻¹' ({x} : Set ℝ)) = ({t} : Set Segment) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      rfl
    rw [he]
    exact source_singleton_zero_of_floor_ne_bot μ hfloor t
  · have he : (Subtype.val ⁻¹' ({x} : Set ℝ)) = (∅ : Set Segment) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hx (h ▸ z.property)
    simp only [he, measure_empty]

end Erdos1152.V4
