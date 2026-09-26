import Erdos1152.V4.HighRegion
import Mathlib.MeasureTheory.Measure.Support

/-!
# The threshold, the true extended potential, and the minus-infinity branch

A real Bochner integral is not used as a pointwise definition at logarithmic
singularities. The extended potential is the decreasing infimum of continuous
truncations; it agrees with the real representative Lebesgue almost everywhere.
The high region has an explicit threshold description even when that threshold
is minus infinity. No support/minimum principle is assumed in these lemmas.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

def SourceLevel (μ : ProbabilityMeasure Segment) (c : ℝ) : Prop :=
  ∃ k : ℕ, 0 < (μ : Measure Segment) {t | truncPotential μ k (t : ℝ) < c}

noncomputable def sourceValues (μ : ProbabilityMeasure Segment) : Set EReal :=
  ((↑) : ℝ → EReal) '' {c | SourceLevel μ c}

noncomputable def potentialFloor (μ : ProbabilityMeasure Segment) : EReal :=
  sInf (sourceValues μ)

noncomputable def extendedPotential (μ : ProbabilityMeasure Segment) (x : ℝ) : EReal :=
  ⨅ k : ℕ, (truncPotential μ k x : EReal)

theorem integrable_trunc_section (μ : ProbabilityMeasure Segment) (k : ℕ) (x : ℝ) :
    Integrable (fun t : Segment => truncProfile k (x - (t : ℝ))) (μ : Measure Segment) :=
  ((continuous_truncProfile k).comp (continuous_const.sub continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem cutoff_antitone : Antitone cutoff := by
  intro k l hkl
  unfold cutoff
  exact inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hkl 1)

theorem truncProfile_antitone (u : ℝ) : Antitone (fun k => truncProfile k u) := by
  intro k l hkl
  unfold truncProfile
  apply Real.log_le_log (lt_of_lt_of_le (cutoff_pos l) (le_max_left _ _))
  exact max_le_max (cutoff_antitone hkl) le_rfl

theorem truncPotential_antitone (μ : ProbabilityMeasure Segment) (x : ℝ) :
    Antitone (fun k => truncPotential μ k x) := by
  intro k l hkl
  exact integral_mono (integrable_trunc_section μ l x) (integrable_trunc_section μ k x)
    (fun t => truncProfile_antitone (x - (t : ℝ)) hkl)

theorem extendedPotential_limit (μ : ProbabilityMeasure Segment) (x : ℝ) :
    Tendsto (fun k => (truncPotential μ k x : EReal)) atTop
      (𝓝 (extendedPotential μ x)) := by
  apply tendsto_atTop_iInf
  intro k l hkl
  exact EReal.coe_le_coe_iff.mpr (truncPotential_antitone μ x hkl)

theorem truncProfile_abs_le_log (k : ℕ) (u : ℝ) (hu : u ≠ 0) :
    |truncProfile k u| ≤ |logProfile u| := by
  by_cases hh : cutoff k ≤ |u|
  · simp only [truncProfile, logProfile, max_eq_right hh, le_refl]
  · have huτ : |u| ≤ cutoff k := (lt_of_not_ge hh).le
    have hlo := Real.log_le_log (abs_pos.mpr hu) huτ
    have hnonpos := Real.log_nonpos (cutoff_pos k).le (cutoff_le_one k)
    have hnonpos' := Real.log_nonpos (abs_nonneg u) (huτ.trans (cutoff_le_one k))
    simp only [truncProfile, logProfile, max_eq_left huτ,
      abs_of_nonpos hnonpos, abs_of_nonpos hnonpos']
    linarith

theorem truncProfile_tendsto_log (u : ℝ) (hu : u ≠ 0) :
    Tendsto (fun k => truncProfile k u) atTop (𝓝 (logProfile u)) := by
  have he := cutoff_tendsto_zero.eventually (gt_mem_nhds (abs_pos.mpr hu))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with k hk
  simp only [truncProfile, logProfile, max_eq_right hk.le]

/-- The diagonal is null for Lebesgue measure in x, even when the source
probability measure has atoms. -/
theorem ae_source_off_diagonal (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, ∀ᵐ t : Segment ∂(μ : Measure Segment), x ≠ (t : ℝ) := by
  rw [Measure.ae_ae_comm]
  · exact Filter.Eventually.of_forall (fun t =>
      ae_restrict_of_ae (Measure.ae_ne volume (t : ℝ)))
  · exact (measurableSet_eq_fun measurable_fst
      (measurable_subtype_coe.comp measurable_snd)).compl

/-- At almost every x the actual source integral is finite and diagonal-free;
then dominated convergence identifies the decreasing pointwise truncations. -/
theorem ae_truncPotential_tendsto (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure,
      Tendsto (fun k => truncPotential μ k x) atTop (𝓝 (potential μ x)) := by
  filter_upwards [(log_integrable_product μ).prod_right_ae, ae_source_off_diagonal μ]
    with x hx hdiag
  apply tendsto_integral_of_dominated_convergence (fun t : Segment => |logProfile (x - t)|)
  · intro k
    exact (integrable_trunc_section μ k x).aestronglyMeasurable
  · exact hx.abs
  · intro k
    filter_upwards [hdiag] with t ht
    simpa only [Real.norm_eq_abs] using truncProfile_abs_le_log k (x - t)
      (sub_ne_zero.mpr ht)
  · filter_upwards [hdiag] with t ht
    exact truncProfile_tendsto_log (x - t) (sub_ne_zero.mpr ht)

theorem ae_extendedPotential_eq (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, extendedPotential μ x = (potential μ x : EReal) := by
  filter_upwards [ae_truncPotential_tendsto μ] with x hx
  exact tendsto_nhds_unique (extendedPotential_limit μ x)
    (EReal.tendsto_coe.mpr hx)

/-- The threshold is characterized without assuming it is finite. -/
theorem potentialFloor_lt_iff (μ : ProbabilityMeasure Segment) (u : ℝ) :
    potentialFloor μ < (u : EReal) ↔ ∃ c : ℝ, SourceLevel μ c ∧ c < u := by
  change sInf (sourceValues μ) < (u : EReal) ↔ _
  rw [sInf_lt_iff]
  constructor
  · rintro ⟨v, ⟨c, hc, rfl⟩, hcu⟩
    exact ⟨c, hc, EReal.coe_lt_coe_iff.mp hcu⟩
  · rintro ⟨c, hc, hcu⟩
    exact ⟨(c : EReal), ⟨c, hc, rfl⟩, EReal.coe_lt_coe_iff.mpr hcu⟩

theorem SourceLevel.mono {μ : ProbabilityMeasure Segment} {c d : ℝ}
    (hc : SourceLevel μ c) (hcd : c ≤ d) : SourceLevel μ d := by
  obtain ⟨k, hk⟩ := hc
  exact ⟨k, hk.trans_le (measure_mono (fun t ht => ht.trans_le hcd))⟩

/-- A purely analytic description of the constructed cover. The rational gaps
are bookkeeping; they do not shrink the high-potential region. -/
theorem mem_highPotentialRegion_iff (μ : ProbabilityMeasure Segment) (x : ℝ) :
    x ∈ highPotentialRegion μ ↔ x ∈ Segment ∧ potentialFloor μ < (potential μ x : EReal) := by
  classical
  constructor
  · intro hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    by_cases hv : ValidLevel μ q
    · rw [potentialLayer, if_pos hv] at hq
      refine ⟨hq.1, (potentialFloor_lt_iff μ _).mpr ?_⟩
      refine ⟨(q.2.1 : ℝ) - 2 * (q.2.2 : ℝ), ⟨q.1, hv.2⟩, ?_⟩
      have hhigh : (q.2.1 : ℝ) + 3 * (q.2.2 : ℝ) ≤ potential μ x := hq.2
      linarith [hv.1]
    · simpa only [potentialLayer, if_neg hv, Set.mem_empty_iff_false] using hq
  · rintro ⟨hx, hfloor⟩
    obtain ⟨c, ⟨k, hc⟩, hcx⟩ := (potentialFloor_lt_iff μ _).mp hfloor
    obtain ⟨ηq, hη0, hηbound⟩ := exists_rat_btwn (by linarith : (0 : ℝ) < (potential μ x - c) / 10)
    obtain ⟨bq, hcb, hbx⟩ := exists_rat_btwn
      (by linarith : c + 2 * (ηq : ℝ) < potential μ x - 3 * (ηq : ℝ))
    let q : LevelIndex := (k, bq, ηq)
    have hmass : 0 < (μ : Measure Segment)
        (Subtype.val ⁻¹' sourceRegion μ k (bq : ℝ) (ηq : ℝ)) := by
      apply hc.trans_le
      apply measure_mono
      intro t ht
      change truncPotential μ k (t : ℝ) < c at ht
      change truncPotential μ k (t : ℝ) < (bq : ℝ) - 2 * (ηq : ℝ)
      linarith
    have hv : ValidLevel μ q := ⟨hη0, hmass⟩
    apply Set.mem_iUnion.mpr
    refine ⟨q, ?_⟩
    rw [potentialLayer, if_pos hv]
    exact ⟨hx, by dsimp [q]; linarith⟩

theorem highPotentialRegion_eq_threshold (μ : ProbabilityMeasure Segment) :
    highPotentialRegion μ = Segment ∩ {x | potentialFloor μ < (potential μ x : EReal)} := by
  ext x
  exact mem_highPotentialRegion_iff μ x

/-- The singular threshold branch is not quietly omitted. It gives the whole
Lebesgue parameter interval, since the representative is finite-valued. -/
theorem highPotentialRegion_of_floor_bot (μ : ProbabilityMeasure Segment)
    (ha : potentialFloor μ = ⊥) : highPotentialRegion μ = Segment := by
  ext x
  rw [mem_highPotentialRegion_iff, ha]
  simp

/-- Identification with the true extended potential is only asserted a.e. -/
theorem ae_highPotentialRegion_iff_extended (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure,
      x ∈ highPotentialRegion μ ↔ potentialFloor μ < extendedPotential μ x := by
  filter_upwards [ae_extendedPotential_eq μ, ae_restrict_mem measurableSet_Icc]
    with x hx hxseg
  rw [mem_highPotentialRegion_iff, hx]
  exact and_iff_right hxseg

/-- The minus-infinity branch supplies hm vacuously; no Bernstein or external
field premise is added for a region that has no remaining points. -/
theorem localAmplificationMinimal_floor_bot (X : NodeArray) (r : ℕ → ℕ)
    (ha : potentialFloor (canonicalMeasure X) = ⊥) :
    LocalAmplificationMinimal X r (canonicalHighRegion X) := by
  have hG : canonicalHighRegion X = Segment :=
    highPotentialRegion_of_floor_bot (canonicalMeasure X) ha
  intro H hH
  refine ⟨1, by norm_num, le_rfl, ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  intro hxc
  have hxG : x ∈ canonicalHighRegion X := by
    rw [hG]
    exact ⟨hx.1.le, hx.2.le⟩
  exact False.elim (hxc hxG)

/-- The threshold is bounded above; only the finite or minus-infinity cases
can occur. This proof uses the actual source probability mass. -/
theorem potentialFloor_ne_top (μ : ProbabilityMeasure Segment) : potentialFloor μ ≠ ⊤ := by
  have hbound (t : Segment) : truncPotential μ 0 (t : ℝ) ≤ Real.log 2 := by
    calc
      _ ≤ ∫ _z : Segment, Real.log 2 ∂(μ : Measure Segment) := by
        apply integral_mono (integrable_trunc_section μ 0 t) (integrable_const _)
        intro z
        apply Real.log_le_log (lt_of_lt_of_le (cutoff_pos 0) (le_max_left _ _))
        apply max_le
        · exact (cutoff_le_one 0).trans (by norm_num)
        · apply abs_le.mpr
          constructor <;> linarith [t.property.1, t.property.2, z.property.1, z.property.2]
      _ = Real.log 2 := by simp
  have hs : SourceLevel μ (Real.log 2 + 1) := by
    refine ⟨0, ?_⟩
    have heq : {t : Segment | truncPotential μ 0 t < Real.log 2 + 1} = Set.univ := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      linarith [hbound t]
    rw [heq]
    simp
  have hle : potentialFloor μ ≤ ((Real.log 2 + 1 : ℝ) : EReal) :=
    sInf_le ⟨Real.log 2 + 1, hs, rfl⟩
  exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hle

/-- At every support point, each truncated value is at least the threshold.
A contradiction would create a positive-mass open sublevel below the infimum. -/
theorem potentialFloor_le_trunc_at_support (μ : ProbabilityMeasure Segment)
    (t : Segment) (ht : t ∈ (μ : Measure Segment).support) (k : ℕ) :
    potentialFloor μ ≤ (truncPotential μ k (t : ℝ) : EReal) := by
  by_contra! hlt
  obtain ⟨c, hc₁, hc₂⟩ := EReal.exists_between_coe_real hlt
  have htc : truncPotential μ k (t : ℝ) < c := EReal.coe_lt_coe_iff.mp hc₁
  have hopen : IsOpen {z : Segment | truncPotential μ k (z : ℝ) < c} :=
    isOpen_lt ((continuous_truncPotential μ k).comp continuous_subtype_val) continuous_const
  have hmass := (Measure.mem_support_iff_forall t).mp ht _ (hopen.mem_nhds htc)
  have hle : potentialFloor μ ≤ (c : EReal) := sInf_le ⟨c, ⟨k, hmass⟩, rfl⟩
  exact (not_le_of_gt hc₂) hle

theorem potentialFloor_le_extended_at_support (μ : ProbabilityMeasure Segment)
    (t : Segment) (ht : t ∈ (μ : Measure Segment).support) :
    potentialFloor μ ≤ extendedPotential μ t :=
  le_iInf (fun k => potentialFloor_le_trunc_at_support μ t ht k)

/-- The analytic threshold is exactly the original infimum over the support,
including the value minus infinity. This identifies the cover's region with
the region used in the supplied mathematical proof. -/
theorem potentialFloor_eq_iInf_support (μ : ProbabilityMeasure Segment) :
    potentialFloor μ =
      ⨅ (t : Segment) (_ : t ∈ (μ : Measure Segment).support), extendedPotential μ t := by
  apply le_antisymm
  · exact le_iInf (fun t => le_iInf (fun ht => potentialFloor_le_extended_at_support μ t ht))
  · apply le_sInf
    rintro v ⟨c, ⟨k, hk⟩, rfl⟩
    obtain ⟨t, htc, hts⟩ := Measure.nonempty_inter_support_of_pos hk
    calc
      _ ≤ extendedPotential μ t := iInf_le_of_le t (iInf_le _ hts)
      _ ≤ (truncPotential μ k t : EReal) := iInf_le _ k
      _ ≤ (c : EReal) := EReal.coe_le_coe_iff.mpr htc.le

end Erdos1152.V4
