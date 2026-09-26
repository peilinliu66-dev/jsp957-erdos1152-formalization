import Erdos1152.V4.LocalMass
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.ProjIcc

/-!
# The actual normalized tangent probability measure

The measure is the normalized restriction of the original source to (x-h,x+h),
pushed forward by t ↦ (t-x)/h. Its weak limit is proved from the actual CDF
and the π-system of open intervals, not supplied as a tangent-measure premise.
Mapping to Segment then supplies the logarithmic-potential L¹ limit used to
remove the affine term of the local external field.

This file is candidate source, not a compilation receipt.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def tangentRealProbability (μ : ProbabilityMeasure Segment) (x h : ℝ) :
    ProbabilityMeasure ℝ := by
  classical
  let I : Set ℝ := Ioo (x-h) (x+h)
  let m : ℝ≥0∞ := realSource μ I
  by_cases hm : m = 0
  · exact ⟨Measure.dirac 0, inferInstance⟩
  · let ν : ProbabilityMeasure ℝ :=
      ⟨m⁻¹ • (realSource μ).restrict I, by
        constructor
        simp only [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ,
          Set.univ_inter, smul_eq_mul]
        exact ENNReal.inv_mul_cancel hm (measure_ne_top _ _)⟩
    exact ν.map (show AEMeasurable (fun t : ℝ => (t-x)/h) (ν : Measure ℝ) by fun_prop)

noncomputable def uniformRealProbability : ProbabilityMeasure ℝ :=
  ⟨ENNReal.ofReal (1/2 : ℝ) • baseMeasure, by
    constructor
    norm_num [baseMeasure, Segment, Measure.smul_apply, Measure.restrict_apply,
      Real.volume_Icc, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

/-- Exact evaluation of the actual normalized restriction and affine image. -/
theorem tangentRealProbability_real_apply (μ : ProbabilityMeasure Segment) (x h : ℝ)
    (hm : 0 < (realSource μ).real (Ioo (x-h) (x+h)))
    (E : Set ℝ) (hE : MeasurableSet E) :
    (tangentRealProbability μ x h : Measure ℝ).real E =
      (realSource μ).real ((fun t : ℝ => (t-x)/h) ⁻¹' E ∩ Ioo (x-h) (x+h)) /
        (realSource μ).real (Ioo (x-h) (x+h)) := by
  have hm0 : realSource μ (Ioo (x-h) (x+h)) ≠ 0 := by
    intro he
    simp only [Measure.real, he, ENNReal.toReal_zero] at hm
    exact (lt_irrefl 0 hm)
  have hf : Measurable (fun t : ℝ => (t-x)/h) := by fun_prop
  change ((tangentRealProbability μ x h : Measure ℝ) E).toReal = _
  simp [tangentRealProbability, hm0, ProbabilityMeasure.map, ProbabilityMeasure.toMeasure,
    Measure.smul_apply, smul_eq_mul, Measure.real, ENNReal.toReal_mul,
    ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
  left
  have hf' : Measurable (fun t : ℝ => (t - x) * h⁻¹) := by fun_prop
  rw [Measure.map_apply hf' hE, Measure.restrict_apply (hf' hE)]

private theorem affine_interval_inter (x h α β : ℝ) (hh : 0 < h) :
    ((fun t : ℝ => (t-x)/h) ⁻¹' Ioo α β) ∩ Ioo (x-h) (x+h) =
      Ioo (x+h*max (-1) α) (x+h*min 1 β) := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ioo,
    lt_div_iff₀ hh, div_lt_iff₀ hh]
  constructor
  · rintro ⟨⟨hα,hβ⟩,⟨hl,hr⟩⟩
    constructor
    · by_cases ha : -1 ≤ α
      · rw [max_eq_right ha]
        nlinarith
      · rw [max_eq_left (le_of_not_ge ha)]
        nlinarith
    · by_cases hb : β ≤ 1
      · rw [min_eq_right hb]
        nlinarith
      · rw [min_eq_left (le_of_not_ge hb)]
        nlinarith
  · rintro ⟨hl,hr⟩
    have hα := mul_le_mul_of_nonneg_left (le_max_right (-1 : ℝ) α) hh.le
    have hminus := mul_le_mul_of_nonneg_left (le_max_left (-1 : ℝ) α) hh.le
    have hβ := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) β) hh.le
    have hone := mul_le_mul_of_nonneg_left (min_le_left (1 : ℝ) β) hh.le
    exact ⟨⟨by nlinarith,by nlinarith⟩,⟨by nlinarith,by nlinarith⟩⟩

/-- The two interval endpoints are explicitly discarded as volume-null points. -/
theorem uniformRealProbability_Ioo (α β : ℝ) :
    (uniformRealProbability : Measure ℝ).real (Ioo α β) =
      max (min 1 β-max (-1) α) 0 / 2 := by
  have he : (Ioo α β ∩ Segment : Set ℝ) =ᵐ[volume]
      Ioo (max (-1) α) (min 1 β) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (-1 : ℝ)),
      compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ))] with t ht0 ht1
    have ht0' : t ≠ -1 := ht0
    have ht1' : t ≠ 1 := ht1
    apply propext
    change ((α < t ∧ t < β) ∧ (-1 ≤ t ∧ t ≤ 1)) ↔
      (max (-1) α < t ∧ t < min 1 β)
    simp only [max_lt_iff, lt_min_iff]
    constructor
    · rintro ⟨⟨hα,hβ⟩,⟨h0,h1⟩⟩
      exact ⟨⟨lt_of_le_of_ne h0 ht0'.symm,hα⟩,⟨lt_of_le_of_ne h1 ht1',hβ⟩⟩
    · rintro ⟨⟨h0,hα⟩,⟨h1,hβ⟩⟩
      exact ⟨⟨hα,hβ⟩,⟨h0.le,h1.le⟩⟩
  have hv := measure_congr he
  simp only [uniformRealProbability, ProbabilityMeasure.coe_mk, Measure.real,
    Measure.smul_apply, baseMeasure, Measure.restrict_apply measurableSet_Ioo,
    smul_eq_mul, ENNReal.toReal_mul]
  rw [hv, Real.volume_Ioo]
  simp only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ENNReal.toReal_ofReal']
  ring

/-- The local tangent distribution converges on every open interval. -/
theorem tangentRealProbability_Ioo_tendsto (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w : ℝ) (hw : 0 < w)
    (hx : HasDerivAt (sourceCDF μ) w x) (α β : ℝ) :
    Tendsto (fun h : ℝ => (tangentRealProbability μ x h : Measure ℝ).real (Ioo α β))
      (𝓝[>] 0) (𝓝 ((uniformRealProbability : Measure ℝ).real (Ioo α β))) := by
  let a := max (-1 : ℝ) α
  let b := min (1 : ℝ) β
  have hmass : ∀ᶠ h : ℝ in 𝓝[>] 0,
      0 < (realSource μ).real (Ioo (x-h) (x+h)) := by
    have hh := (eventually_local_mass_and_central_fraction μ hfloor x w hw hx 1 (by norm_num)).mono
      (fun _ h => h.1)
    filter_upwards [hh] with h hpos
    simpa only [Measure.real, realSource_apply μ _ measurableSet_Ioo, sourceInterval] using hpos
  by_cases hab : a ≤ b
  · have ht := local_relative_interval_mass μ hfloor x w a b hw hab hx
    have he : ∀ᶠ h : ℝ in 𝓝[>] 0,
        (μ : Measure Segment).real (sourceInterval (x+h*a) (x+h*b)) /
          (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) =
        (tangentRealProbability μ x h : Measure ℝ).real (Ioo α β) := by
      filter_upwards [self_mem_nhdsWithin,hmass] with h hh hm
      change 0 < h at hh
      rw [tangentRealProbability_real_apply μ x h hm _ measurableSet_Ioo,
        affine_interval_inter x h α β hh]
      simp only [a,b,Measure.real,realSource_apply μ _ measurableSet_Ioo,sourceInterval]
    rw [uniformRealProbability_Ioo, max_eq_left (sub_nonneg.mpr hab)]
    exact ht.congr' he
  · have hba : b ≤ a := le_of_lt (lt_of_not_ge hab)
    have he : ∀ᶠ h : ℝ in 𝓝[>] 0,
        (tangentRealProbability μ x h : Measure ℝ).real (Ioo α β) = 0 := by
      filter_upwards [self_mem_nhdsWithin,hmass] with h hh hm
      change 0 < h at hh
      rw [tangentRealProbability_real_apply μ x h hm _ measurableSet_Ioo,
        affine_interval_inter x h α β hh]
      have horder : x+h*b ≤ x+h*a := by nlinarith
      rw [Set.Ioo_eq_empty_of_le horder]
      simp
    have hlim : (uniformRealProbability : Measure ℝ).real (Ioo α β) = 0 := by
      rw [uniformRealProbability_Ioo, max_eq_right (sub_nonpos.mpr hba)]
      simp
    rw [hlim]
    exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm he)

/-- Weak convergence is proved with the library π-system criterion. The only
input on x is the actual CDF derivative, which is supplied a.e. on the minimum. -/
theorem tangentRealProbability_tendsto (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w : ℝ) (hw : 0 < w)
    (hx : HasDerivAt (sourceCDF μ) w x) :
    Tendsto (tangentRealProbability μ x) (𝓝[>] 0) (𝓝 uniformRealProbability) := by
  let S : Set (Set ℝ) := {E | ∃ a b : ℝ, E = Ioo a b}
  have hpi : IsPiSystem S := by
    rintro E ⟨a,b,rfl⟩ F ⟨c,d,rfl⟩ _
    exact ⟨max a c,min b d,Set.Ioo_inter_Ioo⟩
  apply hpi.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro E ⟨a,b,rfl⟩
    exact measurableSet_Ioo
  · intro U hU z hz
    obtain ⟨a,b,hzab,habU⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hz)
    exact ⟨Ioo a b,⟨a,b,rfl⟩,Ioo_mem_nhds hzab.1 hzab.2,habU⟩
  · rintro E ⟨a,b,rfl⟩
    apply NNReal.tendsto_coe.mp
    simpa using
      tangentRealProbability_Ioo_tendsto μ hfloor x w hw hx a b

noncomputable def clampSegment (t : ℝ) : Segment :=
  Set.projIcc (-1 : ℝ) 1 (by norm_num) t

theorem continuous_clampSegment : Continuous clampSegment := by
  unfold clampSegment
  exact continuous_projIcc

noncomputable def tangentProbability (μ : ProbabilityMeasure Segment) (x h : ℝ) :
    ProbabilityMeasure Segment :=
  (tangentRealProbability μ x h).map continuous_clampSegment.measurable.aemeasurable

noncomputable def uniformSegmentProbability : ProbabilityMeasure Segment :=
  uniformRealProbability.map continuous_clampSegment.measurable.aemeasurable

theorem tangentProbability_tendsto (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w : ℝ) (hw : 0 < w)
    (hx : HasDerivAt (sourceCDF μ) w x) :
    Tendsto (tangentProbability μ x) (𝓝[>] 0) (𝓝 uniformSegmentProbability) := by
  exact ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (tangentRealProbability μ x) uniformRealProbability
    (tangentRealProbability_tendsto μ hfloor x w hw hx) continuous_clampSegment

/-- The actual rescaled local logarithmic potentials converge in L¹.
The generic weak-potential theorem is applied to every sequence of radii;
no L¹-limit is an additional assumption. -/
theorem tangent_potential_L1 (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w : ℝ) (hw : 0 < w)
    (hx : HasDerivAt (sourceCDF μ) w x) :
    Tendsto (fun h : ℝ => ∫ u,
      |potential (tangentProbability μ x h) u-potential uniformSegmentProbability u| ∂baseMeasure)
      (𝓝[>] 0) (𝓝 0) := by
  apply Filter.tendsto_of_seq_tendsto
  intro hs hhs
  exact weak_convergence_potential_L1 (fun n => tangentProbability μ x (hs n))
    uniformSegmentProbability ((tangentProbability_tendsto μ hfloor x w hw hx).comp hhs)

/-- Public actual-source result at almost every point in the leftover region. -/
theorem ae_minimum_tangent_potential_L1 (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, x ∉ highPotentialRegion μ →
      Tendsto (fun h : ℝ => ∫ u,
        |potential (tangentProbability μ x h) u-potential uniformSegmentProbability u| ∂baseMeasure)
        (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_positive_CDF_derivative_on_minimum μ]
    with x hx hgood
  intro hnot
  obtain ⟨hder,hpos⟩ := hgood hnot
  have hf : potentialFloor μ ≠ ⊥ := by
    intro hbot
    apply hnot
    rw [highPotentialRegion_of_floor_bot μ hbot]
    exact hx
  exact tangent_potential_L1 μ hf x (sourceDensity μ x) hpos hder

end Erdos1152.V4
