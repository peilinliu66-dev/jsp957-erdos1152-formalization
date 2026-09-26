import Erdos1152.V5.FilterKernel
import Erdos1152.V4.TangentMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Exact identities for the genuine local tangent measure

The normalization and the clamp are unfolded here; a tangent measure with
postulated identities is not introduced.  Logarithmic scale identities are
used only away from the source diagonal, which is null when the floor is finite.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V5
open V4

/-- The clamp creates no atoms, since the original uniform probability is
supported on Segment and the clamp is the identity there. -/
theorem uniformSegment_val_singleton (a : ℝ) :
    (uniformSegmentProbability : Measure Segment) {t | (t : ℝ)=a} = 0 := by
  have hE : MeasurableSet {t : Segment | (t : ℝ)=a} :=
    (isClosed_eq continuous_subtype_val continuous_const).measurableSet
  rw [uniformSegmentProbability,ProbabilityMeasure.map_apply' _ _ hE]
  change (ENNReal.ofReal (1/2 : ℝ) • baseMeasure)
    (clampSegment ⁻¹' {t : Segment | (t : ℝ)=a}) = 0
  rw [Measure.smul_apply,baseMeasure,Measure.restrict_apply
    (continuous_clampSegment.measurable hE)]
  have hsub : (clampSegment ⁻¹' {t : Segment | (t : ℝ)=a}) ∩ Segment ⊆ {a} := by
    intro t ht
    have hc : (clampSegment t : ℝ)=t := by
      simp only [clampSegment,Set.projIcc_of_mem _ ht.2,Subtype.coe_mk]
    have hv : (clampSegment t : ℝ)=a := ht.1
    exact hc.symm.trans hv
  rw [measure_mono_null hsub (measure_singleton a)]
  simp

theorem uniformSegment_interval_null_frontier (a b : ℝ) (hab : a < b) :
    (uniformSegmentProbability : Measure Segment) (frontier (sourceInterval a b)) = 0 := by
  have hsub : frontier (sourceInterval a b) ⊆
      {t : Segment | (t : ℝ)=a} ∪ {t : Segment | (t : ℝ)=b} := by
    intro t ht
    have hf := continuous_subtype_val.frontier_preimage_subset (Ioo a b) ht
    have hf' : (t : ℝ) ∈ Icc a b ∧ (t : ℝ) ∉ Ioo a b := by
      simpa only [frontier,closure_Ioo hab.ne,interior_Ioo,mem_preimage,Set.mem_sdiff] using hf
    by_cases hta : (t : ℝ)=a
    · exact Or.inl hta
    · right
      exact le_antisymm hf'.1.2 (not_lt.mp (fun htlt =>
        hf'.2 ⟨lt_of_le_of_ne hf'.1.1 (Ne.symm hta),htlt⟩))
  exact measure_mono_null hsub (measure_union_null
    (uniformSegment_val_singleton a) (uniformSegment_val_singleton b))

noncomputable def localMass (μ : ProbabilityMeasure Segment) (x h : ℝ) : ℝ :=
  (μ : Measure Segment).real (sourceInterval (x-h) (x+h))

@[simp] theorem localMass_realSource (μ : ProbabilityMeasure Segment) (x h : ℝ) :
    (realSource μ).real (Ioo (x-h) (x+h)) = localMass μ x h := by
  simp only [localMass, Measure.real, realSource_apply μ _ measurableSet_Ioo, sourceInterval]

/-- Integrating against the real push-forward does not change the underlying source. -/
theorem integral_realSource_restrict (μ : ProbabilityMeasure Segment)
    (a b : ℝ) (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t in Ioo a b, f t ∂realSource μ) =
      ∫ t in sourceInterval a b, f (t : ℝ) ∂(μ : Measure Segment) := by
  rw [← integral_indicator measurableSet_Ioo]
  change (∫ t, (Ioo a b).indicator f t ∂(Measure.map Subtype.val (μ : Measure Segment))) = _
  rw [integral_map_of_stronglyMeasurable measurable_subtype_coe
    (hf.indicator measurableSet_Ioo).stronglyMeasurable]
  have he : (fun t : Segment => (Ioo a b).indicator f (t : ℝ)) =
      (sourceInterval a b).indicator (fun t : Segment => f (t : ℝ)) := by
    funext t
    by_cases ht : (t : ℝ) ∈ Ioo a b <;> simp [sourceInterval,ht]
  rw [he,integral_indicator (measurableSet_sourceInterval a b)]

/-- Exact normalized integral, valid for every measurable real integrand. -/
theorem integral_tangentProbability (μ : ProbabilityMeasure Segment) (x h : ℝ)
    (hm : 0 < localMass μ x h) (f : Segment → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(tangentProbability μ x h : Measure Segment)) =
      (∫ t in sourceInterval (x-h) (x+h),
        f (clampSegment (((t : ℝ)-x)/h)) ∂(μ : Measure Segment)) / localMass μ x h := by
  have hmR : 0 < (realSource μ).real (Ioo (x-h) (x+h)) := by simpa using hm
  have hm0 : realSource μ (Ioo (x-h) (x+h)) ≠ 0 := by
    intro he
    simp only [Measure.real,he,ENNReal.toReal_zero] at hmR
    exact (lt_irrefl 0 hmR)
  rw [tangentProbability,ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable continuous_clampSegment.measurable hf.stronglyMeasurable]
  have htangent : (tangentRealProbability μ x h : Measure ℝ) =
      Measure.map (fun t : ℝ => (t-x)/h)
        ((realSource μ (Ioo (x-h) (x+h)))⁻¹ •
          (realSource μ).restrict (Ioo (x-h) (x+h))) := by
    simp [tangentRealProbability, hm0, ProbabilityMeasure.map, ProbabilityMeasure.toMeasure]
  rw [htangent]
  rw [integral_map_of_stronglyMeasurable (f := fun t => f (clampSegment t))
    (by fun_prop) (by exact (hf.comp continuous_clampSegment.measurable).stronglyMeasurable),
    integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul]
  rw [integral_realSource_restrict μ (x-h) (x+h)
    (fun t => f (clampSegment ((t-x)/h)))
    (by exact hf.comp (continuous_clampSegment.measurable.comp (by fun_prop)))]
  change ((realSource μ).real (Ioo (x-h) (x+h)))⁻¹ * _ = _
  rw [localMass_realSource]
  ring

/-- The clipping map is genuinely inactive on the source interval. -/
theorem clamp_rescale_coe (x h : ℝ) (hh : 0 < h) (t : Segment)
    (ht : t ∈ sourceInterval (x-h) (x+h)) :
    (clampSegment (((t : ℝ)-x)/h) : ℝ) = ((t : ℝ)-x)/h := by
  have ht' : x-h < (t : ℝ) ∧ (t : ℝ) < x+h := ht
  have hr : ((t : ℝ)-x)/h ∈ Segment := by
    constructor
    · rw [le_div_iff₀ hh]; linarith [ht'.1]
    · rw [div_le_iff₀ hh]; linarith [ht'.2]
  simp only [clampSegment,Set.projIcc_of_mem _ hr,Subtype.coe_mk]

/-- There is no atom at a prescribed real point, including points outside Segment. -/
theorem ae_source_ne (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (z : ℝ) :
    ∀ᵐ t : Segment ∂(μ : Measure Segment), z ≠ (t : ℝ) := by
  have hn : (μ : Measure Segment) {t : Segment | z = (t : ℝ)} = 0 := by
    have he : {t : Segment | z = (t : ℝ)} = Subtype.val ⁻¹' ({z} : Set ℝ) := by
      ext t; simp [eq_comm]
    rw [he,← realSource_apply μ _ (measurableSet_singleton z)]
    exact realSource_singleton_zero_of_floor_ne_bot μ hfloor z
  simpa only [ae_iff, not_not] using hn

/-- The logarithmic scale formula deliberately excludes the zero factor. -/
theorem logProfile_affine (x h u t : ℝ) (hh : 0 < h) (hne : x+h*u ≠ t) :
    logProfile (x+h*u-t) = Real.log h + logProfile (u-(t-x)/h) := by
  have hd : u-(t-x)/h ≠ 0 := by
    intro he
    have hu : u=(t-x)/h := sub_eq_zero.mp he
    have := (eq_div_iff hh.ne').mp hu
    apply hne; nlinarith
  have he : x+h*u-t = h*(u-(t-x)/h) := by field_simp [hh.ne']; ring
  rw [he,logProfile,abs_mul,Real.log_mul (abs_pos.mpr hh.ne').ne'
    (abs_pos.mpr hd).ne',abs_of_pos hh]
  rfl

/-- Exact local potential identity; the only integrability hypothesis is the
actual logarithmic section at the point under evaluation. -/
theorem local_log_integral (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x h u : ℝ) (hh : 0 < h)
    (hm : 0 < localMass μ x h)
    (hi : Integrable (fun t : Segment => logProfile (x+h*u-(t : ℝ)))
      (μ : Measure Segment)) :
    (∫ t in sourceInterval (x-h) (x+h), logProfile (x+h*u-(t : ℝ))
      ∂(μ : Measure Segment)) =
      localMass μ x h * (Real.log h + potential (tangentProbability μ x h) u) := by
  let I := sourceInterval (x-h) (x+h)
  let f : Segment → ℝ := fun t => logProfile (u-(clampSegment (((t : ℝ)-x)/h) : ℝ))
  have he : f =ᵐ[(μ : Measure Segment).restrict I]
      (fun t => logProfile (x+h*u-(t : ℝ))-Real.log h) := by
    filter_upwards [ae_restrict_mem (measurableSet_sourceInterval (x-h) (x+h)),
      ae_restrict_of_ae (ae_source_ne μ hfloor (x+h*u))] with t ht hne
    dsimp only [f]
    rw [clamp_rescale_coe x h hh t ht]
    have hl := logProfile_affine x h u t hh hne
    linarith
  have hf : Integrable f ((μ : Measure Segment).restrict I) :=
    ((hi.restrict (s := I)).sub (integrable_const _)).congr he.symm
  have hnorm := integral_tangentProbability μ x h hm
    (fun t : Segment => logProfile (u-(t : ℝ))) (by unfold logProfile; fun_prop)
  change potential (tangentProbability μ x h) u = (∫ t in I,f t ∂(μ : Measure Segment)) /
    localMass μ x h at hnorm
  rw [integral_congr_ae he,integral_sub (hi.restrict (s := I)) (integrable_const _)] at hnorm
  simp only [integral_const,measureReal_restrict_apply_univ,smul_eq_mul] at hnorm
  change potential (tangentProbability μ x h) u =
    ((∫ t in I,logProfile (x+h*u-(t : ℝ)) ∂(μ : Measure Segment))-
      localMass μ x h*Real.log h)/localMass μ x h at hnorm
  have hmneq := hm.ne'
  have heq := (eq_div_iff hmneq).mp hnorm
  dsimp only [I] at heq
  nlinarith

/-- Actual inner/outer decomposition. No pointwise convergence of the local
potential at zero is assumed: that term is canceled at two sample points later. -/
theorem inner_outer_potential_identity (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x h u : ℝ)
    (hh : 0 < h) (hu : |u| < 1) (hm : 0 < localMass μ x h)
    (hi0 : Integrable (fun t : Segment => logProfile (x-(t : ℝ))) (μ : Measure Segment))
    (hiu : Integrable (fun t : Segment => logProfile (x+h*u-(t : ℝ))) (μ : Measure Segment)) :
    potential μ (x+h*u)-potential μ x = localMass μ x h *
      (potential (tangentProbability μ x h) u -
        potential (tangentProbability μ x h) 0-limitFieldJet μ 0 x h u) := by
  let I := sourceInterval (x-h) (x+h)
  have hI : MeasurableSet I := measurableSet_sourceInterval _ _
  have h0 := local_log_integral μ hfloor x h 0 hh hm (by simpa using hi0)
  have hu' := local_log_integral μ hfloor x h u hh hm hiu
  have hs0 := integral_add_compl hI hi0
  have hsu := integral_add_compl hI hiu
  have hf : localMass μ x h*limitFieldJet μ 0 x h u =
      -(∫ t in Iᶜ,logProfile (x+h*u-(t : ℝ)) ∂(μ : Measure Segment))+
        ∫ t in Iᶜ,logProfile (x-(t : ℝ)) ∂(μ : Measure Segment) := by
    unfold limitFieldJet
    have hc (v : ℝ) : localMass μ x h * (v / localMass μ x h) = v := by
      field_simp [hm.ne']
    change localMass μ x h *
      ((∫ t in Iᶜ, rawFieldJet 0 x h u (t : ℝ) ∂(μ : Measure Segment)) /
        localMass μ x h) = _
    rw [hc]
    have hraw : (fun t : Segment => rawFieldJet 0 x h u (t : ℝ)) =
        (fun t : Segment => -(logProfile (x+h*u-(t : ℝ))-logProfile (x-(t : ℝ)))) := by
      funext t
      simp only [rawFieldJet,Fin.isValue,ite_true,logProfile,Real.log_abs]
    rw [hraw]
    change (∫ t in Iᶜ,-(logProfile (x+h*u-(t : ℝ))-logProfile (x-(t : ℝ)))
      ∂(μ : Measure Segment)) = _
    rw [integral_neg,integral_sub (hiu.restrict (s := Iᶜ)) (hi0.restrict (s := Iᶜ))]
    ring
  simp only [mul_zero,add_zero] at h0
  unfold potential
  change _ = localMass μ x h *
    ((∫ t,logProfile (u-(t : ℝ)) ∂(tangentProbability μ x h : Measure Segment))-
      (∫ t,logProfile (0-(t : ℝ)) ∂(tangentProbability μ x h : Measure Segment))-
      limitFieldJet μ 0 x h u)
  dsimp only [I] at hs0 hsu hf
  unfold potential at h0 hu'
  nlinarith

/-- AE statements on the real line may be pulled through the nondegenerate
local affine coordinate. This is used only for null exceptional sets. -/
theorem ae_affine {P : ℝ → Prop} (hP : ∀ᵐ z ∂volume,P z)
    (x h : ℝ) (hh : h ≠ 0) : ∀ᵐ u ∂volume,P (x+h*u) := by
  have hadd := (measurePreserving_add_left (volume : Measure ℝ) x).quasiMeasurePreserving
  have hmul := Measure.quasiMeasurePreserving_smul (volume : Measure ℝ) hh
  simpa only [smul_eq_mul,Function.comp_apply] using (hadd.comp hmul).ae hP

end Erdos1152.V5
