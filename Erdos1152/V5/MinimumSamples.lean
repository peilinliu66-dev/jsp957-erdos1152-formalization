import Erdos1152.V5.AffineControl
import Erdos1152.V4.UniformLocalPotential
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# Two actual minimum-level sample points in separated windows

The level is the single real value associated with the source's finite floor,
not a location-dependent level to which an uncountable intersection of AE
statements would be applied.  Log-section integrability is included in the
measurable level set. Density and the actual tangent L¹ limit produce the
samples simultaneously, before any finite node deletion is chosen.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical Pointwise

namespace Erdos1152.V5
open V4

noncomputable def regularMinimum (μ : ProbabilityMeasure Segment) : Set ℝ :=
  {z | z ∈ Segment ∧ potential μ z=(potentialFloor μ).toReal ∧
    Integrable (fun t : Segment => logProfile (z-(t : ℝ))) (μ : Measure Segment)}

noncomputable def tangentError (μ : ProbabilityMeasure Segment) (x h u : ℝ) : ℝ :=
  |potential (tangentProbability μ x h) u-(externalField u-1)|

theorem measurableSet_regularMinimum (μ : ProbabilityMeasure Segment) :
    MeasurableSet (regularMinimum μ) := by
  have hi : MeasurableSet {z : ℝ |
      Integrable (fun t : Segment => logProfile (z-(t : ℝ))) (μ : Measure Segment)} :=
    measurableSet_integrable (show StronglyMeasurable
      (fun z : ℝ × Segment => logProfile (z.1-(z.2 : ℝ))) from
      (by unfold logProfile; fun_prop : Measurable
        (fun z : ℝ × Segment => logProfile (z.1-(z.2 : ℝ)))).stronglyMeasurable)
  exact measurableSet_Icc.inter ((measurableSet_eq_fun (measurable_potential μ) measurable_const).inter hi)

theorem integrable_tangentError (μ : ProbabilityMeasure Segment) (x h : ℝ) :
    Integrable (tangentError μ x h) baseMeasure := by
  change Integrable (fun u => |potential (tangentProbability μ x h) u-(externalField u-1)|) baseMeasure
  simpa only [Pi.sub_apply,potential_uniformSegment] using
    ((integrable_potential (tangentProbability μ x h)).sub
      (integrable_potential uniformSegmentProbability)).abs

theorem measurable_tangentError (μ : ProbabilityMeasure Segment) (x h : ℝ) :
    Measurable (tangentError μ x h) := by
  change Measurable (fun u => |potential (tangentProbability μ x h) u-(externalField u-1)|)
  simpa only [Function.comp_def,Pi.sub_apply,potential_uniformSegment] using
    continuous_abs.measurable.comp ((measurable_potential (tangentProbability μ x h)).sub
      (measurable_potential uniformSegmentProbability))

/-- Only null source sections are discarded in defining the regular level. -/
theorem ae_remaining_regularMinimum (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure,x ∉ highPotentialRegion μ → x ∈ regularMinimum μ := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (log_integrable_product μ).prod_right_ae,ae_extendedPotential_eq μ,
    ae_compl_high_is_minimum μ] with x hx hi he hm
  intro hnot
  have hfloor : potentialFloor μ=(potential μ x : EReal) := (hm hnot).symm.trans he
  refine ⟨hx,?_,hi⟩
  rw [hfloor]
  simp

/-- Affine pullback of volume, with the original scale displayed. -/
theorem volume_affine_preimage (x h : ℝ) (hh : 0 < h) (E : Set ℝ) :
    volume ((fun u : ℝ => x+h*u) ⁻¹' E)=ENNReal.ofReal h⁻¹*volume E := by
  change volume ((fun u : ℝ => h • u) ⁻¹' ((fun v : ℝ => x+v) ⁻¹' E)) = _
  rw [Measure.addHaar_preimage_smul volume hh.ne',measure_preimage_add]
  simp only [Module.finrank_self,pow_one,abs_inv,abs_of_pos hh]

theorem volume_real_affine_preimage (x h : ℝ) (hh : 0 < h) (E : Set ℝ) :
    volume.real ((fun u : ℝ => x+h*u) ⁻¹' E)=h⁻¹*volume.real E := by
  have he := congrArg ENNReal.toReal (volume_affine_preimage x h hh E)
  simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofReal (inv_pos.mpr hh).le] using he

private theorem affine_image_pointwise (x h : ℝ) (J : Set ℝ) :
    (fun u : ℝ => x+h*u) '' J = {x}+h • J := by
  ext z
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨x,by simp,h*u,⟨u,hu,rfl⟩,rfl⟩
  · rintro ⟨a,ha,b,⟨u,hu,rfl⟩,rfl⟩
    have ha' : a=x := Set.mem_singleton_iff.mp ha
    subst a
    exact ⟨u,hu,rfl⟩

/-- A density-one point gives full limiting mass in each fixed coordinate
window, not just the existence of one minimum point somewhere in a ball. -/
theorem density_window_mass (M : Set ℝ) (x : ℝ)
    (hd : Tendsto (fun h => volume (M ∩ closedBall x h)/volume (closedBall x h))
      (𝓝[>] 0) (𝓝 1)) (a b : ℝ) (hab : a < b) :
    Tendsto (fun h : ℝ => volume.real
      (Ioo a b ∩ (fun u : ℝ => x+h*u) ⁻¹' M)) (𝓝[>] 0) (𝓝 (b-a)) := by
  let J : Set ℝ := Ioo a b
  have hJ : volume J ≠ 0 := by simp [J,Real.volume_Ioo,hab]
  have hJtop : volume J ≠ ∞ := by simp [J,Real.volume_Ioo]
  have hlen : 0 < volume.real J := by simp [J,Real.volume_real_Ioo,hab.le]; linarith
  have h := Measure.tendsto_addHaar_inter_smul_one_of_density_one volume M x hd J
    measurableSet_Ioo hJ hJtop
  have ht := (ENNReal.continuousAt_toReal ENNReal.one_ne_top).tendsto.comp h
  simp only [Function.comp_def,ENNReal.toReal_div,ENNReal.toReal_one] at ht
  have he : ∀ᶠ h : ℝ in 𝓝[>] 0,
      volume.real (J ∩ (fun u : ℝ => x+h*u) ⁻¹' M)/volume.real J =
      volume.real (M ∩ ({x}+h • J))/volume.real ({x}+h • J) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    let f : ℝ → ℝ := fun u => x+h*u
    have hinj : Function.Injective f := by
      intro u v huv
      have hm : h*u=h*v := add_left_cancel huv
      exact mul_left_cancel₀ hh.ne' hm
    have hpreJ : f ⁻¹' (f '' J)=J := Set.preimage_image_eq J hinj
    have hpre : f ⁻¹' (M ∩ f '' J)=J ∩ f ⁻¹' M := by
      rw [Set.preimage_inter,hpreJ,Set.inter_comm]
    have hmeas := volume_real_affine_preimage x h hh (M ∩ f '' J)
    have hjmeas := volume_real_affine_preimage x h hh (f '' J)
    change volume.real (f ⁻¹' (M ∩ f '' J))=h⁻¹*volume.real (M ∩ f '' J) at hmeas
    change volume.real (f ⁻¹' (f '' J))=h⁻¹*volume.real (f '' J) at hjmeas
    rw [hpre] at hmeas
    rw [hpreJ] at hjmeas
    rw [hmeas,hjmeas,mul_div_mul_left _ _ (inv_ne_zero hh.ne')]
    simp only [f,affine_image_pointwise]
  have hc : Tendsto (fun h : ℝ => volume.real (J ∩ (fun u : ℝ => x+h*u) ⁻¹' M)/volume.real J)
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := ht.congr' (he.mono fun _ hh => hh.symm)
  have hc' := hc.mul_const (volume.real J)
  simp only [div_mul_cancel₀ _ hlen.ne',one_mul] at hc'
  simpa [J,Real.volume_real_Ioo,hab.le] using hc'

/-- The integration argument producing a good point includes the measure
budget; no supremum or quotient norm is substituted for this step. -/
private theorem exists_error_small (μ : ProbabilityMeasure Segment) (x h τ : ℝ)
    (hτ : 0 < τ) (E : Set ℝ) (hE : MeasurableSet E) (hES : E ⊆ Segment)
    (hbudget : (∫ u,tangentError μ x h u ∂baseMeasure) < τ*volume.real E) :
    ∃ u ∈ E,tangentError μ x h u < τ := by
  by_contra! hn
  have hle : ∀ u : ℝ,E.indicator (fun _ => τ) u ≤ tangentError μ x h u := by
    intro u
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu]
      exact hn u hu
    · rw [Set.indicator_of_notMem hu]
      exact abs_nonneg _
  have hint := integral_mono_ae ((integrable_const τ).indicator hE)
    (integrable_tangentError μ x h) (Filter.Eventually.of_forall hle)
  rw [integral_indicator hE,integral_const] at hint
  have hreal : baseMeasure.real E=volume.real E := by
    rw [Measure.real,Measure.restrict_apply hE,Set.inter_eq_left.mpr hES]
    rfl
  simp only [measureReal_restrict_apply_univ,smul_eq_mul] at hint
  rw [hreal] at hint
  nlinarith

/-- Quantitative L¹ good points in each separated minimum-level window. -/
theorem minimum_samples (μ : ProbabilityMeasure Segment) (x : ℝ)
    (hd : Tendsto (fun h => volume (regularMinimum μ ∩ closedBall x h)/volume (closedBall x h))
      (𝓝[>] 0) (𝓝 1))
    (hL : Tendsto (fun h : ℝ => ∫ u,tangentError μ x h u ∂baseMeasure)
      (𝓝[>] 0) (𝓝 0)) :
    ∀ τ > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
      ∃ u ∈ Ioo (-1/4 : ℝ) (-1/8), ∃ v ∈ Ioo (1/8 : ℝ) (1/4),
        x+h*u ∈ regularMinimum μ ∧ x+h*v ∈ regularMinimum μ ∧
        tangentError μ x h u < τ ∧ tangentError μ x h v < τ := by
  intro τ hτ
  have hl := density_window_mass (regularMinimum μ) x hd (-1/4) (-1/8) (by norm_num)
  have hr := density_window_mass (regularMinimum μ) x hd (1/8) (1/4) (by norm_num)
  have hle := hl.eventually (lt_mem_nhds (by norm_num : (1/16 : ℝ)< -1/8-(-1/4)))
  have hre := hr.eventually (lt_mem_nhds (by norm_num : (1/16 : ℝ)< 1/4-1/8))
  have he := hL.eventually (gt_mem_nhds (div_pos hτ (by norm_num : (0 : ℝ)<16)))
  filter_upwards [hle,hre,he] with h hlh hrh heh
  let Eminus := Ioo (-1/4 : ℝ) (-1/8) ∩ (fun u : ℝ => x+h*u) ⁻¹' regularMinimum μ
  let Eplus := Ioo (1/8 : ℝ) (1/4) ∩ (fun u : ℝ => x+h*u) ⁻¹' regularMinimum μ
  change (1/16 : ℝ) < volume.real Eminus at hlh
  change (1/16 : ℝ) < volume.real Eplus at hrh
  have hm : MeasurableSet ((fun u : ℝ => x+h*u) ⁻¹' regularMinimum μ) :=
    (measurableSet_regularMinimum μ).preimage (by fun_prop)
  have hEL : Eminus ⊆ Segment := by intro u hu; constructor <;> linarith [hu.1.1,hu.1.2]
  have hER : Eplus ⊆ Segment := by intro u hu; constructor <;> linarith [hu.1.1,hu.1.2]
  obtain ⟨u,hu,heu⟩ := exists_error_small μ x h τ hτ Eminus (measurableSet_Ioo.inter hm) hEL
    (by change (∫u,tangentError μ x h u ∂baseMeasure)<τ*volume.real Eminus; nlinarith)
  obtain ⟨v,hv,hev⟩ := exists_error_small μ x h τ hτ Eplus (measurableSet_Ioo.inter hm) hER
    (by change (∫u,tangentError μ x h u ∂baseMeasure)<τ*volume.real Eplus; nlinarith)
  exact ⟨u,hu.1,v,hv.1,hu.2,hv.2,heu,hev⟩

/-- Public sample theorem for the actual minimum region. Its density and L¹
hypotheses are both supplied internally. -/
theorem ae_minimum_samples (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure,x ∉ highPotentialRegion μ →
      x ∈ regularMinimum μ ∧
      ∀ τ > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∃ u ∈ Ioo (-1/4 : ℝ) (-1/8), ∃ v ∈ Ioo (1/8 : ℝ) (1/4),
          x+h*u ∈ regularMinimum μ ∧ x+h*v ∈ regularMinimum μ ∧
          tangentError μ x h u < τ ∧ tangentError μ x h v < τ := by
  filter_upwards [ae_remaining_regularMinimum μ,ae_minimum_tangent_potential_L1_model μ,
    ae_restrict_of_ae (Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
      (measurableSet_regularMinimum μ))] with x hmin hL hd
  intro hnot
  have hx := hmin hnot
  have hd' : Tendsto (fun h => volume (regularMinimum μ ∩ closedBall x h)/volume (closedBall x h))
      (𝓝[>] 0) (𝓝 1) := by simpa only [Set.indicator_of_mem hx,Pi.one_apply] using hd
  exact ⟨hx,minimum_samples μ x hd' (hL hnot)⟩

end Erdos1152.V5
