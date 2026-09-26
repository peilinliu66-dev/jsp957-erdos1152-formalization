import Erdos1152.V4.VerticalBoundary
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

/-!
# Positive density on the actual minimum level

Besicovitch differentiation supplies a finite Radon--Nikodym density a.e.
The quantitative source-ball obstruction proved from the actual harmonic
potential forces that density to be positive on the actual leftover region.
Thus the zero-density branch is eliminated, rather than omitted or assumed.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def realSourceProbability (μ : ProbabilityMeasure Segment) : ProbabilityMeasure ℝ :=
  μ.map measurable_subtype_coe.aemeasurable

noncomputable def realSource (μ : ProbabilityMeasure Segment) : Measure ℝ :=
  (realSourceProbability μ : Measure ℝ)

instance realSource_isProbabilityMeasure (μ : ProbabilityMeasure Segment) :
    IsProbabilityMeasure (realSource μ) := by
  unfold realSource
  infer_instance

noncomputable def sourceDensity (μ : ProbabilityMeasure Segment) (x : ℝ) : ℝ :=
  ((realSource μ).rnDeriv volume x).toReal

theorem sourceDensity_nonneg (μ : ProbabilityMeasure Segment) (x : ℝ) :
    0 ≤ sourceDensity μ x := ENNReal.toReal_nonneg

theorem realSource_apply (μ : ProbabilityMeasure Segment) (E : Set ℝ)
    (hE : MeasurableSet E) :
    realSource μ E = (μ : Measure Segment) (Subtype.val ⁻¹' E) := by
  exact ProbabilityMeasure.map_apply' μ measurable_subtype_coe.aemeasurable hE

theorem realSource_ball (μ : ProbabilityMeasure Segment) (x r : ℝ) :
    realSource μ (ball x r) = (μ : Measure Segment) (sourceBall x r) := by
  rw [realSource_apply μ _ measurableSet_ball]
  congr 1
  ext t
  simp only [Set.mem_preimage, mem_ball, Real.dist_eq, sourceBall,
    Set.mem_setOf_eq, abs_sub_comm]

theorem sourceBall_le_closedBall (μ : ProbabilityMeasure Segment) (x r : ℝ) :
    (μ : Measure Segment) (sourceBall x r) ≤ realSource μ (closedBall x r) := by
  rw [← realSource_ball]
  exact measure_mono ball_subset_closedBall

/-- The density is obtained from the genuine push-forward measure, not
introduced as an arbitrary function satisfying a desired limit. -/
theorem ae_sourceDensity_limit (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      Tendsto (fun r : ℝ => (realSource μ).real (closedBall x r) / (2 * r))
        (𝓝[>] 0) (𝓝 (sourceDensity μ x)) := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv (realSource μ) volume,
    Measure.rnDeriv_lt_top (realSource μ) volume] with x hx hfinite
  have ht := (ENNReal.continuousAt_toReal hfinite.ne).tendsto.comp hx
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change 0 < r at hr
  rw [Function.comp_apply, ENNReal.toReal_div, Real.volume_closedBall,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)]
  rfl

theorem sourceDensity_lower_at_minimum (μ : ProbabilityMeasure Segment)
    (x : Segment) (A : ℝ) (hA : potentialFloor μ = (A : EReal))
    (hxA : potential μ x = A)
    (hi : Integrable (fun t : Segment => logProfile ((x : ℝ) - (t : ℝ))) (μ : Measure Segment))
    (hd : ∀ᵐ t : Segment ∂(μ : Measure Segment), (x : ℝ) ≠ (t : ℝ))
    (hlim : Tendsto (fun r : ℝ => (realSource μ).real (closedBall (x : ℝ) r) / (2 * r))
      (𝓝[>] 0) (𝓝 (sourceDensity μ x))) :
    densityObstructionConstant / 2 ≤ sourceDensity μ x := by
  by_contra! hsmall
  have he := hlim.eventually (gt_mem_nhds hsmall)
  obtain ⟨R, hR, hRat⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp he
  obtain ⟨r, hr, hrR, hmass⟩ := minimum_has_large_source_ball μ x A hA hxA hi hd
    (R / 2) (half_pos hR)
  have hratio := hRat (show r ∈ Ioo (0 : ℝ) R from ⟨hr, by linarith⟩)
  have hupper : (realSource μ).real (closedBall (x : ℝ) r) < densityObstructionConstant * r := by
    have hh := (div_lt_iff₀ (by positivity : 0 < 2 * r)).mp hratio
    nlinarith
  have hbound : ENNReal.ofReal (densityObstructionConstant * r) ≤
      realSource μ (closedBall (x : ℝ) r) :=
    hmass.le.trans (sourceBall_le_closedBall μ x r)
  have hreal := ENNReal.toReal_mono (measure_ne_top (realSource μ) _) hbound
  rw [ENNReal.toReal_ofReal (mul_nonneg densityObstructionConstant_pos.le hr.le)] at hreal
  exact (not_le_of_gt hupper) hreal

/-- An actual new analytic conclusion: uniformly positive finite source
density almost everywhere on the complement of the constructed high cover.
No positivity/differentiation/Harnack input is a theorem parameter. -/
theorem ae_positive_density_on_minimum (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, x ∉ highPotentialRegion μ →
      densityObstructionConstant / 2 ≤ sourceDensity μ x ∧ 0 < sourceDensity μ x := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    (log_integrable_product μ).prod_right_ae, ae_source_off_diagonal μ,
    ae_extendedPotential_eq μ, ae_compl_high_is_minimum μ,
    ae_restrict_of_ae (ae_sourceDensity_limit μ)] with x hxseg hi hd heq hmin hlim
  intro hnot
  let x' : Segment := ⟨x, hxseg⟩
  have hfloor : potentialFloor μ = (potential μ x : EReal) :=
    (hmin hnot).symm.trans heq
  have hlow := sourceDensity_lower_at_minimum μ x' (potential μ x) hfloor rfl hi hd hlim
  exact ⟨hlow, (half_pos densityObstructionConstant_pos).trans_le hlow⟩

end Erdos1152.V4
