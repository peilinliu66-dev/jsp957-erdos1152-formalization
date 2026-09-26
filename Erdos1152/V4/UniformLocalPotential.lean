import Erdos1152.V4.TangentMeasure
import Erdos1152.ExternalField

/-!
# Identify the actual tangent-potential limit with the model external field

The limiting probability is not merely an abstract compactness limit.
It is the normalized uniform measure, and its logarithmic potential is
exactly the existing model `externalField - 1`. The last theorem gives the
actual L¹ limit needed for the two-point affine-term cancellation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

/-- Exact integration against the uniform probability mapped to Segment. -/
theorem integral_uniformSegment (f : Segment → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(uniformSegmentProbability : Measure Segment)) =
      (1/2 : ℝ) * ∫ t, f (clampSegment t) ∂baseMeasure := by
  rw [uniformSegmentProbability, ProbabilityMeasure.toMeasure_map,
    integral_map_of_stronglyMeasurable continuous_clampSegment.measurable hf.stronglyMeasurable]
  change (∫ t, f (clampSegment t) ∂(ENNReal.ofReal (1/2 : ℝ) • baseMeasure)) = _
  rw [integral_smul_measure]
  norm_num [smul_eq_mul]

/-- Identify the limit with the explicit model, using the original upstream
integral calculation rather than assuming a model-potential limit. -/
theorem potential_uniformSegment (u : ℝ) :
    potential uniformSegmentProbability u = externalField u-1 := by
  unfold potential
  rw [integral_uniformSegment (fun t : Segment => logProfile (u-(t : ℝ)))
    (by unfold logProfile; fun_prop)]
  have he : (∫ t, logProfile (u-(clampSegment t : ℝ)) ∂baseMeasure) =
      ∫ t, logProfile (u-t) ∂baseMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simp only [clampSegment, Set.projIcc_of_mem _ ht, Subtype.coe_mk]
  rw [he]
  change (1/2 : ℝ) * (∫ t in Icc (-1 : ℝ) 1, Real.log |u-t|) = externalField u-1
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
  calc
    _ = uniformPotential u := by unfold uniformPotential; ring
    _ = externalField u-1 := uniformPotential_eq u

/-- The h→0 logarithmic-potential limit is now the exact model Q−1. -/
theorem tangent_potential_L1_model (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w : ℝ) (hw : 0 < w)
    (hx : HasDerivAt (sourceCDF μ) w x) :
    Tendsto (fun h : ℝ => ∫ u,
      |potential (tangentProbability μ x h) u-(externalField u-1)| ∂baseMeasure)
      (𝓝[>] 0) (𝓝 0) := by
  simpa only [potential_uniformSegment] using tangent_potential_L1 μ hfloor x w hw hx

/-- Public actual-source statement, with the derivative and the weak limit
both supplied internally on the true remaining minimum region. -/
theorem ae_minimum_tangent_potential_L1_model (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, x ∉ highPotentialRegion μ →
      Tendsto (fun h : ℝ => ∫ u,
        |potential (tangentProbability μ x h) u-(externalField u-1)| ∂baseMeasure)
        (𝓝[>] 0) (𝓝 0) := by
  simpa only [potential_uniformSegment] using ae_minimum_tangent_potential_L1 μ

end Erdos1152.V4
