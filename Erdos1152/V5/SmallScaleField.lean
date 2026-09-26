import Erdos1152.V5.MinimumSamples
import Erdos1152.V5.AnnulusLimit

/-!
# Actual small-scale C² external-field limit

This file combines the fixed-annulus limit, the true remote tail, and two
minimum-level L¹-good samples.  The residual derivative at zero is proved
to tend to zero rather than silently discarded.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V5
open V4

/-- All three actual jets converge, uniformly on every compact subinterval
of (-1,1), for almost every point outside the actual high-potential cover.
The source measure, not a collection of analytic hypotheses, is the only
input.  The conclusion is about h -> 0, not about rows at fixed h. -/
theorem ae_minimum_small_scale_field (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure,x ∉ highPotentialRegion μ →
      ∀ b,0 < b → b < 1 → ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
        0 < localMass μ x h ∧
        ∀ j : Fin 3,∀ u,|u| ≤ b → |limitFieldJet μ j x h u-modelJet j u| < ε := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_minimum_samples μ,
    ae_minimum_second_small_scale μ,ae_positive_CDF_derivative_on_minimum μ]
    with x hxseg hsample hsecond hder
  intro hnot b hb0 hb1 ε hε
  have hfloor : potentialFloor μ ≠ ⊥ := by
    intro hbot
    exact hnot (by rw [highPotentialRegion_of_floor_bot μ hbot]; exact hxseg)
  obtain ⟨hxM,hsample'⟩ := hsample hnot
  obtain ⟨hd,hw⟩ := hder hnot
  have hmass : ∀ᶠ h : ℝ in 𝓝[>] 0,0 < localMass μ x h :=
    (eventually_local_mass_and_central_fraction μ hfloor x (sourceDensity μ x)
      hw hd 1 (by norm_num)).mono (fun _ hh => hh.1)
  let B := max b (1/2 : ℝ)
  have hB0 : 0 < B := hb0.trans_le (le_max_left _ _)
  have hB1 : B < 1 := max_lt hb1 (by norm_num)
  have hbB : b ≤ B := le_max_left _ _
  have hhalf : (1/2 : ℝ) ≤ B := le_max_right _ _
  have hBsq : B^2 ≤ 1 := by nlinarith
  let δ := ε/64
  have hδ : 0 < δ := div_pos hε (by norm_num)
  have hδε : 64*δ=ε := by dsimp [δ]; ring
  filter_upwards [self_mem_nhdsWithin,hmass,
    hsecond hnot B hB0 hB1 δ hδ,hsample' δ hδ]
    with h hh hm hs hsam
  obtain ⟨u,hu,v,hv,huM,hvM,huL,hvL⟩ := hsam
  have hub : |u| ≤ B := by apply abs_le.mpr; constructor <;> linarith [hu.1,hu.2]
  have hvb : |v| ≤ B := by apply abs_le.mpr; constructor <;> linarith [hv.1,hv.2]
  have hu1 : |u| < 1 := hub.trans_lt hB1
  have hv1 : |v| < 1 := hvb.trans_lt hB1
  have haff := field_affine_error μ x h B δ hh hB0.le hB1 hδ.le
    (fun z hz => (hs z hz).le)
  have heu : |affineRemainder μ x h u| ≤ δ :=
    (haff.2 u hub).trans (by nlinarith)
  have hev : |affineRemainder μ x h v| ≤ δ :=
    (haff.2 v hvb).trans (by nlinarith)
  have heq := minimum_sample_slope_identity μ hfloor x h u v hh hu1 hv1 hm hxM.2.2
    huM.2.2 hvM.2.2 (huM.2.1.trans hvM.2.1.symm)
  have hβ := slope_bound_two_samples (affineSlope μ x h) u v
    (affineRemainder μ x h u) (affineRemainder μ x h v)
    (potential (tangentProbability μ x h) u-(externalField u-1))
    (potential (tangentProbability μ x h) v-(externalField v-1)) δ δ (1/4)
    (by norm_num) (by linarith [hu.2,hv.1]) hδ.le hδ.le heu hev huL.le hvL.le heq
  have hβ' : |affineSlope μ x h| ≤ 16*δ := by linarith
  refine ⟨hm,?_⟩
  intro j z hz
  have hzB : |z| ≤ B := hz.trans hbB
  have hz1 : |z| ≤ 1 := hzB.trans hB1.le
  fin_cases j
  · change |limitFieldJet μ 0 x h z-externalField z| < ε
    have he : limitFieldJet μ 0 x h z-externalField z =
        affineRemainder μ x h z+affineSlope μ x h*z := by unfold affineRemainder; ring
    rw [he]
    have htri := abs_add_le (affineRemainder μ x h z) (affineSlope μ x h*z)
    rw [abs_mul] at htri
    have hez : |affineRemainder μ x h z| ≤ δ :=
      (haff.2 z hzB).trans (by nlinarith)
    have hbz : |affineSlope μ x h| * |z| ≤ 16*δ := by
      exact (mul_le_mul_of_nonneg_left hz1 (abs_nonneg _)).trans (by simpa using hβ')
    linarith
  · change |limitFieldJet μ 1 x h z-Real.artanh z| < ε
    have htri := abs_add_le
      (limitFieldJet μ 1 x h z-Real.artanh z-affineSlope μ x h) (affineSlope μ x h)
    have hez := haff.1 z hzB
    have he : limitFieldJet μ 1 x h z-Real.artanh z-affineSlope μ x h+affineSlope μ x h =
        limitFieldJet μ 1 x h z-Real.artanh z := by ring
    rw [he] at htri
    nlinarith
  · change |limitFieldJet μ 2 x h z-1/(1-z^2)| < ε
    exact (hs z hzB).trans (by linarith)

/-- The original three named functions, for users of the old interface who
do not need the finite jet index. -/
theorem ae_minimum_C2_model (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure,x ∉ highPotentialRegion μ →
      ∀ b,0 < b → b < 1 → ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
        0 < localMass μ x h ∧ ∀ u,|u| ≤ b →
          |limitFieldJet μ 0 x h u-externalField u| < ε ∧
          |limitFieldJet μ 1 x h u-Real.artanh u| < ε ∧
          |limitFieldJet μ 2 x h u-1/(1-u^2)| < ε := by
  filter_upwards [ae_minimum_small_scale_field μ] with x hx
  intro hn b hb0 hb1 ε hε
  filter_upwards [hx hn b hb0 hb1 ε hε] with h hh
  exact ⟨hh.1,fun u hu => ⟨hh.2 0 u hu,hh.2 1 u hu,hh.2 2 u hu⟩⟩

end Erdos1152.V5
