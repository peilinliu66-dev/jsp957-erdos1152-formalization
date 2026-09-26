import Erdos1152.V3.WeakKernel
import Erdos1152.V3.AnalyticCardinal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Group.Integral

/-!
# The actual logarithmic potential and its L¹ continuity under weak convergence

The diagonal uses Lean's real logarithm only inside Lebesgue integrals.  The
uniform domination below explicitly discards the Lebesgue-null point zero;
it does not identify `Real.log 0` with negative infinity.

No L¹-convergence hypothesis is introduced.  The proof is by one-source
translation domination, product integrability, Fubini, and a fixed truncation
followed by weak convergence.  This is candidate source pending compilation.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable abbrev baseMeasure : Measure ℝ := volume.restrict Segment
abbrev masterInterval : Set ℝ := Icc (-2 : ℝ) 2

noncomputable def cutoff (k : ℕ) : ℝ := (k + 1 : ℝ)⁻¹
noncomputable def logProfile (u : ℝ) : ℝ := Real.log |u|
noncomputable def truncProfile (k : ℕ) (u : ℝ) : ℝ :=
  Real.log (max (cutoff k) |u|)
noncomputable def truncationError (k : ℕ) (u : ℝ) : ℝ :=
  |truncProfile k u - logProfile u|
noncomputable def errorMass (k : ℕ) : ℝ :=
  ∫ u in masterInterval, truncationError k u
noncomputable def logMass : ℝ := ∫ u in masterInterval, |logProfile u|

theorem cutoff_pos (k : ℕ) : 0 < cutoff k := by
  unfold cutoff
  positivity

theorem cutoff_le_one (k : ℕ) : cutoff k ≤ 1 := by
  unfold cutoff
  apply inv_le_one_of_one_le₀
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem cutoff_tendsto_zero : Tendsto cutoff atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (fun n : ℕ => by linarith) hn

theorem measurable_logProfile : Measurable logProfile := by
  unfold logProfile
  fun_prop

theorem continuous_truncProfile (k : ℕ) : Continuous (truncProfile k) := by
  unfold truncProfile
  exact (continuous_const.max continuous_abs).log
    (fun u => (lt_of_lt_of_le (cutoff_pos k) (le_max_left _ _)).ne')

theorem logProfile_integrable : IntegrableOn logProfile masterInterval := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le
    (by norm_num : (-2 : ℝ) ≤ 2)).mp
  change IntervalIntegrable (fun u => Real.log |u|) volume (-2) 2
  simpa only [Real.log_abs] using
    (intervalIntegral.intervalIntegrable_log' : IntervalIntegrable Real.log volume (-2) 2)

theorem truncProfile_integrable (k : ℕ) :
    IntegrableOn (truncProfile k) masterInterval :=
  (continuous_truncProfile k).continuousOn.integrableOn_compact isCompact_Icc

theorem truncationError_integrable (k : ℕ) :
    IntegrableOn (truncationError k) masterInterval :=
  ((truncProfile_integrable k).sub logProfile_integrable).abs

theorem truncationError_nonneg (k : ℕ) (u : ℝ) :
    0 ≤ truncationError k u := abs_nonneg _

theorem errorMass_nonneg (k : ℕ) : 0 ≤ errorMass k :=
  integral_nonneg (truncationError_nonneg k)

theorem logMass_nonneg : 0 ≤ logMass :=
  integral_nonneg (fun _ => abs_nonneg _)

/-- Domination is only claimed off the diagonal, where the true logarithm is finite. -/
theorem truncationError_le_log (k : ℕ) (u : ℝ) (hu : u ≠ 0) :
    truncationError k u ≤ |logProfile u| := by
  by_cases hh : cutoff k ≤ |u|
  · simp [truncationError, truncProfile, logProfile, max_eq_right hh]
  · have hsmall : |u| ≤ cutoff k := le_of_lt (lt_of_not_ge hh)
    have hlow := Real.log_le_log (abs_pos.mpr hu) hsmall
    have htop := Real.log_nonpos (cutoff_pos k).le (cutoff_le_one k)
    have hu1 : |u| ≤ 1 := hsmall.trans (cutoff_le_one k)
    have hlog := Real.log_nonpos (abs_nonneg u) hu1
    simp only [truncationError, truncProfile, logProfile, max_eq_left hsmall]
    rw [abs_of_nonneg (sub_nonneg.mpr hlow), abs_of_nonpos hlog]
    linarith

theorem truncationError_tendsto_zero (u : ℝ) (hu : u ≠ 0) :
    Tendsto (fun k => truncationError k u) atTop (𝓝 0) := by
  have he := cutoff_tendsto_zero.eventually (gt_mem_nhds (abs_pos.mpr hu))
  have hz : ∀ᶠ k : ℕ in atTop, truncationError k u = 0 := by
    filter_upwards [he] with k hk
    simp [truncationError, truncProfile, logProfile, max_eq_right hk.le]
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm hz) tendsto_const_nhds

/-- A single error function controls every translated source, and its mass tends to zero. -/
theorem errorMass_tendsto_zero : Tendsto errorMass atTop (𝓝 0) := by
  have hneq : ∀ᵐ u ∂volume.restrict masterInterval, u ≠ (0 : ℝ) :=
    ae_restrict_of_ae (volume.ae_ne 0)
  have hlim : ∀ᵐ u ∂volume.restrict masterInterval,
      Tendsto (fun k => truncationError k u) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hneq] with u hu
    exact truncationError_tendsto_zero u hu
  have hbound (k : ℕ) : ∀ᵐ u ∂volume.restrict masterInterval,
      ‖truncationError k u‖ ≤ |logProfile u| := by
    filter_upwards [hneq] with u hu
    simpa only [Real.norm_eq_abs, abs_of_nonneg (truncationError_nonneg k u)]
      using truncationError_le_log k u hu
  change Tendsto (fun k => ∫ u in masterInterval, truncationError k u) atTop (𝓝 0)
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence (fun u => |logProfile u|)
      (fun k => (truncationError_integrable k).aestronglyMeasurable)
      logProfile_integrable.abs hbound hlim

/-- Translation does not increase a nonnegative profile's mass when restricted
from [-2,2] to [-1,1] with a source in [-1,1]. -/
theorem shifted_profile_bound (f : ℝ → ℝ)
    (hf : IntegrableOn f masterInterval) (hf0 : ∀ u, 0 ≤ f u)
    (t : Segment) :
    Integrable (fun x : ℝ => f (x - (t : ℝ))) baseMeasure ∧
      (∫ x, f (x - (t : ℝ)) ∂baseMeasure) ≤ ∫ u in masterInterval, f u := by
  let F : ℝ → ℝ := masterInterval.indicator f
  have hF : Integrable F volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hf
  have hFt : Integrable (fun x : ℝ => F (x - (t : ℝ))) volume := hF.comp_sub_right t
  have hmem (x : ℝ) (hx : x ∈ Segment) : x - (t : ℝ) ∈ masterInterval := by
    constructor <;> linarith [hx.1, hx.2, t.property.1, t.property.2]
  have heq : (fun x : ℝ => f (x - (t : ℝ))) =ᵐ[baseMeasure]
      fun x => F (x - (t : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact (Set.indicator_of_mem (hmem x hx) f).symm
  have hft : Integrable (fun x : ℝ => f (x - (t : ℝ))) baseMeasure :=
    hFt.integrableOn.congr heq.symm
  refine ⟨hft, ?_⟩
  have hI : Integrable (Segment.indicator (fun x : ℝ => f (x - (t : ℝ)))) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr hft
  have hF0 (x : ℝ) : 0 ≤ F x := by
    by_cases hx : x ∈ masterInterval
    · simpa only [F, Set.indicator_of_mem hx] using hf0 x
    · simp only [F, Set.indicator_of_notMem hx, le_refl]
  have hle (x : ℝ) : Segment.indicator (fun x : ℝ => f (x - (t : ℝ))) x ≤
      F (x - (t : ℝ)) := by
    by_cases hx : x ∈ Segment
    · simp only [Set.indicator_of_mem hx, F, Set.indicator_of_mem (hmem x hx), le_refl]
    · simpa only [Set.indicator_of_notMem hx] using hF0 (x - (t : ℝ))
  calc
    _ = ∫ x, Segment.indicator (fun x : ℝ => f (x - (t : ℝ))) x :=
      (integral_indicator measurableSet_Icc).symm
    _ ≤ ∫ x, F (x - (t : ℝ)) := integral_mono hI hFt hle
    _ = ∫ u in masterInterval, f u := by
      rw [integral_sub_right_eq_self, integral_indicator measurableSet_Icc]

/-- Product integrability is derived from one-source bounds, not postulated. -/
theorem shifted_profile_integrable_product
    (μ : ProbabilityMeasure Segment) (f : ℝ → ℝ)
    (hm : Measurable f) (hi : IntegrableOn f masterInterval) :
    Integrable (fun p : ℝ × Segment => f (p.1 - (p.2 : ℝ)))
      (baseMeasure.prod (μ : Measure Segment)) := by
  have hmeas : Measurable (fun p : ℝ × Segment => f (p.1 - (p.2 : ℝ))) := by
    exact hm.comp (measurable_fst.sub (measurable_subtype_coe.comp measurable_snd))
  have hsource (t : Segment) :=
    shifted_profile_bound (fun u => |f u|) hi.abs (fun _ => abs_nonneg _) t
  apply (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with t
    refine (hsource t).1.mono' ?_ ?_
    · exact (hm.comp (measurable_id.sub measurable_const)).aestronglyMeasurable
    · filter_upwards with x
      simp only [Real.norm_eq_abs, le_refl]
  · have hms : AEStronglyMeasurable
        (fun t : Segment => ∫ x, ‖f (x - (t : ℝ))‖ ∂baseMeasure)
        (μ : Measure Segment) :=
      hmeas.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
    apply (integrable_const (∫ u in masterInterval, |f u|)).mono' hms
    filter_upwards with t
    have h0 : 0 ≤ ∫ x, ‖f (x - (t : ℝ))‖ ∂baseMeasure :=
      integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simpa only [Real.norm_eq_abs] using (hsource t).2

noncomputable def potential (μ : ProbabilityMeasure Segment) (x : ℝ) : ℝ :=
  ∫ t : Segment, logProfile (x - (t : ℝ)) ∂(μ : Measure Segment)

noncomputable def truncPotential (μ : ProbabilityMeasure Segment) (k : ℕ) (x : ℝ) : ℝ :=
  ∫ t : Segment, truncProfile k (x - (t : ℝ)) ∂(μ : Measure Segment)

theorem measurable_potential (μ : ProbabilityMeasure Segment) : Measurable (potential μ) := by
  have hm : Measurable (fun p : ℝ × Segment => logProfile (p.1 - (p.2 : ℝ))) := by
    exact measurable_logProfile.comp
      (measurable_fst.sub (measurable_subtype_coe.comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_truncPotential (μ : ProbabilityMeasure Segment) (k : ℕ) :
    Measurable (truncPotential μ k) := by
  have hm : Measurable (fun p : ℝ × Segment => truncProfile k (p.1 - (p.2 : ℝ))) := by
    exact (continuous_truncProfile k).measurable.comp
      (measurable_fst.sub (measurable_subtype_coe.comp measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem log_integrable_product (μ : ProbabilityMeasure Segment) :
    Integrable (fun p : ℝ × Segment => logProfile (p.1 - (p.2 : ℝ)))
      (baseMeasure.prod (μ : Measure Segment)) :=
  shifted_profile_integrable_product μ logProfile measurable_logProfile logProfile_integrable

theorem trunc_integrable_product (μ : ProbabilityMeasure Segment) (k : ℕ) :
    Integrable (fun p : ℝ × Segment => truncProfile k (p.1 - (p.2 : ℝ)))
      (baseMeasure.prod (μ : Measure Segment)) :=
  shifted_profile_integrable_product μ (truncProfile k)
    (continuous_truncProfile k).measurable (truncProfile_integrable k)

theorem integrable_potential (μ : ProbabilityMeasure Segment) :
    Integrable (potential μ) baseMeasure := (log_integrable_product μ).integral_prod_left

theorem integrable_truncPotential (μ : ProbabilityMeasure Segment) (k : ℕ) :
    Integrable (truncPotential μ k) baseMeasure :=
  (trunc_integrable_product μ k).integral_prod_left

/-- An actual uniform truncation bound for every probability measure. -/
theorem potential_truncation_L1 (μ : ProbabilityMeasure Segment) (k : ℕ) :
    (∫ x, |truncPotential μ k x - potential μ x| ∂baseMeasure) ≤ errorMass k := by
  have ht := trunc_integrable_product μ k
  have hl := log_integrable_product μ
  have hd := ht.sub hl
  have hda := hd.abs
  have hpoint : ∀ᵐ x ∂baseMeasure,
      |truncPotential μ k x - potential μ x| ≤
        ∫ t : Segment, |truncProfile k (x - (t : ℝ)) - logProfile (x - (t : ℝ))|
          ∂(μ : Measure Segment) := by
    filter_upwards [ht.prod_right_ae, hl.prod_right_ae] with x htx hlx
    rw [truncPotential, potential, ← integral_sub htx hlx]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm
        (fun t : Segment => truncProfile k (x - (t : ℝ)) - logProfile (x - (t : ℝ))))
  calc
    _ ≤ ∫ x, ∫ t : Segment,
        |truncProfile k (x - (t : ℝ)) - logProfile (x - (t : ℝ))|
          ∂(μ : Measure Segment) ∂baseMeasure :=
      integral_mono_ae ((integrable_truncPotential μ k).sub (integrable_potential μ)).abs
        hda.integral_prod_left hpoint
    _ = ∫ t : Segment, ∫ x,
        |truncProfile k (x - (t : ℝ)) - logProfile (x - (t : ℝ))|
          ∂baseMeasure ∂(μ : Measure Segment) := integral_integral_swap hda
    _ ≤ ∫ _t : Segment, errorMass k ∂(μ : Measure Segment) := by
      apply integral_mono_ae hda.integral_prod_right (integrable_const _)
      filter_upwards with t
      exact (shifted_profile_bound (truncationError k) (truncationError_integrable k)
        (truncationError_nonneg k) t).2
    _ = errorMass k := by simp

@[simp] theorem baseMeasure_mass : baseMeasure.real Set.univ = 2 := by
  norm_num [baseMeasure, Measure.real, Segment, Real.volume_Icc]

/-- Weak convergence of the actual measures gives L¹ convergence of their
actual logarithmic potentials, including atomic and singular measures. -/
theorem weak_convergence_potential_L1
    (μs : ℕ → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n => ∫ x, |potential (μs n) x - potential μ x| ∂baseMeasure)
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ :=
    (errorMass_tendsto_zero.eventually
      (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 8))).exists
  have hu := V3.weak_convergence_uniform_truncated_log μs μ hμ
    (cutoff k) (cutoff_pos k) (ε / 8) (by positivity)
  filter_upwards [hu] with n hn
  have hmid : (∫ x,
      |truncPotential (μs n) k x - truncPotential μ k x| ∂baseMeasure) ≤ 2 * (ε / 8) := by
    calc
      _ ≤ ∫ _x, ε / 8 ∂baseMeasure := by
        apply integral_mono_ae
          ((integrable_truncPotential (μs n) k).sub (integrable_truncPotential μ k)).abs
          (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        change |truncPotential (μs n) k x - truncPotential μ k x| ≤ ε / 8
        simpa only [truncPotential, truncProfile, V3.truncatedLogKernel, sub_zero]
          using (hn (⟨x, hx⟩ : Segment)).le
      _ = 2 * (ε / 8) := by norm_num [integral_const, smul_eq_mul]
  have hleft : (∫ x,
      |potential (μs n) x - truncPotential (μs n) k x| ∂baseMeasure) ≤ errorMass k := by
    simpa only [abs_sub_comm] using potential_truncation_L1 (μs n) k
  have hright := potential_truncation_L1 μ k
  have htri : (∫ x, |potential (μs n) x - potential μ x| ∂baseMeasure) ≤
      (∫ x, |potential (μs n) x - truncPotential (μs n) k x| ∂baseMeasure) +
      (∫ x, |truncPotential (μs n) k x - truncPotential μ k x| ∂baseMeasure) +
      (∫ x, |truncPotential μ k x - potential μ x| ∂baseMeasure) := by
    have h₁ : Integrable (fun x =>
        |potential (μs n) x - truncPotential (μs n) k x|) baseMeasure :=
      ((integrable_potential (μs n)).sub (integrable_truncPotential (μs n) k)).abs
    have h₂ : Integrable (fun x =>
        |truncPotential (μs n) k x - truncPotential μ k x|) baseMeasure :=
      ((integrable_truncPotential (μs n) k).sub (integrable_truncPotential μ k)).abs
    have h₃ : Integrable (fun x =>
        |truncPotential μ k x - potential μ x|) baseMeasure :=
      ((integrable_truncPotential μ k).sub (integrable_potential μ)).abs
    have h₁₂ : Integrable (fun x =>
        |potential (μs n) x - truncPotential (μs n) k x| +
          |truncPotential (μs n) k x - truncPotential μ k x|) baseMeasure := h₁.add h₂
    rw [← integral_add h₁ h₂, ← integral_add h₁₂ h₃]
    apply integral_mono
      ((integrable_potential (μs n)).sub (integrable_potential μ)).abs
      (((((integrable_potential (μs n)).sub (integrable_truncPotential (μs n) k)).abs).add
        (((integrable_truncPotential (μs n) k).sub (integrable_truncPotential μ k)).abs)).add
        (((integrable_truncPotential μ k).sub (integrable_potential μ)).abs))
    intro x
    simp only [Pi.add_apply, Pi.sub_apply]
    have h1 := abs_sub_le (potential (μs n) x) (truncPotential (μs n) k x) (potential μ x)
    have h2 := abs_sub_le (truncPotential (μs n) k x) (truncPotential μ k x) (potential μ x)
    linarith
  have h0 : 0 ≤ ∫ x, |potential (μs n) x - potential μ x| ∂baseMeasure :=
    integral_nonneg (fun _ => abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  linarith

end Erdos1152.V4
