import Erdos1152.V3.LogKernel
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Weak convergence of compactly parameterized kernels

Uniform convergence is obtained by a finite cover; it is not passed as an
assumption. The empirical row uses all original n+1 nodes. No minimum-potential
or cardinal-growth conclusion is postulated here. Build status is recorded by the canonical driver.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V3

private theorem kernel_section_integrable
    (f : Segment × Segment → ℝ) (hf : Continuous f)
    (x : Segment) (μ : ProbabilityMeasure Segment) :
    Integrable (fun t => f (x, t)) (μ : Measure Segment) := by
  have hc : Continuous (fun t : Segment => f (x, t)) :=
    hf.comp (continuous_const.prodMk continuous_id)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- A modulus for the kernel is also a modulus for integration against every
probability measure, with no absolute-continuity assumption. -/
theorem integral_kernel_difference_le
    (f : Segment × Segment → ℝ) (hf : Continuous f)
    (μ : ProbabilityMeasure Segment) (x y : Segment) (C : ℝ)
    (hC : ∀ t : Segment, |f (x, t) - f (y, t)| ≤ C) :
    |(∫ t, f (x, t) ∂(μ : Measure Segment)) -
       ∫ t, f (y, t) ∂(μ : Measure Segment)| ≤ C := by
  have hbound : ∀ᵐ t ∂(μ : Measure Segment), ‖f (x, t) - f (y, t)‖ ≤ C :=
    Filter.Eventually.of_forall (fun t => by simpa only [Real.norm_eq_abs] using hC t)
  have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure Segment)) hbound
  rw [integral_sub (kernel_section_integrable f hf x μ)
    (kernel_section_integrable f hf y μ)] at h
  simpa [Real.norm_eq_abs] using h

/-- Weak convergence of probability measures gives uniform convergence in the
parameter of a jointly continuous kernel on the compact product. -/
theorem weak_convergence_uniform_kernel
    (μs : ℕ → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs atTop (𝓝 μ))
    (f : Segment × Segment → ℝ) (hf : Continuous f) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ x : Segment,
      |(∫ t, f (x, t) ∂(μs n : Measure Segment)) -
         ∫ t, f (x, t) ∂(μ : Measure Segment)| < ε := by
  intro ε hε
  have huc : UniformContinuous f :=
    CompactSpace.uniformContinuous_of_continuous hf
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuous_iff.mp huc (ε / 4) (by positivity)
  obtain ⟨A, _, hAfin, hcover⟩ :=
    finite_cover_balls_of_compact
      (isCompact_univ : IsCompact (Set.univ : Set Segment)) hδ
  have hpoint (y : Segment) :
      ∀ᶠ n : ℕ in atTop,
        |(∫ t, f (y, t) ∂(μs n : Measure Segment)) -
           ∫ t, f (y, t) ∂(μ : Measure Segment)| < ε / 4 := by
    let fy : C(Segment, ℝ) :=
      ⟨fun t => f (y, t), hf.comp (continuous_const.prodMk continuous_id)⟩
    have ht := ((ProbabilityMeasure.continuous_integral_continuousMap fy).tendsto μ).comp hμ
    have he := ht.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4))
    simpa [Metric.mem_ball, Real.dist_eq, fy] using he
  have hfinite : ∀ᶠ n : ℕ in atTop, ∀ y ∈ hAfin.toFinset,
      |(∫ t, f (y, t) ∂(μs n : Measure Segment)) -
         ∫ t, f (y, t) ∂(μ : Measure Segment)| < ε / 4 :=
    (eventually_all_finset hAfin.toFinset).mpr (fun y _ => hpoint y)
  filter_upwards [hfinite] with n hn
  intro x
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ A, dist x y < δ := by
    simpa only [Set.mem_iUnion, Metric.mem_ball, exists_prop] using hcover (Set.mem_univ x)
  have hxykernel (t : Segment) : |f (x, t) - f (y, t)| ≤ ε / 4 := by
    have hd : dist (x, t) (y, t) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_left dist_nonneg] using hxy
    simpa only [Real.dist_eq] using (hmod hd).le
  have hleft := integral_kernel_difference_le f hf (μs n) x y (ε / 4) hxykernel
  have hright := integral_kernel_difference_le f hf μ x y (ε / 4) hxykernel
  have hcenter := hn y (hAfin.mem_toFinset.mpr hy)
  have htri₁ := abs_sub_le
    (∫ t, f (x, t) ∂(μs n : Measure Segment))
    (∫ t, f (y, t) ∂(μs n : Measure Segment))
    (∫ t, f (x, t) ∂(μ : Measure Segment))
  have htri₂ := abs_sub_le
    (∫ t, f (y, t) ∂(μs n : Measure Segment))
    (∫ t, f (y, t) ∂(μ : Measure Segment))
    (∫ t, f (x, t) ∂(μ : Measure Segment))
  rw [abs_sub_comm (∫ t, f (y, t) ∂(μ : Measure Segment))
    (∫ t, f (x, t) ∂(μ : Measure Segment))] at htri₂
  linarith

/-- The actual truncated logarithmic potential, not an abstract kernel limit. -/
theorem weak_convergence_uniform_truncated_log
    (μs : ℕ → ProbabilityMeasure Segment) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto μs atTop (𝓝 μ)) (τ : ℝ) (hτ : 0 < τ) :
    ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop, ∀ x : Segment,
      |(∫ t : Segment, truncatedLogKernel τ x t ∂(μs n : Measure Segment)) -
         ∫ t : Segment, truncatedLogKernel τ x t ∂(μ : Measure Segment)| < ε := by
  apply weak_convergence_uniform_kernel μs μ hμ
    (fun p : Segment × Segment => truncatedLogKernel τ p.1 p.2)
  exact (continuous_truncatedLogKernel τ hτ).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))

/-- Prokhorov compactness and metrizability supply the subsequence. -/
theorem exists_probability_weak_subsequence
    (μs : ℕ → ProbabilityMeasure Segment) :
    ∃ (rows : ℕ → ℕ), StrictMono rows ∧
      ∃ μ : ProbabilityMeasure Segment,
        Tendsto (fun j => μs (rows j)) atTop (𝓝 μ) := by
  obtain ⟨μ, _, rows, hrows, hlim⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (ProbabilityMeasure Segment))).tendsto_subseq
      (fun n => Set.mem_univ (μs n))
  exact ⟨rows, hrows, μ, hlim⟩

noncomputable def empiricalMeasure (X : NodeArray) (n : ℕ) : Measure Segment :=
  ((n + 1 : ℝ≥0∞)⁻¹) • ∑ i : Fin (n + 1), Measure.dirac (X.node n i)

instance empiricalMeasure_isProbabilityMeasure (X : NodeArray) (n : ℕ) :
    IsProbabilityMeasure (empiricalMeasure X n) := by
  constructor
  have hn0 : (n + 1 : ℝ≥0∞) ≠ 0 := by positivity
  have hnt : (n + 1 : ℝ≥0∞) ≠ ⊤ := by simp
  simpa [empiricalMeasure, Measure.smul_apply, Measure.finsetSum_apply] using
    ENNReal.inv_mul_cancel hn0 hnt

noncomputable def empiricalProbability (X : NodeArray) (n : ℕ) :
    ProbabilityMeasure Segment :=
  ⟨empiricalMeasure X n, inferInstance⟩

/-- The normalization is the original n+1, even on a later subsequence. -/
theorem integral_empirical (X : NodeArray) (n : ℕ) (f : Segment → ℝ) :
    (∫ t, f t ∂empiricalMeasure X n) =
      (∑ i : Fin (n + 1), f (X.node n i)) / (n + 1 : ℝ) := by
  rw [empiricalMeasure, integral_smul_measure,
    integral_finsetSum_measure (fun i _ => integrable_dirac (by simp))]
  simp [ENNReal.toReal_inv, ENNReal.toReal_add, smul_eq_mul, div_eq_mul_inv, mul_comm]

theorem exists_empirical_weak_subsequence (X : NodeArray) :
    ∃ (rows : ℕ → ℕ), StrictMono rows ∧
      ∃ μ : ProbabilityMeasure Segment,
        Tendsto (fun j => empiricalProbability X (rows j)) atTop (𝓝 μ) :=
  exists_probability_weak_subsequence (empiricalProbability X)

end Erdos1152.V3
