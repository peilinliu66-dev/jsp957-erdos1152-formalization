import Erdos1152.V4.FinitePotential

/-!
# Positive empirical counts and surviving low-potential sources

The finite-growth hypotheses `hcount`, `htrunc`, `hcost`, and `hpay` are supplied
from the actual weak limit.  None is retained as a terminal analytic assumption.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

/-- Continuity is on the whole real parameter axis. The source variable ranges
on a compact space, so no condition at infinity in the parameter is required. -/
theorem continuous_truncPotential (μ : ProbabilityMeasure Segment) (k : ℕ) :
    Continuous (truncPotential μ k) := by
  have hc : Continuous
      (Function.uncurry (fun (x : ℝ) (t : Segment) => truncProfile k (x - (t : ℝ)))) :=
    (continuous_truncProfile k).comp
      (continuous_fst.sub (continuous_subtype_val.comp continuous_snd))
  change Continuous (fun x => ∫ t : Segment, truncProfile k (x - (t : ℝ)) ∂(μ : Measure Segment))
  simpa only [setIntegral_univ] using
    (continuous_parametric_integral_of_continuous (μ := (μ : Measure Segment)) hc
      (isCompact_univ : IsCompact (Set.univ : Set Segment)))

/-- Exact conversion between empirical mass and the cardinality of actual real nodes. -/
theorem empirical_mass_eq_node_count (X : NodeArray) (n : ℕ)
    (V : Set ℝ) (hV : MeasurableSet V) :
    (V3.empiricalMeasure X n).real (Subtype.val ⁻¹' V) =
      (((rowNodes X n).filter (fun x => x ∈ V)).card : ℝ) / (n + 1 : ℝ) := by
  classical
  let f : Segment → ℝ := (Subtype.val ⁻¹' V).indicator (fun _ => 1)
  have hf := V3.integral_empirical X n f
  have hleft : (∫ t, f t ∂V3.empiricalMeasure X n) =
      (V3.empiricalMeasure X n).real (Subtype.val ⁻¹' V) := by
    rw [show f = (Subtype.val ⁻¹' V).indicator (fun _ => (1 : ℝ)) from rfl,
      integral_indicator (hV.preimage measurable_subtype_coe)]
    simp only [integral_const, smul_eq_mul, mul_one, Measure.restrict_apply_univ,
      Measure.real]
  have hsum : (∑ i : Fin (n + 1), f (X.node n i)) =
      (((rowNodes X n).filter (fun x => x ∈ V)).card : ℝ) := by
    have himage : (∑ x ∈ rowNodes X n, if x ∈ V then (1 : ℝ) else 0) =
        ∑ i : Fin (n + 1), if (X.node n i : ℝ) ∈ V then (1 : ℝ) else 0 := by
      exact Finset.sum_image (fun _ _ _ _ h => X.nodes_injective n h)
    have hsum' : (∑ i : Fin (n + 1), f (X.node n i)) =
        ∑ x ∈ rowNodes X n, if x ∈ V then (1 : ℝ) else 0 := by
      simpa only [f, Set.indicator, Set.mem_preimage] using himage.symm
    rw [hsum']
    simp only [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_zero, add_zero]
  rwa [hleft, hsum] at hf

/-- An open set with positive limiting mass contains a positive linear fraction
of original row nodes.  Arbitrarily small original node gaps are permitted. -/
theorem eventually_positive_linear_node_count
    (X : NodeArray) (rows : ℕ → ℕ) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (V : Set ℝ) (hV : IsOpen V)
    (hmass : 0 < (μ : Measure Segment) (Subtype.val ⁻¹' V)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ j : ℕ in atTop,
      c * (rows j + 1 : ℝ) <
        (((rowNodes X (rows j)).filter (fun x => x ∈ V)).card : ℝ) := by
  let v : ℝ := (μ : Measure Segment).real (Subtype.val ⁻¹' V)
  have hv : 0 < v := ENNReal.toReal_pos hmass.ne' (measure_ne_top _ _)
  have hc : 0 < v / 2 := by positivity
  have hopen : IsOpen (Subtype.val ⁻¹' V : Set Segment) := hV.preimage continuous_subtype_val
  have hn := μ.toMeasure_add_pos_gt_mem_nhds hopen (ENNReal.ofReal_pos.mpr hc)
  refine ⟨v / 2, hc, ?_⟩
  filter_upwards [hμ.eventually hn] with j hj
  have ht := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
    (by finiteness :
      (V3.empiricalProbability X (rows j)).toMeasure (Subtype.val ⁻¹' V) +
        ENNReal.ofReal (v / 2) ≠ ⊤)).mpr hj
  have hmass' : v < (V3.empiricalMeasure X (rows j)).real (Subtype.val ⁻¹' V) + v / 2 := by
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hc.le] at ht
    exact ht
  rw [empirical_mass_eq_node_count X (rows j) V hV.measurableSet] at hmass'
  have hfrac : v / 2 <
      (((rowNodes X (rows j)).filter (fun x => x ∈ V)).card : ℝ) / (rows j + 1 : ℝ) := by
    linarith
  exact (lt_div_iff₀ (by positivity : (0 : ℝ) < rows j + 1)).mp hfrac

/-- The row subsequence is fixed before the finite deletion budget is given. -/
theorem eventually_more_nodes_than_finite_set
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (V : Set ℝ) (hV : IsOpen V)
    (hmass : 0 < (μ : Measure Segment) (Subtype.val ⁻¹' V)) (D : ℕ) :
    ∀ᶠ j : ℕ in atTop, D < ((rowNodes X (rows j)).filter (fun x => x ∈ V)).card := by
  obtain ⟨c, hc, hcount⟩ := eventually_positive_linear_node_count X rows μ hμ V hV hmass
  have hlarge := (rows_size_tendsto_atTop rows hr).eventually
    (eventually_gt_atTop ((D : ℝ) / c))
  filter_upwards [hcount, hlarge] with j hj hN
  have hd : (D : ℝ) < (rows j + 1 : ℝ) * c := (div_lt_iff₀ hc).mp hN
  have hlt : (D : ℝ) <
      (((rowNodes X (rows j)).filter (fun x => x ∈ V)).card : ℝ) := by nlinarith
  exact_mod_cast hlt

noncomputable def sourceRegion (μ : ProbabilityMeasure Segment) (k : ℕ) (b η : ℝ) : Set ℝ :=
  {x | truncPotential μ k x < b - 2 * η}

theorem isOpen_sourceRegion (μ : ProbabilityMeasure Segment) (k : ℕ) (b η : ℝ) :
    IsOpen (sourceRegion μ k b η) :=
  isOpen_lt (continuous_truncPotential μ k) continuous_const

/-- The four finite hypotheses needed by the cardinal-growth lemma are now
consequences of the actual weak limit and fixed scalar parameters. -/
theorem eventually_finite_source_hypotheses
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (k : ℕ) (b η : ℝ) (hη : 0 < η)
    (hmass : 0 < (μ : Measure Segment) (Subtype.val ⁻¹' sourceRegion μ k b η))
    (S : Finset Segment) :
    ∀ᶠ j : ℕ in atTop,
      (deletedReal S).card < ((rowNodes X (rows j)).filter
        (fun x => x ∈ sourceRegion μ k b η)).card ∧
      (∀ z ∈ rowNodes X (rows j), z ∈ sourceRegion μ k b η →
        (∑ y ∈ rowNodes X (rows j), V3.truncatedLogKernel (cutoff k) z y) ≤
          (rows j + 1 : ℝ) * (b - η)) ∧
      (((deletedReal S).card : ℝ) + 1) * (-Real.log (cutoff k)) ≤
        (rows j + 1 : ℝ) * η ∧
      Real.log 2 ≤ η * (rows j + 1 : ℝ) := by
  have hcount := eventually_more_nodes_than_finite_set X rows hr μ hμ
    (sourceRegion μ k b η) (isOpen_sourceRegion μ k b η) hmass (deletedReal S).card
  have hunif := V3.weak_convergence_uniform_truncated_log
    (fun j => V3.empiricalProbability X (rows j)) μ hμ (cutoff k) (cutoff_pos k) η hη
  have hcost := (rows_size_tendsto_atTop rows hr).eventually
    (eventually_ge_atTop ((((deletedReal S).card : ℝ) + 1) * (-Real.log (cutoff k)) / η))
  have hpay := (rows_size_tendsto_atTop rows hr).eventually
    (eventually_ge_atTop (Real.log 2 / η))
  filter_upwards [hcount, hunif, hcost, hpay] with j hj hU hC hP
  refine ⟨hj, ?_, ?_, ?_⟩
  · intro z hz hzV
    have hzseg := rowNodes_subset X (rows j) hz
    have he : |truncPotential (V3.empiricalProbability X (rows j)) k z -
        truncPotential μ k z| < η := by
      simpa only [truncPotential, truncProfile, V3.truncatedLogKernel] using
        hU (⟨z, hzseg⟩ : Segment)
    have hzlow : truncPotential μ k z < b - 2 * η := hzV
    have hnum : truncPotential (V3.empiricalProbability X (rows j)) k z ≤ b - η := by
      have := (abs_lt.mp he).2
      linarith
    rw [truncPotential_empirical] at hnum
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < rows j + 1)).mp hnum
    simpa only [mul_comm] using h
  · exact (div_le_iff₀ hη).mp hC
  · have h := (div_le_iff₀ hη).mp hP
    simpa only [mul_comm] using h

end Erdos1152.V4
