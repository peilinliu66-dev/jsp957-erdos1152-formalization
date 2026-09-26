import Erdos1152.V4.SourceCount
import Erdos1152.CoarseCardinalLocal

/-!
# The actual high-potential cover

The region is defined exclusively by integrals of the selected weak limit,
not by a cardinal-growth or local-amplification predicate. The theorem
`cardinalGrowthCover_canonical` constructs all fields of the upstream cover.
The fixed weak subsequence is selected once; a tail can depend on the finite
assigned set, as permitted by the original definition.

Candidate source: no compilation claim is made by this file.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

theorem cardinalGoodSet_bad_tendsto_zero
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (S : Finset Segment) (c η : ℝ) (hη : 0 < η) :
    Tendsto (fun j => volume.real
      (V3.highRegion (potential μ) c \
        V3.cardinalGoodSet (potential μ) c η (unassignedNodes X S (rows j))
          (rows j + 1 : ℝ))) atTop (𝓝 0) := by
  have hlim := (unassigned_potential_L1 X rows hr μ hμ S).div_const η
  simp only [zero_div] at hlim
  apply squeeze_zero (fun j => ENNReal.toReal_nonneg) _ hlim
  intro j
  let Y := unassignedNodes X S (rows j)
  let e : ℝ → ℝ := fun x =>
    |V3.finiteLogPotential Y (rows j + 1 : ℝ) x - potential μ x|
  have hY : ∀ y ∈ Y, y ∈ Segment := by
    intro y hy
    rw [show Y = rowNodes X (rows j) \ deletedReal S from
      unassignedNodes_eq_sdiff X S (rows j)] at hy
    exact rowNodes_subset X (rows j) (Finset.mem_sdiff.mp hy).1
  have he : Integrable e baseMeasure :=
    ((finitePotential_integrable Y (rows j + 1 : ℝ) hY).sub
      (integrable_potential μ)).abs
  have he0 : 0 ≤ ∫ x, e x ∂baseMeasure := integral_nonneg (fun _ => abs_nonneg _)
  have her : (∫⁻ x in Segment, ENNReal.ofReal (e x)) =
      ENNReal.ofReal (∫ x, e x ∂baseMeasure) :=
    (ofReal_integral_eq_lintegral_ofReal he
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm
  have hineq := V3.cardinalGoodSet_error_measure (potential μ)
    (measurable_potential μ) c η Y (rows j + 1 : ℝ)
  change ENNReal.ofReal η * volume
      (V3.highRegion (potential μ) c \ V3.cardinalGoodSet (potential μ) c η Y
        (rows j + 1 : ℝ)) ≤ ∫⁻ x in Segment, ENNReal.ofReal (e x) at hineq
  rw [her] at hineq
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hineq
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hη.le,
    ENNReal.toReal_ofReal he0] at hreal
  apply (le_div_iff₀ hη).mpr
  simpa only [Measure.real, mul_comm] using hreal

/-- A concrete clipped-potential source region supplies the complete cardinal
cover on a fixed high level. No finite-growth input remains. -/
theorem cardinalGrowthOn_potential_layer
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (k : ℕ) (b η : ℝ) (hη : 0 < η)
    (hmass : 0 < (μ : Measure Segment) (Subtype.val ⁻¹' sourceRegion μ k b η)) :
    CardinalGrowthOn X (V3.highRegion (potential μ) (b + 3 * η)) := by
  classical
  intro S
  have hf := eventually_finite_source_hypotheses X rows hr μ hμ k b η hη hmass S
  obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hf
  let tail : ℕ → ℕ := fun j => j + j₀
  have ht : Tendsto tail atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp [tail]; omega) tendsto_id
  let ns : ℕ → ℕ := fun j => rows (tail j)
  have hns : Tendsto ns atTop atTop := hr.comp ht
  have hμns : Tendsto (fun j => V3.empiricalProbability X (ns j)) atTop (𝓝 μ) :=
    hμ.comp ht
  have hsource (j : ℕ) : ∃ z ∈ unassignedNodes X S (ns j),
      ∀ x ∈ V3.cardinalGoodSet (potential μ) (b + 3 * η) η
        (unassignedNodes X S (ns j)) (ns j + 1 : ℝ),
        Real.exp (η * (ns j + 1 : ℝ)) ≤
          |(cardinalPolynomial (unassignedNodes X S (ns j)) z).eval x| := by
    obtain ⟨hc, hu, hcost, hp⟩ := hj₀ (tail j) (by dsimp [tail]; omega)
    obtain ⟨z, hz, _, hgrow, _⟩ := V3.finite_cardinal_growth_with_error_bound
      (rowNodes X (ns j)) (deletedReal S) (sourceRegion μ k b η) (potential μ)
      (ns j + 1 : ℝ) (cutoff k) b η η (by positivity) (cutoff_pos k)
      (cutoff_le_one k) (measurable_potential μ) (fun x hx => rowNodes_subset X (ns j) hx)
      hc hu hcost hp
    refine ⟨z, ?_, ?_⟩
    · simpa only [unassignedNodes_eq_sdiff] using hz
    · simpa only [unassignedNodes_eq_sdiff] using hgrow
  choose z hz hzg using hsource
  let E : ℕ → Set ℝ := fun j => V3.cardinalGoodSet (potential μ) (b + 3 * η) η
    (unassignedNodes X S (ns j)) (ns j + 1 : ℝ)
  refine ⟨ns, hns, z, hz, η, hη, E, ?_, ?_, ?_⟩
  · intro j
    exact ⟨V3.measurable_cardinalGoodSet (potential μ) (measurable_potential μ) _ _ _ _,
      V3.cardinalGoodSet_subset _ _ _ _ _⟩
  · exact cardinalGoodSet_bad_tendsto_zero X ns hns μ hμns S (b + 3 * η) η hη
  · exact Filter.Eventually.of_forall hzg

/-- Empty levels must still satisfy the upstream source-every-row requirement.
We use rows late enough to leave at least one unassigned node. -/
theorem cardinalGrowthOn_empty (X : NodeArray) : CardinalGrowthOn X ∅ := by
  classical
  intro S
  let rows : ℕ → ℕ := fun j => j + S.card
  have hr : Tendsto rows atTop atTop :=
    tendsto_atTop_mono (fun j => by dsimp [rows]; omega) tendsto_id
  have hne (j : ℕ) : (unassignedNodes X S (rows j)).Nonempty := by
    have hc := unassignedNodes_card X S (rows j)
    apply Finset.card_pos.mp
    dsimp [rows] at hc ⊢
    omega
  choose z hz using hne
  refine ⟨rows, hr, z, hz, 1, by norm_num, fun _ => ∅, ?_, ?_, ?_⟩
  · intro j
    exact ⟨MeasurableSet.empty, Set.Subset.rfl⟩
  · simpa only [Set.sdiff_self, measureReal_empty] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · filter_upwards with j x hx
    exact False.elim hx

abbrev LevelIndex := ℕ × ℚ × ℚ

/-- This is an analytic test on the weak limit. It does not mention either
`CardinalGrowthOn` or `LocalAmplification`. -/
def ValidLevel (μ : ProbabilityMeasure Segment) (q : LevelIndex) : Prop :=
  0 < (q.2.2 : ℝ) ∧
    0 < (μ : Measure Segment)
      (Subtype.val ⁻¹' sourceRegion μ q.1 (q.2.1 : ℝ) (q.2.2 : ℝ))

noncomputable def potentialLayer (μ : ProbabilityMeasure Segment) (q : LevelIndex) : Set ℝ :=
  if ValidLevel μ q then V3.highRegion (potential μ) ((q.2.1 : ℝ) + 3 * (q.2.2 : ℝ))
  else ∅

/-- A countable union of explicit logarithmic-potential levels. -/
noncomputable def highPotentialRegion (μ : ProbabilityMeasure Segment) : Set ℝ :=
  ⋃ q : LevelIndex, potentialLayer μ q

theorem measurable_potentialLayer (μ : ProbabilityMeasure Segment) (q : LevelIndex) :
    MeasurableSet (potentialLayer μ q) := by
  classical
  unfold potentialLayer
  split_ifs
  · exact V3.measurable_highRegion _ (measurable_potential μ) _
  · exact MeasurableSet.empty

theorem potentialLayer_subset (μ : ProbabilityMeasure Segment) (q : LevelIndex) :
    potentialLayer μ q ⊆ Segment := by
  classical
  unfold potentialLayer
  split_ifs
  · exact fun _ hx => hx.1
  · exact empty_subset _

theorem measurable_highPotentialRegion (μ : ProbabilityMeasure Segment) :
    MeasurableSet (highPotentialRegion μ) :=
  MeasurableSet.iUnion (measurable_potentialLayer μ)

theorem highPotentialRegion_subset (μ : ProbabilityMeasure Segment) :
    highPotentialRegion μ ⊆ Segment := by
  intro x hx
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
  exact potentialLayer_subset μ q hq

/-- Every level, including the inactive levels, has a constructed growth item. -/
theorem cardinalGrowthOn_all_layers
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (q : LevelIndex) : CardinalGrowthOn X (potentialLayer μ q) := by
  classical
  by_cases hq : ValidLevel μ q
  · rw [potentialLayer, if_pos hq]
    exact cardinalGrowthOn_potential_layer X rows hr μ hμ q.1 _ _ hq.1 hq.2
  · rw [potentialLayer, if_neg hq]
    exact cardinalGrowthOn_empty X

/-- This theorem constructs the original, unchanged cover definition. -/
theorem cardinalGrowthCover_of_weak_limit
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ)) :
    CardinalGrowthCover X (highPotentialRegion μ) := by
  classical
  let qn : ℕ → LevelIndex := fun n => (Encodable.decode (α := LevelIndex) n).getD (0, 0, 0)
  let B : ℕ → Set ℝ := fun n => potentialLayer μ (qn n)
  refine ⟨B, ?_, ?_⟩
  · intro n
    exact ⟨measurable_potentialLayer μ (qn n), potentialLayer_subset μ (qn n),
      cardinalGrowthOn_all_layers X rows hr μ hμ (qn n)⟩
  · filter_upwards with x hx
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
    refine ⟨Encodable.encode q, ?_⟩
    simpa only [B, qn, Encodable.encodek, Option.getD_some] using hq

/-- The data are obtained from compactness, never supplied by a caller. -/
noncomputable def canonicalRows (X : NodeArray) : ℕ → ℕ :=
  Classical.choose (V3.exists_empirical_weak_subsequence X)

noncomputable def canonicalMeasure (X : NodeArray) : ProbabilityMeasure Segment :=
  Classical.choose (Classical.choose_spec (V3.exists_empirical_weak_subsequence X)).2

theorem canonicalRows_strictMono (X : NodeArray) : StrictMono (canonicalRows X) :=
  (Classical.choose_spec (V3.exists_empirical_weak_subsequence X)).1

theorem canonicalRows_tendsto (X : NodeArray) :
    Tendsto (canonicalRows X) atTop atTop := (canonicalRows_strictMono X).tendsto_atTop

theorem canonicalMeasure_weak (X : NodeArray) :
    Tendsto (fun j => V3.empiricalProbability X (canonicalRows X j)) atTop
      (𝓝 (canonicalMeasure X)) :=
  Classical.choose_spec ((Classical.choose_spec
    (V3.exists_empirical_weak_subsequence X)).2)

noncomputable def canonicalHighRegion (X : NodeArray) : Set ℝ :=
  highPotentialRegion (canonicalMeasure X)

/-- FIRST ACTUAL ANALYTIC INSTANCE: no weak-limit, error, source, cover,
or amplification input remains in the statement. -/
theorem cardinalGrowthCover_canonical (X : NodeArray) :
    CardinalGrowthCover X (canonicalHighRegion X) :=
  cardinalGrowthCover_of_weak_limit X (canonicalRows X) (canonicalRows_tendsto X)
    (canonicalMeasure X) (canonicalMeasure_weak X)

/-- The coarse Remez proof is connected to the constructed high-potential
instance. The only hypothesis is the original sublinear excess condition. -/
theorem localAmplificationAbove_canonical (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0)) :
    LocalAmplificationAbove X r (canonicalHighRegion X) :=
  localAmplificationAbove_of_cardinalGrowthCover_coarse X r hr
    (canonicalHighRegion X) (cardinalGrowthCover_canonical X)

end Erdos1152.V4
