import Erdos1152.V4.RestrictedKernel
import Erdos1152.V4.FiniteExternalField

/-!
# Uniform restricted kernels after arbitrary finite deletion

All sums in this file run over the actual original n+1 nodes. Deleting a
fixed finite set costs at most |S| times the uniform kernel bound divided by
n+1. The weak subsequence and local interval are fixed before S is introduced.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def removedIndices (X : NodeArray) (S : Finset Segment) (n : ℕ) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun i => X.node n i ∈ S)

noncomputable def erasedAverage (X : NodeArray) (S : Finset Segment) (n : ℕ)
    (f : Segment → ℝ) : ℝ :=
  (∑ i : Fin (n+1), if X.node n i ∈ S then 0 else f (X.node n i)) / (n+1 : ℝ)

theorem removedIndices_card_le (X : NodeArray) (S : Finset Segment) (n : ℕ) :
    (removedIndices X S n).card ≤ S.card := by
  calc
    _ = ((removedIndices X S n).image (X.node n)).card :=
      (Finset.card_image_of_injective _ (X.injective n)).symm
    _ ≤ S.card := Finset.card_le_card (by
      intro t ht
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hi).2)

theorem erasedAverage_add_removed (X : NodeArray) (S : Finset Segment) (n : ℕ)
    (f : Segment → ℝ) :
    erasedAverage X S n f + (∑ i ∈ removedIndices X S n, f (X.node n i))/(n+1 : ℝ) =
      ∫ t, f t ∂V3.empiricalMeasure X n := by
  rw [V3.integral_empirical, erasedAverage, ← add_div]
  congr 1
  rw [removedIndices, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases his : X.node n i ∈ S <;> simp [his]

theorem erasedAverage_difference_le (X : NodeArray) (S : Finset Segment) (n : ℕ)
    (f : Segment → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ t, |f t| ≤ M) :
    |erasedAverage X S n f - ∫ t, f t ∂V3.empiricalMeasure X n| ≤
      (S.card : ℝ)*M/(n+1 : ℝ) := by
  have he := erasedAverage_add_removed X S n f
  have hd : erasedAverage X S n f - ∫ t, f t ∂V3.empiricalMeasure X n =
      -(∑ i ∈ removedIndices X S n, f (X.node n i))/(n+1 : ℝ) := by
    rw [neg_div]
    linarith
  rw [hd, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < n+1)]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ i ∈ removedIndices X S n, |f (X.node n i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ removedIndices X S n, M := Finset.sum_le_sum (fun i hi => hM _)
    _ = ((removedIndices X S n).card : ℝ)*M := by simp
    _ ≤ (S.card : ℝ)*M := mul_le_mul_of_nonneg_right
      (by exact_mod_cast removedIndices_card_le X S n) hM0

theorem erasedAverage_indicator_bounds (X : NodeArray) (S : Finset Segment) (n : ℕ)
    (E : Set Segment) :
    0 ≤ erasedAverage X S n (E.indicator (fun _ => (1 : ℝ))) ∧
    erasedAverage X S n (E.indicator (fun _ => (1 : ℝ))) ≤ 1 := by
  constructor
  · unfold erasedAverage
    apply div_nonneg _ (by positivity)
    apply Finset.sum_nonneg
    intro i hi
    simp only [Set.indicator]
    split_ifs <;> norm_num
  · have hs : (∑ i : Fin (n+1), if X.node n i ∈ S then (0 : ℝ)
        else E.indicator (fun _ => (1 : ℝ)) (X.node n i)) ≤ (n+1 : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin (n+1), (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          simp only [Set.indicator]
          split_ifs <;> norm_num
        _ = _ := by simp
    exact (div_le_one (by positivity : (0 : ℝ) < n+1)).mpr hs

theorem erasedAverage_sum_real_nodes (X : NodeArray) (S : Finset Segment) (n : ℕ)
    (f : ℝ → ℝ) :
    erasedAverage X S n (fun t => f (t : ℝ)) =
      (∑ t ∈ unassignedNodes X S n, f t)/(n+1 : ℝ) := by
  rw [erasedAverage, unassignedNodes_eq_sdiff]
  congr 1
  have he : (∑ t ∈ rowNodes X n \ deletedReal S, f t) =
      ∑ t ∈ rowNodes X n, if t ∈ deletedReal S then 0 else f t := by
    -- Express the actual set difference as a filter.
    simp only [Finset.sdiff_eq_filter]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hs : t ∈ deletedReal S <;> simp [hs]
  rw [he, rowNodes, Finset.sum_image (fun _ _ _ _ h => X.nodes_injective n h)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [coe_mem_deletedReal]

/-- The uniform deletion error tends to zero along the fixed original rows. -/
theorem deletion_bound_tendsto_zero (rows : ℕ → ℕ) (hrows : Tendsto rows atTop atTop)
    (S : Finset Segment) (M : ℝ) :
    Tendsto (fun j => (S.card : ℝ)*M/(rows j+1 : ℝ)) atTop (𝓝 0) := by
  have hd := rows_size_tendsto_atTop rows hrows
  exact tendsto_const_nhds.div_atTop hd

/-- An exact concrete corollary: undeleted interval-node fractions converge
to the mass of the fixed actual interval, for every finite S. -/
theorem erased_interval_fraction_tendsto (X : NodeArray) (rows : ℕ → ℕ)
    (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) {a b : ℝ} (hab : a < b) (S : Finset Segment) :
    Tendsto (fun j => erasedAverage X S (rows j)
      ((sourceInterval a b).indicator (fun _ => (1 : ℝ)))) atTop
      (𝓝 ((μ : Measure Segment).real (sourceInterval a b))) := by
  have hm := weak_sourceInterval_mass _ μ hμ hfloor hab
  have herr : Tendsto (fun j => erasedAverage X S (rows j)
      ((sourceInterval a b).indicator (fun _ => (1 : ℝ))) -
        ∫ t, (sourceInterval a b).indicator (fun _ => (1 : ℝ)) t
          ∂V3.empiricalMeasure X (rows j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (deletion_bound_tendsto_zero rows hrows S 1)
    filter_upwards with j
    simpa only [Real.norm_eq_abs] using erasedAverage_difference_le X S (rows j)
      ((sourceInterval a b).indicator (fun _ => (1 : ℝ))) 1 zero_le_one
      (fun t => by by_cases ht : t ∈ sourceInterval a b <;> simp [ht])
  have hm' : Tendsto (fun j => ∫ t, (sourceInterval a b).indicator (fun _ => (1 : ℝ)) t
      ∂V3.empiricalMeasure X (rows j)) atTop (𝓝 ((μ : Measure Segment).real (sourceInterval a b))) := by
    simpa only [integral_indicator (measurableSet_sourceInterval a b), setIntegral_const,
      smul_eq_mul, mul_one, V3.empiricalProbability, ProbabilityMeasure.coe_mk] using hm
  simpa only [sub_add_cancel, zero_add] using herr.add hm'

/-- Exterior-kernel weak convergence survives every fixed finite deletion.
The limiting kernel and the interval do not depend on S. -/
theorem erased_exterior_uniform (X : NodeArray) (rows : ℕ → ℕ)
    (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) (K : Segment × Segment → ℝ) (hK : Continuous K)
    {a b : ℝ} (hab : a < b) (S : Finset Segment) :
    ∀ ε > (0 : ℝ), ∀ᶠ j in atTop, ∀ x : Segment,
      |erasedAverage X S (rows j) ((sourceInterval a b)ᶜ.indicator (fun t => K (x,t))) -
        ∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment)| < ε := by
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Segment × Segment))).exists_bound_of_continuousOn hK.continuousOn
  let M := max 0 C
  have hM0 : 0 ≤ M := le_max_left _ _
  have hM (x t : Segment) : |K (x,t)| ≤ M := by
    have hb : |K (x,t)| ≤ C := by
      simpa only [Real.norm_eq_abs] using hC (x,t) (Set.mem_univ _)
    exact hb.trans (le_max_right _ _)
  intro ε hε
  have hd := (deletion_bound_tendsto_zero rows hrows S M).eventually
    (gt_mem_nhds (half_pos hε))
  have hw := weak_convergence_uniform_exterior_kernel
    (fun j => V3.empiricalProbability X (rows j)) μ hμ hfloor K hK hab (ε/2) (half_pos hε)
  filter_upwards [hd,hw] with j hj hwj
  intro x
  have he := erasedAverage_difference_le X S (rows j)
    ((sourceInterval a b)ᶜ.indicator (fun t => K (x,t))) M hM0 (fun t => by
      by_cases ht : t ∈ (sourceInterval a b)ᶜ
      · simpa only [Set.indicator_of_mem ht] using hM x t
      · simpa only [Set.indicator_of_notMem ht, abs_zero] using hM0)
  rw [integral_indicator (measurableSet_sourceInterval a b).compl] at he
  have htri := abs_sub_le
    (erasedAverage X S (rows j) ((sourceInterval a b)ᶜ.indicator (fun t => K (x,t))))
    (∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂V3.empiricalMeasure X (rows j))
    (∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment))
  have hwx := hwj x
  change |(∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂V3.empiricalMeasure X (rows j)) - _| < _ at hwx
  linarith

/-- Explicit scalar stability for the subsequent normalization by s/N. -/
theorem quotient_stability (x y d e M : ℝ) (hd : 0 < d) (he : d/2 ≤ e)
    (hM : |y| ≤ M) :
    |x/e-y/d| ≤ (2/d)*|x-y|+(2*M/d^2)*|e-d| := by
  have he0 : 0 < e := (half_pos hd).trans_le he
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hid : x/e-y/d = (x-y)/e + y*(d-e)/(e*d) := by field_simp; ring
  rw [hid]
  calc
    _ ≤ |(x-y)/e| + |y*(d-e)/(e*d)| := abs_add_le _ _
    _ = |x-y|/e + |y| * |e-d|/(e*d) := by
      rw [abs_div, abs_of_pos he0, abs_div, abs_mul, abs_mul,
        abs_of_pos he0, abs_of_pos hd, abs_sub_comm d e]
    _ ≤ |x-y|/(d/2) + (M*|e-d|)/((d/2)*d) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (abs_nonneg _) (half_pos hd) he
      · exact div_le_div₀ (mul_nonneg hM0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_right hM (abs_nonneg _))
          (mul_pos (half_pos hd) hd) (mul_le_mul_of_nonneg_right he hd.le)
    _ = _ := by field_simp <;> ring

/-- Uniformity is retained after the row normalization. This is a theorem
about the actual deleted sums, not a predicate requiring a field limit. -/
theorem erased_normalized_exterior_uniform (X : NodeArray) (rows : ℕ → ℕ)
    (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) (K : Segment × Segment → ℝ) (hK : Continuous K)
    {a b : ℝ} (hab : a < b) (hmass : 0 < (μ : Measure Segment).real (sourceInterval a b))
    (S : Finset Segment) :
    ∀ ε > (0 : ℝ), ∀ᶠ j in atTop, ∀ x : Segment,
      |erasedAverage X S (rows j) ((sourceInterval a b)ᶜ.indicator (fun t => K (x,t))) /
        erasedAverage X S (rows j) ((sourceInterval a b).indicator (fun _ => (1 : ℝ))) -
        (∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment)) /
          (μ : Measure Segment).real (sourceInterval a b)| < ε := by
  let d := (μ : Measure Segment).real (sourceInterval a b)
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Segment × Segment))).exists_bound_of_continuousOn hK.continuousOn
  let M := max 0 C
  have hM0 : 0 ≤ M := le_max_left _ _
  have hM (x : Segment) : |∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment)| ≤ M := by
    have hb (t : Segment) : ‖K (x,t)‖ ≤ M := (hC (x,t) (Set.mem_univ _)).trans (le_max_right _ _)
    have hle := norm_integral_le_of_norm_le_const
      (μ := (μ : Measure Segment).restrict (sourceInterval a b)ᶜ)
      (Filter.Eventually.of_forall hb)
    have hm : (μ : Measure Segment).real ((sourceInterval a b)ᶜ) ≤ 1 := by
      have h := measureReal_mono (μ := (μ : Measure Segment))
        (subset_univ ((sourceInterval a b)ᶜ)) (measure_ne_top (μ : Measure Segment) Set.univ)
      simpa only [Measure.real, measure_univ, ENNReal.toReal_one] using h
    have hle' : |∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment)| ≤
        M*(μ : Measure Segment).real ((sourceInterval a b)ᶜ) := by
      simpa only [Real.norm_eq_abs, Measure.real, Measure.restrict_apply_univ] using hle
    exact hle'.trans (by nlinarith)
  have hd := erased_interval_fraction_tendsto X rows hrows μ hμ hfloor hab S
  let A := 2/d+2*M/d^2+1
  have hA : 0 < A := by dsimp [A,d]; positivity
  intro ε hε
  have hden := hd.eventually (lt_mem_nhds (by simpa only [d] using half_lt_self hmass))
  have hdenerr := hd.eventually (Metric.ball_mem_nhds d (div_pos hε hA))
  have hnum := erased_exterior_uniform X rows hrows μ hμ hfloor K hK hab S
    (ε/A) (div_pos hε hA)
  filter_upwards [hden,hdenerr,hnum] with j hj hje hjn
  intro x
  have hdpos : 0 < d := hmass
  have hbound := quotient_stability
    (erasedAverage X S (rows j) ((sourceInterval a b)ᶜ.indicator (fun t => K (x,t))))
    (∫ t in (sourceInterval a b)ᶜ, K (x,t) ∂(μ : Measure Segment)) d
    (erasedAverage X S (rows j) ((sourceInterval a b).indicator (fun _ => (1 : ℝ)))) M
    hdpos hj.le (hM x)
  have he : |erasedAverage X S (rows j) ((sourceInterval a b).indicator (fun _ => (1 : ℝ)))-d| < ε/A := by
    simpa only [Metric.mem_ball, Real.dist_eq] using hje
  have hn := hjn x
  have c1 : 0 < 2/d := div_pos (by norm_num) hdpos
  have c2 : 0 ≤ 2*M/d^2 := by positivity
  have h1 := mul_lt_mul_of_pos_left hn c1
  have h2 := mul_le_mul_of_nonneg_left he.le c2
  have htotal : (2/d)*(ε/A)+(2*M/d^2)*(ε/A) < ε := by
    have hid : A*(ε/A)=ε := mul_div_cancel₀ ε hA.ne'
    have hterm : 0 < ε/A := div_pos hε hA
    dsimp only [A] at hid
    nlinarith
  exact hbound.trans_lt ((add_lt_add_of_lt_of_le h1 h2).trans htotal)

end Erdos1152.V4
