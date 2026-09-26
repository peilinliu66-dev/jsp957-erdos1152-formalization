import Erdos1152.V4.PotentialL1

/-!
# Original-row normalization and arbitrary fixed finite deletion

This file turns the probability-potential L¹ theorem into the actual error
integral occurring in `V3.finite_cardinal_growth_with_error_bound`.  The node
count is always the original `rows j + 1`, never the subsequence index.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def rowNodes (X : NodeArray) (n : ℕ) : Finset ℝ :=
  Finset.univ.image (fun i => (X.node n i : ℝ))

noncomputable def deletedReal (S : Finset Segment) : Finset ℝ :=
  S.image Subtype.val

@[simp] theorem mem_rowNodes (X : NodeArray) (n : ℕ) (x : ℝ) :
    x ∈ rowNodes X n ↔ ∃ i, (X.node n i : ℝ) = x := by
  simp [rowNodes]

@[simp] theorem rowNodes_card (X : NodeArray) (n : ℕ) : (rowNodes X n).card = n + 1 := by
  simp only [rowNodes, Finset.card_image_of_injective _ (X.nodes_injective n),
    Finset.card_univ, Fintype.card_fin]

theorem rowNodes_subset (X : NodeArray) (n : ℕ) : (rowNodes X n : Set ℝ) ⊆ Segment := by
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_rowNodes X n x).mp hx
  exact (X.node n i).property

@[simp] theorem deletedReal_card (S : Finset Segment) : (deletedReal S).card = S.card := by
  exact Finset.card_image_of_injective _ Subtype.val_injective

@[simp] theorem coe_mem_deletedReal (S : Finset Segment) (x : Segment) :
    (x : ℝ) ∈ deletedReal S ↔ x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    exact (Subtype.val_injective he) ▸ hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The abstract finite-deletion theorem now has exactly the upstream node set. -/
theorem unassignedNodes_eq_sdiff (X : NodeArray) (S : Finset Segment) (n : ℕ) :
    unassignedNodes X S n = rowNodes X n \ deletedReal S := by
  ext x
  rw [mem_unassignedNodes, Finset.mem_sdiff, mem_rowNodes]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨⟨i, he⟩, ?_⟩
    intro hx
    apply hi
    apply (coe_mem_deletedReal S (X.node n i)).mp
    simpa only [he] using hx
  · rintro ⟨⟨i, he⟩, hx⟩
    refine ⟨i, ?_, he⟩
    intro hi
    apply hx
    have hm := (coe_mem_deletedReal S (X.node n i)).mpr hi
    simpa only [he] using hm

theorem log_source_integrable (t : Segment) :
    Integrable (fun x : ℝ => logProfile (x - (t : ℝ))) baseMeasure := by
  have ha := (shifted_profile_bound (fun u => |logProfile u|)
    logProfile_integrable.abs (fun _ => abs_nonneg _) t).1
  refine ha.mono' ?_ ?_
  · exact (measurable_logProfile.comp (measurable_id.sub measurable_const)).aestronglyMeasurable
  · filter_upwards with x
    simp only [Real.norm_eq_abs, le_refl]

theorem log_source_L1_bound (t : Segment) :
    (∫ x, |logProfile (x - (t : ℝ))| ∂baseMeasure) ≤ logMass :=
  (shifted_profile_bound (fun u => |logProfile u|)
    logProfile_integrable.abs (fun _ => abs_nonneg _) t).2

theorem finitePotential_integrable (Y : Finset ℝ) (N : ℝ)
    (hY : ∀ y ∈ Y, y ∈ Segment) :
    Integrable (V3.finiteLogPotential Y N) baseMeasure := by
  have hi : Integrable (fun x : ℝ => ∑ y ∈ Y, logProfile (x - y)) baseMeasure :=
    integrable_finsetSum Y (fun y hy => log_source_integrable ⟨y, hY y hy⟩)
  change Integrable (fun x => (∑ y ∈ Y, Real.log |x - y|) / N) baseMeasure
  simpa only [logProfile] using hi.div_const N

/-- Uniform bound for a finite removed set; only its cardinality is used. -/
theorem finitePotential_L1_bound (Y : Finset ℝ) (N : ℝ) (hN : 0 < N)
    (hY : ∀ y ∈ Y, y ∈ Segment) :
    (∫ x, |V3.finiteLogPotential Y N x| ∂baseMeasure) ≤
      (Y.card : ℝ) * logMass / N := by
  have hi (y : ℝ) (hy : y ∈ Y) :
      Integrable (fun x : ℝ => |logProfile (x - y)|) baseMeasure :=
    (log_source_integrable ⟨y, hY y hy⟩).abs
  calc
    _ ≤ ∫ x, (∑ y ∈ Y, |logProfile (x - y)|) / N ∂baseMeasure := by
      apply integral_mono (finitePotential_integrable Y N hY).abs
        ((integrable_finsetSum Y hi).div_const N)
      intro x
      dsimp only [V3.finiteLogPotential, logProfile]
      rw [abs_div, abs_of_pos hN]
      exact div_le_div_of_nonneg_right
        (Finset.abs_sum_le_sum_abs (fun y => Real.log |x - y|) Y) hN.le
    _ = (∑ y ∈ Y, ∫ x, |logProfile (x - y)| ∂baseMeasure) / N := by
      rw [integral_div, integral_finsetSum Y hi]
    _ ≤ (∑ _y ∈ Y, logMass) / N := by
      apply div_le_div_of_nonneg_right _ hN.le
      apply Finset.sum_le_sum
      intro y hy
      exact log_source_L1_bound ⟨y, hY y hy⟩
    _ = (Y.card : ℝ) * logMass / N := by simp

/-- Equality, not an asymptotic assertion, for the empirical logarithmic potential. -/
theorem potential_empirical (X : NodeArray) (n : ℕ) (x : ℝ) :
    potential (V3.empiricalProbability X n) x =
      V3.finiteLogPotential (rowNodes X n) (n + 1 : ℝ) x := by
  change (∫ t : Segment, logProfile (x - (t : ℝ)) ∂V3.empiricalMeasure X n) = _
  rw [V3.integral_empirical]
  unfold V3.finiteLogPotential rowNodes
  rw [Finset.sum_image (fun _ _ _ _ h => X.nodes_injective n h)]
  rfl

theorem truncPotential_empirical (X : NodeArray) (n k : ℕ) (x : ℝ) :
    truncPotential (V3.empiricalProbability X n) k x =
      (∑ y ∈ rowNodes X n, V3.truncatedLogKernel (cutoff k) x y) / (n + 1 : ℝ) := by
  change (∫ t : Segment, truncProfile k (x - (t : ℝ)) ∂V3.empiricalMeasure X n) = _
  rw [V3.integral_empirical]
  unfold rowNodes
  rw [Finset.sum_image (fun _ _ _ _ h => X.nodes_injective n h)]
  rfl

/-- Exact finite-deletion identity, with the original normalization. -/
theorem finitePotential_sdiff_sub (Y D : Finset ℝ) (N x : ℝ) :
    V3.finiteLogPotential (Y \ D) N x - V3.finiteLogPotential Y N x =
      -V3.finiteLogPotential (Y ∩ D) N x := by
  have hdisj : Disjoint (Y \ D) (Y ∩ D) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hz).2
  have hunion : (Y \ D) ∪ (Y ∩ D) = Y := by
    ext y
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hs := Finset.sum_union (f := fun y => Real.log |x - y|) hdisj
  rw [hunion] at hs
  dsimp only [V3.finiteLogPotential]
  rw [hs]
  ring

theorem finitePotential_deletion_L1 (Y D : Finset ℝ) (N : ℝ) (hN : 0 < N)
    (hY : ∀ y ∈ Y, y ∈ Segment) :
    (∫ x, |V3.finiteLogPotential (Y \ D) N x - V3.finiteLogPotential Y N x|
      ∂baseMeasure) ≤ (D.card : ℝ) * logMass / N := by
  simp_rw [finitePotential_sdiff_sub, abs_neg]
  apply (finitePotential_L1_bound (Y ∩ D) N hN
    (fun y hy => hY y (Finset.mem_inter.mp hy).1)).trans
  apply div_le_div_of_nonneg_right _ hN.le
  apply mul_le_mul_of_nonneg_right _ logMass_nonneg
  exact_mod_cast Finset.card_le_card (Finset.inter_subset_right : Y ∩ D ⊆ D)

/-- The triangle inequality is applied only to integrable actual potentials. -/
theorem integral_abs_sub_triangle (f g h : ℝ → ℝ)
    (hf : Integrable f baseMeasure) (hg : Integrable g baseMeasure)
    (hh : Integrable h baseMeasure) :
    (∫ x, |f x - h x| ∂baseMeasure) ≤
      (∫ x, |f x - g x| ∂baseMeasure) + (∫ x, |g x - h x| ∂baseMeasure) := by
  have hfg : Integrable (fun x => |f x - g x|) baseMeasure := (hf.sub hg).abs
  have hgh : Integrable (fun x => |g x - h x|) baseMeasure := (hg.sub hh).abs
  rw [← integral_add hfg hgh]
  exact integral_mono (hf.sub hh).abs ((hf.sub hg).abs.add (hg.sub hh).abs)
    (fun x => abs_sub_le (f x) (g x) (h x))

theorem rows_size_tendsto_atTop (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop) :
    Tendsto (fun j => (rows j + 1 : ℝ)) atTop atTop := by
  have hn : Tendsto (fun j => (rows j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hr
  exact tendsto_atTop_mono (fun j => by linarith) hn

/-- All finite assigned-node sets are admitted, after the fixed weak subsequence
has already been chosen.  No rate or separation hypothesis is used. -/
theorem unassigned_potential_L1
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (S : Finset Segment) :
    Tendsto (fun j => ∫ x,
      |V3.finiteLogPotential (unassignedNodes X S (rows j)) (rows j + 1 : ℝ) x -
        potential μ x| ∂baseMeasure) atTop (𝓝 0) := by
  have hfull := weak_convergence_potential_L1
    (fun j => V3.empiricalProbability X (rows j)) μ hμ
  have hsmall : Tendsto (fun j => (S.card : ℝ) * logMass / (rows j + 1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (rows_size_tendsto_atTop rows hr)).const_mul
        ((S.card : ℝ) * logMass)
  have hupper := hsmall.add hfull
  simp only [zero_add] at hupper
  apply squeeze_zero
    (fun j => integral_nonneg (fun _ => abs_nonneg _)) _ hupper
  intro j
  have hy : ∀ y ∈ unassignedNodes X S (rows j), y ∈ Segment := by
    rw [unassignedNodes_eq_sdiff]
    exact fun y hy => rowNodes_subset X (rows j) (Finset.mem_sdiff.mp hy).1
  have htri := integral_abs_sub_triangle
    (V3.finiteLogPotential (unassignedNodes X S (rows j)) (rows j + 1 : ℝ))
    (potential (V3.empiricalProbability X (rows j))) (potential μ)
    (finitePotential_integrable _ _ hy)
    (integrable_potential _) (integrable_potential μ)
  apply htri.trans
  apply add_le_add_left
  simpa only [unassignedNodes_eq_sdiff, potential_empirical, deletedReal_card] using
    finitePotential_deletion_L1 (rowNodes X (rows j)) (deletedReal S)
      (rows j + 1 : ℝ) (by positivity) (rowNodes_subset X (rows j))

/-- The previously displayed error integral is now proved to tend to zero. -/
theorem unassigned_error_lintegral_tendsto_zero
    (X : NodeArray) (rows : ℕ → ℕ) (hr : Tendsto rows atTop atTop)
    (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun j => V3.empiricalProbability X (rows j)) atTop (𝓝 μ))
    (S : Finset Segment) :
    Tendsto (fun j => ∫⁻ x in Segment,
      ENNReal.ofReal |V3.finiteLogPotential (unassignedNodes X S (rows j))
        (rows j + 1 : ℝ) x - potential μ x|) atTop (𝓝 0) := by
  have h := ENNReal.continuous_ofReal.tendsto 0 |>.comp
    (unassigned_potential_L1 X rows hr μ hμ S)
  simp only [ENNReal.ofReal_zero] at h
  convert h using 1
  ext j
  have hY : ∀ y ∈ unassignedNodes X S (rows j), y ∈ Segment := by
    rw [unassignedNodes_eq_sdiff]
    exact fun y hy => rowNodes_subset X (rows j) (Finset.mem_sdiff.mp hy).1
  exact (ofReal_integral_eq_lintegral_ofReal
    ((finitePotential_integrable _ _ hY).sub (integrable_potential μ)).abs
    (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).symm

end Erdos1152.V4
