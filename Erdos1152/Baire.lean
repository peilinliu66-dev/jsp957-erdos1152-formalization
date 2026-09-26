import Erdos1152.Density

/-! A single continuous function for every admissible sequence of interpolants. -/

open Polynomial MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Erdos1152

theorem exists_all_finiteObstructions (X : NodeArray) (r : ℕ → ℕ)
    (hamp : FiniteAmplification X r) :
    ∃ f : ContinuousFunction, ∀ M N k : ℕ,
      FiniteObstruction X r M ((k + 1 : ℝ≥0∞)⁻¹) N f := by
  let U : ℕ × ℕ × ℕ → Set ContinuousFunction := fun i =>
    interior {f | FiniteObstruction X r i.1 ((i.2.2 + 1 : ℝ≥0∞)⁻¹) i.2.1 f}
  have hopen : ∀ i, IsOpen (U i) := fun _ => isOpen_interior
  have hdense : ∀ i, Dense (U i) := fun i =>
    dense_finiteObstruction_interior X r hamp i.1 (ENNReal.inv_pos.mpr (by simp)) i.2.1
  obtain ⟨f, hf⟩ := (dense_iInter_of_isOpen hopen hdense).nonempty
  refine ⟨f, fun M N k => ?_⟩
  change f ∈ {g | FiniteObstruction X r M ((k + 1 : ℝ≥0∞)⁻¹) N g}
  exact interior_subset (mem_iInter.mp hf (M, N, k))

theorem common_tail_null (X : NodeArray) (r : ℕ → ℕ) (f : ContinuousFunction)
    (hf : ∀ M N k : ℕ, FiniteObstruction X r M ((k + 1 : ℝ≥0∞)⁻¹) N f)
    (p : ℕ → ℝ[X]) (hp : ∀ n, X.Interpolates r f n (p n)) (M N : ℕ) :
    volume (Segment ∩ {x | ∀ n ≥ N, |(p n).eval x| ≤ (M : ℝ)}) = 0 := by
  by_contra hzero
  obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt hzero
  obtain ⟨s, hs, hf⟩ := hf M N k
  have hbound := hf p (fun n _ => hp n)
  have hsub : Segment ∩ {x | ∀ n ≥ N, |(p n).eval x| ≤ (M : ℝ)} ⊆
      commonLowSet s p M := by
    rintro x ⟨hx, hpx⟩
    exact ⟨hx, fun n hn => hpx n (hs n hn)⟩
  have hi : (k + 1 : ℝ≥0∞)⁻¹ ≤ (k : ℝ≥0∞)⁻¹ :=
    ENNReal.inv_le_inv.mpr (le_add_of_nonneg_right zero_le_one)
  exact (lt_irrefl _ ((measure_mono hsub).trans_lt (hbound.trans_le hi) |>.trans hk))

/-- The finite amplification theorem implies the full order of quantifiers in Theorem 1. -/
theorem ae_unbounded_of_finiteAmplification (X : NodeArray) (r : ℕ → ℕ)
    (hamp : FiniteAmplification X r) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment, ∀ M N : ℕ,
        ∃ n ≥ N, (M : ℝ) < |(p n).eval x| := by
  obtain ⟨f, hf⟩ := exists_all_finiteObstructions X r hamp
  refine ⟨f, fun p hp => ?_⟩
  apply ae_all_iff.mpr
  intro M
  apply ae_all_iff.mpr
  intro N
  apply (ae_restrict_iff' measurableSet_Icc).mpr
  apply ae_iff.mpr
  apply measure_mono_null _ (common_tail_null X r f hf p hp M N)
  intro x hx
  simp only [mem_ofPred_eq, Classical.not_imp, not_exists, not_and, not_lt] at hx
  exact hx

theorem limsup_eq_top_of_unbounded (u : ℕ → ℝ)
    (hu : ∀ M N : ℕ, ∃ n ≥ N, (M : ℝ) < u n) :
    limsup (fun n => (u n : EReal)) atTop = ⊤ := by
  apply (EReal.eq_top_iff_forall_lt _).mpr
  intro y
  obtain ⟨M, hM⟩ := exists_nat_gt y
  have hf : ∃ᶠ n in atTop, ((M : ℝ) : EReal) ≤ (u n : EReal) := by
    apply frequently_atTop.mpr
    intro N
    obtain ⟨n, hn, hu⟩ := hu M N
    exact ⟨n, hn, by exact_mod_cast hu.le⟩
  exact (EReal.coe_lt_coe_iff.mpr hM).trans_le (le_limsup_of_frequently_le hf)

theorem ae_limsup_eq_top_of_finiteAmplification (X : NodeArray) (r : ℕ → ℕ)
    (hamp : FiniteAmplification X r) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ := by
  obtain ⟨f, hf⟩ := ae_unbounded_of_finiteAmplification X r hamp
  refine ⟨f, fun p hp => ?_⟩
  filter_upwards [hf p hp] with x hx
  exact limsup_eq_top_of_unbounded _ hx

end Erdos1152
