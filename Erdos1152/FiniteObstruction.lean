import Erdos1152.Nodes
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! Stability of a finite obstruction under perturbations of the interpolation data. -/

open Polynomial MeasureTheory Set
open scoped ENNReal

namespace Erdos1152

def commonLowSet (s : Finset ℕ) (p : ℕ → ℝ[X]) (H : ℝ) : Set ℝ :=
  Segment ∩ {x | ∀ n ∈ s, |(p n).eval x| ≤ H}

theorem commonLowSet_measurable (s : Finset ℕ) (p : ℕ → ℝ[X]) (H : ℝ) :
    MeasurableSet (commonLowSet s p H) := by
  have he : {x : ℝ | ∀ n ∈ s, |(p n).eval x| ≤ H} =
      ⋂ n ∈ s, {x | |(p n).eval x| ≤ H} := by ext x; simp
  unfold commonLowSet
  rw [he]
  exact measurableSet_Icc.inter (MeasurableSet.iInter fun n =>
    MeasurableSet.iInter fun _ => isClosed_le (p n).continuous.abs continuous_const |>.measurableSet)

theorem commonLowSet_measure_ne_top (s : Finset ℕ) (p : ℕ → ℝ[X]) (H : ℝ) :
    volume (commonLowSet s p H) ≠ ⊤ :=
  measure_ne_top_of_subset inter_subset_left (by simp [Segment])

def FiniteObstruction (X : NodeArray) (r : ℕ → ℕ) (H : ℝ) (δ : ℝ≥0∞)
    (N : ℕ) (f : ContinuousFunction) : Prop :=
  ∃ s : Finset ℕ, (∀ n ∈ s, N ≤ n) ∧
    ∀ p : ℕ → ℝ[X], (∀ n ∈ s, X.Interpolates r f n (p n)) →
      volume (commonLowSet s p H) < δ

/-- Proposition 11, stated separately from the analytic hypotheses used to prove it. -/
def FiniteAmplification (X : NodeArray) (r : ℕ → ℕ) : Prop :=
  ∀ H : ℝ, 1 < H → ∀ δ : ℝ≥0∞, 0 < δ → ∀ N : ℕ,
    ∃ g : ContinuousFunction, ‖g‖ ≤ 1 ∧ FiniteObstruction X r H δ N g

theorem finiteObstruction_interior (X : NodeArray) (r : ℕ → ℕ)
    {H M : ℝ} {δ : ℝ≥0∞} {N : ℕ} {f : ContinuousFunction}
    (hf : FiniteObstruction X r H δ N f) (hHM : M < H) :
    f ∈ interior {g | FiniteObstruction X r M δ N g} := by
  obtain ⟨s, hs, hf⟩ := hf
  let C := 1 + ∑ n ∈ s, X.lagrangeBound n
  have hC : 0 < C := by
    have := Finset.sum_nonneg (fun n (_ : n ∈ s) => X.lagrangeBound_nonneg n)
    dsimp [C]
    linarith
  have hCn (n : ℕ) (hn : n ∈ s) : X.lagrangeBound n ≤ C := by
    have := Finset.single_le_sum (fun i (_ : i ∈ s) => X.lagrangeBound_nonneg i) hn
    dsimp [C]
    linarith
  apply mem_interior_iff_mem_nhds.mpr
  refine Filter.mem_of_superset (Metric.ball_mem_nhds f (div_pos (sub_pos.mpr hHM) hC)) ?_
  intro g hg
  refine ⟨s, hs, ?_⟩
  intro p hp
  let q := fun n => p n - X.lagrange n (g - f)
  have hq : ∀ n ∈ s, X.Interpolates r f n (q n) := by
    intro n hn
    refine ⟨?_, ?_⟩
    · simpa only [q, max_self] using natDegree_sub_le_of_le (hp n hn).1
        ((X.lagrange_natDegree n (g - f)).trans (show n ≤ n + 1 + r n by omega))
    intro i
    simp [q, eval_sub, X.lagrange_eval, (hp n hn).2 i]
  apply lt_of_le_of_lt (measure_mono ?_) (hf q hq)
  rintro x ⟨hx, hpx⟩
  refine ⟨hx, fun n hn => ?_⟩
  have hg' : ‖g - f‖ < (H - M) / C := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hg
  have hsmall : |(X.lagrange n (g - f)).eval x| < H - M := by
    calc
      _ ≤ X.lagrangeBound n * ‖g - f‖ := X.lagrange_eval_bound n (g - f) ⟨x, hx⟩
      _ ≤ C * ‖g - f‖ := mul_le_mul_of_nonneg_right (hCn n hn) (norm_nonneg _)
      _ < H - M := by nlinarith [(lt_div_iff₀ hC).mp hg']
  have htriangle := abs_sub ((p n).eval x) ((X.lagrange n (g - f)).eval x)
  change |(p n - X.lagrange n (g - f)).eval x| ≤ H
  rw [eval_sub]
  linarith [hpx n hn]

end Erdos1152
