import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.ContinuousMap.Polynomial
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Tactic.NormNum

/-! Node arrays and the interpolation conditions on the compact interval. -/

open Polynomial

namespace Erdos1152

abbrev Segment := Set.Icc (-1 : ℝ) 1
abbrev ContinuousFunction := C(Segment, ℝ)

instance : Nonempty Segment := ⟨⟨0, by constructor <;> norm_num⟩⟩

/-- Row `n` contains `n + 1` distinct nodes; this includes every positive row size. -/
structure NodeArray where
  node : (n : ℕ) → Fin (n + 1) → Segment
  injective : ∀ n, Function.Injective (node n)

namespace NodeArray

def Interpolates (X : NodeArray) (r : ℕ → ℕ) (f : ContinuousFunction)
    (n : ℕ) (p : ℝ[X]) : Prop :=
  p.natDegree ≤ n + 1 + r n ∧ ∀ i, p.eval (X.node n i : ℝ) = f (X.node n i)

noncomputable def lagrange (X : NodeArray) (n : ℕ) (f : ContinuousFunction) : ℝ[X] :=
  Lagrange.interpolate Finset.univ (fun i => (X.node n i : ℝ)) (fun i => f (X.node n i))

theorem nodes_injective (X : NodeArray) (n : ℕ) :
    Function.Injective (fun i => (X.node n i : ℝ)) :=
  Subtype.val_injective.comp (X.injective n)

theorem lagrange_eval (X : NodeArray) (n : ℕ) (f : ContinuousFunction) (i : Fin (n + 1)) :
    (X.lagrange n f).eval (X.node n i : ℝ) = f (X.node n i) := by
  exact Lagrange.eval_interpolate_at_node _ (X.nodes_injective n).injOn (Finset.mem_univ i)

theorem lagrange_natDegree (X : NodeArray) (n : ℕ) (f : ContinuousFunction) :
    (X.lagrange n f).natDegree ≤ n := by
  apply natDegree_le_of_degree_le
  simpa [lagrange] using Lagrange.degree_interpolate_le (s := Finset.univ)
    (fun i => f (X.node n i))
    (X.nodes_injective n).injOn

theorem lagrange_interpolates (X : NodeArray) (r : ℕ → ℕ) (n : ℕ)
    (f : ContinuousFunction) : X.Interpolates r f n (X.lagrange n f) :=
  ⟨(X.lagrange_natDegree n f).trans (by omega), X.lagrange_eval n f⟩

noncomputable def lagrangeBound (X : NodeArray) (n : ℕ) : ℝ :=
  ∑ i : Fin (n + 1),
    ‖(Lagrange.basis Finset.univ (fun j => (X.node n j : ℝ)) i).toContinuousMapOn Segment‖

theorem lagrangeBound_nonneg (X : NodeArray) (n : ℕ) : 0 ≤ X.lagrangeBound n :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem lagrange_eval_bound (X : NodeArray) (n : ℕ) (f : ContinuousFunction) (x : Segment) :
    |(X.lagrange n f).eval (x : ℝ)| ≤ X.lagrangeBound n * ‖f‖ := by
  simp only [lagrange, Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  calc
    _ ≤ ∑ i : Fin (n + 1), |f (X.node n i)| *
        |(Lagrange.basis Finset.univ (fun j => (X.node n j : ℝ)) i).eval (x : ℝ)| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun i => f (X.node n i) *
          (Lagrange.basis Finset.univ (fun j => (X.node n j : ℝ)) i).eval (x : ℝ)) Finset.univ
    _ ≤ ∑ i : Fin (n + 1), ‖f‖ *
        ‖(Lagrange.basis Finset.univ (fun j => (X.node n j : ℝ)) i).toContinuousMapOn Segment‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul (f.norm_coe_le_norm _) _ (abs_nonneg _) (norm_nonneg f)
      exact ContinuousMap.norm_coe_le_norm
        ((Lagrange.basis Finset.univ (fun j => (X.node n j : ℝ)) i).toContinuousMapOn Segment) x
    _ = _ := by simp [lagrangeBound, Finset.mul_sum, mul_comm]

end NodeArray

end Erdos1152
