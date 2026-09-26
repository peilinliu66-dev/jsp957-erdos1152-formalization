import Erdos1152.V5.Minimal

/-!
# Original same-function / all-interpolants terminal

Compilation and kernel verification status are recorded by the complete build
driver and the actual compiler receipts. The statement has no analytic parameters.
-/
open Polynomial MeasureTheory Filter
open scoped Topology
namespace Erdos1152.V5

/-- Full node-array and sublinear excess range. The function is selected before
all interpolation sequences; the exceptional null set may depend on the sequence.
Only X, r and the original sublinearity condition are parameters. -/
theorem ae_limsup_eq_top
    (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0)) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ := by
  exact V4.ae_limsup_eq_top_of_canonical_minimal X r hr
    (localAmplificationMinimal_canonical X r hr)

end Erdos1152.V5
