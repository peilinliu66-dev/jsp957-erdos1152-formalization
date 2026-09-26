import Erdos1152.Main
import Erdos1152.CoarseCardinalLocal

/-! Conditional terminal with the first analytic input replaced by the new
coarse Remez proof candidate. This is NOT a solution of Erdős 1152:
CardinalGrowthCover and LocalAmplificationMinimal remain assumptions.
The source has NOT been compiled in the current environment. -/
open Polynomial MeasureTheory Filter
open scoped ENNReal Topology
namespace Erdos1152

theorem ae_limsup_eq_top_of_cardinalGrowth_minimal_coarse
    (X : NodeArray) (r : ℕ → ℕ) (A : Set ℝ)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (hg : CardinalGrowthCover X A) (hm : LocalAmplificationMinimal X r A) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ := by
  apply ae_limsup_eq_top_of_localAmplification X r
  exact localAmplification_of_above_minimal X r A
    (localAmplificationAbove_of_cardinalGrowthCover_coarse X r hr A hg) hm

end Erdos1152
