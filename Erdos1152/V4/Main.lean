import Erdos1152.V4.HighRegion
import Erdos1152.CoarseMain

/-!
# Integration of the constructed high branch with coarse Remez

This is deliberately named as a conditional reduction. The original minimal
amplification input has NOT been implemented in full. No unconditional final
root is declared. The actual growth input is constructed in HighRegion, and
the exact Chebyshev-Remez assumption is avoided by the existing coarse proof.
-/

open Polynomial MeasureTheory Filter
open scoped ENNReal Topology

namespace Erdos1152.V4

/-- The original same-f / all-p / almost-everywhere quantifier order is
preserved. Only the still-missing original hm remains an analytic parameter.
This source has not been elaborated in the current environment. -/
theorem ae_limsup_eq_top_of_canonical_minimal
    (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0))
    (hm : LocalAmplificationMinimal X r (canonicalHighRegion X)) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ := by
  exact ae_limsup_eq_top_of_cardinalGrowth_minimal_coarse X r
    (canonicalHighRegion X) hr (cardinalGrowthCover_canonical X) hm

end Erdos1152.V4
