import Erdos1152.LocalToInterval
import Erdos1152.FiniteConstruction
import Erdos1152.Baire
import Erdos1152.CardinalLocal

/-! The finite and category part of Theorem 1, with its local analytic input explicit. -/

open Polynomial MeasureTheory Filter
open scoped ENNReal Topology

namespace Erdos1152

theorem finiteAmplification_of_localAmplification (X : NodeArray) (r : ℕ → ℕ)
    (hlocal : LocalAmplification X r) : FiniteAmplification X r := by
  apply finiteAmplification_of_intervalAmplification X r
  intro H hH
  obtain ⟨c, hc, hc1, hlocalH⟩ := hlocal H hH
  refine ⟨c / 2, by positivity, by linarith, fun N => ?_⟩
  exact intervalAmplification_of_localData X r H c hc.le hlocalH N

/-- One continuous function works for every admissible interpolation sequence. -/
theorem ae_limsup_eq_top_of_localAmplification (X : NodeArray) (r : ℕ → ℕ)
    (hlocal : LocalAmplification X r) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ :=
  ae_limsup_eq_top_of_finiteAmplification X r
    (finiteAmplification_of_localAmplification X r hlocal)

/-- The main conclusion from Remez, cardinal growth above the minimum potential,
and the remaining local input on its complement. -/
theorem ae_limsup_eq_top_of_cardinalGrowth_minimal (X : NodeArray) (r : ℕ → ℕ)
    (A : Set ℝ) (hR : RemezChebyshevInequality)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (hg : CardinalGrowthCover X A) (hm : LocalAmplificationMinimal X r A) :
    ∃ f : ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ :=
  ae_limsup_eq_top_of_localAmplification X r
    (localAmplification_of_above_minimal X r A
      (localAmplificationAbove_of_cardinalGrowthCover X r hR hr A hg) hm)

end Erdos1152
