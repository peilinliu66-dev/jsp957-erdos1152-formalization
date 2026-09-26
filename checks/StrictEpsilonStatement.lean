import JSP957Final

/-! Independent full-type regression for the strict relative-degree endpoint.
Run this file with Lean; verification is recorded by the complete build driver. -/
set_option pp.universes true
set_option pp.proofs false
set_option pp.fullNames true

open Polynomial MeasureTheory Filter
open scoped Topology

example (X : Erdos1152.NodeArray) (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ f : Erdos1152.ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n,
        WithBot.map (fun d : ℕ => (d : ℝ)) (p n).degree <
          (↑((n + 1 : ℝ) * (1 + ε (n + 1))) : WithBot ℝ) ∧
        ∀ i, (p n).eval (X.node n i : ℝ) = f (X.node n i)) →
      ∀ᵐ x ∂volume.restrict Erdos1152.Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ :=
  Erdos1152.V5.ae_limsup_eq_top_strict_epsilon X ε hε

#print Erdos1152.V5.ae_limsup_eq_top_strict_epsilon
#check @Erdos1152.V5.ae_limsup_eq_top_strict_epsilon
