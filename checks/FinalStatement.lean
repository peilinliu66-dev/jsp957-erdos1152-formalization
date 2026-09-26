import JSP957Final

set_option pp.universes true
set_option pp.proofs false
set_option pp.fullNames true

open Polynomial MeasureTheory Filter
open scoped Topology

example (X : Erdos1152.NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0)) :
    ∃ f : Erdos1152.ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Erdos1152.Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ :=
  Erdos1152.V5.ae_limsup_eq_top X r hr

#print Erdos1152.V5.ae_limsup_eq_top
#check @Erdos1152.V5.ae_limsup_eq_top
#print Erdos1152.NodeArray
#print Erdos1152.NodeArray.Interpolates
#print Erdos1152.LocalAmplificationMinimal
