import JSP957Final

/-! Diagnostics of repaired dependencies. A successful diagnostic is not a
substitute for the complete build and FinalStatement / FinalAxioms entries. -/
set_option pp.universes true
set_option pp.proofs false
set_option pp.fullNames true

open Polynomial MeasureTheory Filter
open scoped Topology

-- This application must elaborate at the original quantifier order without
-- additional analytic assumptions. Printed names alone do not establish that.
example (X : Erdos1152.NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0)) :
    ∃ f : Erdos1152.ContinuousFunction, ∀ p : ℕ → ℝ[X],
      (∀ n, X.Interpolates r f n (p n)) →
      ∀ᵐ x ∂volume.restrict Erdos1152.Segment,
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ :=
  Erdos1152.V5.ae_limsup_eq_top X r hr

#check @Erdos1152.V5.sum_fejerGridWeight
#check @Erdos1152.V5.coefficient_fejerKernel
#check @Erdos1152.V5.corrected_moments
#check @Erdos1152.V5.cauchy_finite_simple_poles
#check @Erdos1152.V5.actual_weighted_family
#print axioms Erdos1152.V5.corrected_moments
#print axioms Erdos1152.V5.cauchy_finite_simple_poles
#print axioms Erdos1152.V5.actual_weighted_family
#print Erdos1152.V5.localAmplificationMinimal_canonical
#print Erdos1152.V5.ae_limsup_eq_top
#print axioms Erdos1152.V5.ae_limsup_eq_top
