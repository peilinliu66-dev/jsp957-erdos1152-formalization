import Erdos1152.V5.FejerGrid

/-!
V6 regression entry for the repaired FejerGrid dependency.
These are compiler checks, not an independent proof of the original problem.
No output from this file is claimed until it is actually run with Lean.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open Erdos1152.V5

-- Reproduce the accepted defect without hiding the required rewrite inside .mp.
example {ι : Type*} (a : ι → ℂ) (p q : ι)
    (hmax : ‖a q‖ ≤ ‖a p‖) (hz : a p = 0) : a q = 0 := by
  have hq : ‖a q‖ ≤ 0 := by simpa [hz] using hmax
  exact norm_le_zero_iff.mp hq

-- The auxiliary grid length, unlike the original interpolation nodes, is nonzero.
example (L : ℕ) [NeZero L] (a : ZMod L → ℂ) (p : ZMod L) :
    fejerGridCombination L a (circleGrid L p) = a p :=
  fejerGridCombination_at_grid L a p

example (L : ℕ) [NeZero L] (x : FourierCircle) :
    ∑ q : ZMod L, fejerGridWeight L q x = 1 :=
  sum_fejerGridWeight L x

-- The zero-constraint boundary still has a nontrivial normalized grid vector.
example : ∃ a : ZMod 1 → ℂ, ∃ p : ZMod 1,
    a p = 1 ∧ (∀ q, ‖a q‖ ≤ 1) ∧
    (∀ x, ‖fejerGridCombination 1 a x‖ ≤ 1) := by
  obtain ⟨a, p, hp, ha, _, hf, _⟩ :=
    exists_normalized_fejer_annihilator 1 (κ := Fin 0) (by simp)
      (0 : CircleFunction →ₗ[ℂ] (Fin 0 → ℂ))
  exact ⟨a, p, hp, ha, hf⟩

#check @Erdos1152.V5.exists_normalized_fejer_annihilator
#print axioms Erdos1152.V5.exists_normalized_fejer_annihilator
