import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Degree.Defs
import Erdos1152.V5.FiniteFourier

/-!
# Strict relative-degree endpoint

Candidate pending compilation against the completed fixed project dependencies.
The node-array row `n` represents the positive row size `N = n + 1`.
The input `ε` is indexed by the original row size, so the bound uses `ε (n + 1)`.

We use a convenient majorant `ceil (N * |ε N|)`; optimal rounding is unnecessary.
The final degree inequality uses `WithBot ℝ`, preserving `degree 0 = ⊥` even
when a finite initial value of `N * (1 + ε N)` is nonpositive.
-/

open Polynomial MeasureTheory Filter
open scoped Topology

namespace Erdos1152.V5

/-- A natural-valued majorant for the real excess in the strict degree bound. -/
noncomputable def strictEpsilonExcess (ε : ℕ → ℝ) (n : ℕ) : ℕ :=
  ⌈(n + 1 : ℝ) * |ε (n + 1)|⌉₊

theorem strictEpsilonExcess_ratio_le (ε : ℕ → ℝ) (n : ℕ) :
    (strictEpsilonExcess ε n : ℝ) / (n + 1 : ℝ) ≤
      |ε (n + 1)| + 1 / (n + 1 : ℝ) := by
  have hN : 0 < (n + 1 : ℝ) := by positivity
  have hceil : (strictEpsilonExcess ε n : ℝ) ≤
      (n + 1 : ℝ) * |ε (n + 1)| + 1 := by
    simpa only [strictEpsilonExcess] using
      (Nat.ceil_lt_add_one
        (mul_nonneg hN.le (abs_nonneg (ε (n + 1))))).le
  calc
    (strictEpsilonExcess ε n : ℝ) / (n + 1 : ℝ) ≤
        ((n + 1 : ℝ) * |ε (n + 1)| + 1) / (n + 1 : ℝ) :=
      div_le_div_of_nonneg_right hceil hN.le
    _ = |ε (n + 1)| + 1 / (n + 1 : ℝ) := by
      field_simp [hN.ne']

theorem strictEpsilonExcess_sublinear (ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => (strictEpsilonExcess ε n : ℝ) / (n + 1 : ℝ))
      atTop (𝓝 0) := by
  have hshift : Tendsto (fun n : ℕ => ε (n + 1)) atTop (𝓝 0) :=
    hε.comp (tendsto_add_atTop_nat 1)
  have habs : Tendsto (fun n : ℕ => |ε (n + 1)|) atTop (𝓝 0) := by
    simpa only [Function.comp_def, abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)).comp hshift
  have hinv : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hupper : Tendsto (fun n : ℕ => |ε (n + 1)| + 1 / (n + 1 : ℝ))
      atTop (𝓝 0) := by
    simpa only [zero_add] using habs.add hinv
  exact squeeze_zero
    (fun n => div_nonneg (Nat.cast_nonneg _) (by positivity))
    (strictEpsilonExcess_ratio_le ε) hupper

/-- The strict real-degree bound, including the zero polynomial, implies the
natural-degree budget required by the integer-excess terminal. -/
theorem natDegree_le_strictEpsilonExcess (ε : ℕ → ℝ) (n : ℕ) (p : ℝ[X])
    (hdegree : WithBot.map (fun d : ℕ => (d : ℝ)) p.degree <
      (↑((n + 1 : ℝ) * (1 + ε (n + 1))) : WithBot ℝ)) :
    p.natDegree ≤ n + 1 + strictEpsilonExcess ε n := by
  classical
  by_cases hp : p = 0
  · subst p
    simp
  have hd : (p.natDegree : ℝ) < (n + 1 : ℝ) * (1 + ε (n + 1)) := by
    simpa only [Polynomial.degree_eq_natDegree hp, Nat.cast_withBot, WithBot.map_coe,
      WithBot.coe_lt_coe] using hdegree
  have hmajor : (n + 1 : ℝ) * ε (n + 1) ≤
      (n + 1 : ℝ) * |ε (n + 1)| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
  have hceil : (n + 1 : ℝ) * |ε (n + 1)| ≤
      (strictEpsilonExcess ε n : ℝ) := by
    simpa only [strictEpsilonExcess] using
      Nat.le_ceil ((n + 1 : ℝ) * |ε (n + 1)|)
  have hbound : (p.natDegree : ℝ) ≤
      (n + 1 : ℝ) + (strictEpsilonExcess ε n : ℝ) := by
    nlinarith
  exact_mod_cast hbound

end Erdos1152.V5

#print axioms Erdos1152.V5.strictEpsilonExcess_ratio_le
#print axioms Erdos1152.V5.strictEpsilonExcess_sublinear
#print axioms Erdos1152.V5.natDegree_le_strictEpsilonExcess
