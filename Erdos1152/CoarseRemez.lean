import Erdos1152.FiniteLagrangeBounds
import Mathlib.Analysis.Complex.Exponential

/-! An elementary exponential Remez bound. The theorem below has no Remez
hypothesis. It uses finite separated sampling, Lagrange interpolation, and
factorial cancellation. New proof candidate: NOT compiler checked here. -/

open Polynomial MeasureTheory Set
open scoped Classical

namespace Erdos1152

noncomputable def coarseRemezConstant : ℝ := 32 * Real.exp 1

theorem coarseRemezConstant_pos : 0 < coarseRemezConstant := by
  unfold coarseRemezConstant
  positivity

theorem two_le_coarseRemezConstant : 2 ≤ coarseRemezConstant := by
  have h := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [coarseRemezConstant]
  linarith

private theorem factorial_cancellation (d : ℕ) :
    ((d + 1 : ℝ) ^ d) / (d.factorial : ℝ) ≤ (2 * Real.exp 1) ^ d := by
  by_cases hd : d = 0
  · subst d
    norm_num
  · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have hd1r : (1 : ℝ) ≤ d := by exact_mod_cast hd1
    have hbase : (d + 1 : ℝ) ≤ 2 * d := by linarith
    have hexp := Real.pow_div_factorial_le_exp (d : ℝ)
      (Nat.cast_nonneg d : (0 : ℝ) ≤ d) d
    have he : Real.exp (d : ℝ) = (Real.exp 1) ^ d := by
      simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) d
    calc
      (d + 1 : ℝ) ^ d / (d.factorial : ℝ)
          ≤ (2 * (d : ℝ)) ^ d / (d.factorial : ℝ) :=
            div_le_div_of_nonneg_right
              (pow_le_pow_left₀ (by positivity) hbase d) (by positivity)
      _ = (2 : ℝ) ^ d * ((d : ℝ) ^ d / (d.factorial : ℝ)) := by
        rw [mul_pow]
        ring
      _ ≤ (2 : ℝ) ^ d * Real.exp (d : ℝ) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (2 * Real.exp 1) ^ d := by rw [he, mul_pow]

/-- Universal measurable-set estimate on `[-1,1]`, with an absolute base `32e`.
In particular, the set may have empty interior. This is a theorem, not an
external analytic hypothesis. Its proof candidate still requires compilation. -/
theorem coarse_remez (p : ℝ[X]) (E : Set ℝ) (H : ℝ)
    (_hE : MeasurableSet E) (hEsub : E ⊆ Icc (-1 : ℝ) 1)
    (hμ : 0 < volume.real E) (hH : 0 ≤ H)
    (hval : ∀ x ∈ E, |p.eval x| ≤ H) (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) :
    |p.eval z| ≤ H * (coarseRemezConstant / volume.real E) ^ p.natDegree := by
  let μ : ℝ := volume.real E
  let d : ℕ := p.natDegree
  obtain ⟨x, hxmono, hxE, hxgap⟩ := exists_sorted_samples E μ hμ rfl d
  let δ : ℝ := μ / (4 * (d + 1 : ℝ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsep := eval_bound_of_separated_nodes p d le_rfl x hxmono δ H hδ hH
    (fun i => hEsub (hxE i)) hxgap (fun i => hval (x i) (hxE i)) z hz
  have hμ0 : μ ≠ 0 := hμ.ne'
  have hn0 : (d + 1 : ℝ) ≠ 0 := by positivity
  have hδval : (4 : ℝ) / δ = (16 / μ) * (d + 1) := by
    dsimp [δ]
    field_simp [hμ0, hn0]
    <;> ring
  have hfact := factorial_cancellation d
  calc
    |p.eval z| ≤ H * (4 / δ) ^ d / (d.factorial : ℝ) := hsep
    _ = H * (16 / μ) ^ d * ((d + 1 : ℝ) ^ d / (d.factorial : ℝ)) := by
      rw [hδval, mul_pow]
      ring
    _ ≤ H * (16 / μ) ^ d * (2 * Real.exp 1) ^ d :=
      mul_le_mul_of_nonneg_left hfact (by positivity)
    _ = H * (coarseRemezConstant / volume.real E) ^ p.natDegree := by
      dsimp [coarseRemezConstant, μ, d]
      rw [show (32 * Real.exp 1) / volume.real E =
        (16 / volume.real E) * (2 * Real.exp 1) by ring,
        mul_pow (16 / volume.real E) (2 * Real.exp 1)]
      ring

end Erdos1152
