import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Scalar analytic estimates for a new explicit weighted-packet construction.
These are proved from numerical inequalities, not from LocalAmplification.
The complete packet construction is in research/WEIGHTED_KERNEL_REPLACEMENT.md.
This Lean source is an UNCOMPILED candidate. -/

open Real Polynomial
namespace Erdos1152

/-- A positive binomial tilt is bounded by the exponential with matching slope. -/
theorem binomial_tilt_le_exp (k : ℕ) (t : ℝ) (ht : 0 ≤ 1 + t) :
    (1 + t) ^ k ≤ Real.exp ((k : ℝ) * t) := by
  rw [Real.exp_nat_mul]
  apply pow_le_pow_left₀ ht
  simpa [add_comm] using Real.add_one_le_exp t

/-- The second-order error of the binomial tilt, valid with either sign of `t`. -/
theorem log_one_add_error_bound (t : ℝ) (ht : |t| ≤ 1 / 2) :
    0 ≤ t - Real.log (1 + t) ∧ t - Real.log (1 + t) ≤ 2 * t ^ 2 := by
  have ht' := abs_le.mp ht
  have hx : 0 < 1 + t := by linarith
  have hu : Real.log (1 + t) ≤ t := by
    simpa using Real.log_le_sub_one_of_pos hx
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hl
  have hlow : 1 - (1 + t)⁻¹ ≤ Real.log (1 + t) := by linarith
  have he : t - (1 - (1 + t)⁻¹) = t ^ 2 / (1 + t) := by
    field_simp [hx.ne']
    ring
  refine ⟨sub_nonneg.mpr hu, ?_⟩
  calc
    t - Real.log (1 + t) ≤ t - (1 - (1 + t)⁻¹) := by linarith
    _ = t ^ 2 / (1 + t) := he
    _ ≤ 2 * t ^ 2 := by
      apply (div_le_iff₀ hx).mpr
      have hp := mul_nonneg (sq_nonneg t) (show 0 ≤ 1 + 2 * t by linarith)
      nlinarith [hp]

theorem log_binomial_tilt_error (k : ℕ) (t : ℝ) (ht : |t| ≤ 1 / 2) :
    0 ≤ (k : ℝ) * t - Real.log ((1 + t) ^ k) ∧
      (k : ℝ) * t - Real.log ((1 + t) ^ k) ≤ 2 * k * t ^ 2 := by
  rw [Real.log_pow]
  have h := log_one_add_error_bound t ht
  have h0 := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) h.1
  have h1 := mul_le_mul_of_nonneg_left h.2 (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  constructor <;> nlinarith

/-- A supporting quadratic for the residual field is preserved by the polynomial
binomial tilt. In the packet construction the matching equation is
`k * alpha = s * (Q_s' y - (m/s) * Q' y)`. -/
theorem weighted_tilt_envelope (F : ℝ → ℝ) (s y u a c α : ℝ) (k : ℕ)
    (hs : 0 ≤ s) (hbase : 0 ≤ 1 + α * (u - y))
    (hmatch : (k : ℝ) * α = s * a)
    (hsupport : F y + a * (u - y) + c * (u - y) ^ 2 ≤ F u) :
    Real.exp (-s * (F u - F y)) * (1 + α * (u - y)) ^ k ≤
      Real.exp (-s * c * (u - y) ^ 2) := by
  calc
    _ ≤ Real.exp (-s * (F u - F y)) * Real.exp ((k : ℝ) * (α * (u - y))) :=
      mul_le_mul_of_nonneg_left (binomial_tilt_le_exp k (α * (u - y)) hbase)
        (Real.exp_pos _).le
    _ = Real.exp (-s * (F u - F y) + (k : ℝ) * (α * (u - y))) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_left hsupport hs
      rw [show (k : ℝ) * (α * (u - y)) = (s * a) * (u - y) by
        rw [← mul_assoc, hmatch]]
      nlinarith [hm]

noncomputable def tiltPolynomial (y α : ℝ) (k : ℕ) : ℝ[X] :=
  (C (1 - α * y) + C α * Polynomial.X) ^ k

@[simp] theorem tiltPolynomial_eval (y α u : ℝ) (k : ℕ) :
    (tiltPolynomial y α k).eval u = (1 + α * (u - y)) ^ k := by
  simp only [tiltPolynomial, eval_pow, eval_add, eval_C, eval_mul, eval_X]
  congr 1
  ring

theorem tiltPolynomial_degree (y α : ℝ) (k : ℕ) :
    (tiltPolynomial y α k).natDegree ≤ k := by
  have hlin : (C (1 - α * y) + C α * (Polynomial.X : ℝ[X])).natDegree ≤ 1 := by
    apply (natDegree_add_le _ _).trans
    apply max_le
    · simp only [natDegree_C]; omega
    · exact (natDegree_C_mul_le _ _).trans (by simp)
  calc
    _ ≤ (C (1 - α * y) + C α * (Polynomial.X : ℝ[X])).natDegree * k :=
      by simpa only [tiltPolynomial, Nat.mul_comm] using
        (natDegree_pow_le (p := C (1 - α * y) + C α * (Polynomial.X : ℝ[X])) (n := k))
    _ ≤ 1 * k := Nat.mul_le_mul_right k hlin
    _ = k := one_mul k

/-- A half-slack tilt and a quarter-slack Jackson factor fit below degree `s`.
No excess-degree assumption is hidden in this purely finite budget. -/
theorem tilted_packet_degree_budget (s m k j : ℕ)
    (hm : m ≤ s) (hk : 2 * k ≤ s - m) (hj : 4 * j ≤ s - m) :
    m + k + j ≤ s := by omega

end Erdos1152
