import Erdos1152.V5.NormalizeTrig
import Erdos1152.V5.EntireSinc

noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def trigExtension (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) : ℂ :=
  ∑n∈Finset.Icc (-(k:ℤ)) k,
    coefficient P n*Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)

theorem trigExtension_entire (k : ℕ) (R : ℝ) (P : CircleFunction) :
    Differentiable ℂ (trigExtension k R P) := by
  unfold trigExtension
  fun_prop

theorem trigExtension_real (k : ℕ) (R : ℝ) (P : CircleFunction)
    (hP : P∈bandSpace k) (x : ℝ) :
    trigExtension k R P x=P ((Real.pi*x/R:ℝ):FourierCircle) := by
  obtain ⟨c,hc⟩ := band_expansion hP
  have hcoeff (n : ℤ) (hn : n∈Finset.Icc (-(k:ℤ)) k) : coefficient P n=c n := by
    rw [hc,coefficient_finiteFourier,if_pos hn]
  rw [hc]
  unfold trigExtension
  simp only [finiteFourier_apply]
  apply sum_congr rfl
  intro n hn
  rw [←hc,hcoeff n hn,character_coe]
  congr 2
  push_cast
  ring

private theorem norm_exponential_frequency (n : ℤ) (R : ℝ) (z : ℂ) :
    ‖Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)‖=
      Real.exp (-(Real.pi*n/R:ℝ)*z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp

private theorem frequency_abs_bound {k : ℕ} {n : ℤ}
    (hn : n∈Finset.Icc (-(k:ℤ)) k) {R : ℝ} (hR : 0<R) :
    |Real.pi*n/R|≤Real.pi*k/R := by
  have hb : |(n:ℝ)|≤(k:ℝ) := by
    have := abs_le.mpr (Finset.mem_Icc.mp hn)
    exact_mod_cast this
  rw [abs_div,abs_mul,abs_of_pos Real.pi_pos,abs_of_pos hR]
  gcongr

private theorem card_int_band (k : ℕ) :
    (Finset.Icc (-(k:ℤ)) k).card = 2*k+1 := by
  rw [Int.card_Icc]
  omega

/-- Exponential type and a coefficient bound uniform over every normalized witness. -/
theorem trigExtension_bound (k : ℕ) (R : ℝ) (hR : 0<R) (P : CircleFunction)
    (z : ℂ) :
    ‖trigExtension k R P z‖≤(2*k+1:ℕ)*‖P‖*
      Real.exp ((Real.pi*k/R)*|z.im|) := by
  unfold trigExtension
  apply (norm_sum_le _ _).trans
  calc
    (∑n∈Finset.Icc (-(k:ℤ)) k,
      ‖coefficient P n*Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)‖)
      ≤∑n∈Finset.Icc (-(k:ℤ)) k,‖P‖*Real.exp ((Real.pi*k/R)*|z.im|) := by
        apply sum_le_sum
        intro n hn
        rw [norm_mul,norm_exponential_frequency]
        apply mul_le_mul (norm_coefficient_le P n)
        · apply Real.exp_le_exp.mpr
          calc
            -(Real.pi*n/R)*z.im≤|-(Real.pi*n/R)*z.im| := le_abs_self _
            _=|Real.pi*n/R| * |z.im| := by simp [abs_mul]
            _≤_ := mul_le_mul_of_nonneg_right (frequency_abs_bound hn hR) (abs_nonneg _)
        · positivity
        · positivity
    _=(2*k+1:ℕ)*‖P‖*Real.exp ((Real.pi*k/R)*|z.im|) := by
      simp only [sum_const,nsmul_eq_mul,card_int_band]
      ring

noncomputable def trigDerivative (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) : ℂ :=
  ∑n∈Finset.Icc (-(k:ℤ)) k,
    coefficient P n*((Real.pi*n/R:ℂ)*Complex.I)*
      Complex.exp ((Real.pi*n/R:ℂ)*z*Complex.I)

theorem trigExtension_derivative (k : ℕ) (R : ℝ) (P : CircleFunction) (z : ℂ) :
    HasDerivAt (trigExtension k R P) (trigDerivative k R P z) z := by
  unfold trigExtension trigDerivative
  apply HasDerivAt.fun_sum
  intro n hn
  simpa only [id_eq,mul_one,mul_assoc,mul_comm,mul_left_comm] using
    (((hasDerivAt_id z).const_mul (Real.pi*n/R:ℂ)).mul_const Complex.I).cexp.const_mul
      (coefficient P n)

theorem trigDerivative_real_bound (k : ℕ) (R : ℝ) (hR : 0<R)
    (P : CircleFunction) (x : ℝ) :
    ‖trigDerivative k R P x‖≤((2*k+1:ℕ):ℝ)*‖P‖*(Real.pi*k/R) := by
  unfold trigDerivative
  apply (norm_sum_le _ _).trans
  calc
    _≤∑n∈Finset.Icc (-(k:ℤ)) k,‖P‖*(Real.pi*k/R) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul,norm_mul,norm_mul,norm_exponential_frequency]
      simp only [Complex.ofReal_im,mul_zero,Real.exp_zero,mul_one,Complex.norm_I,
        Complex.norm_real,Real.norm_eq_abs]
      rw [show (Real.pi*n/R:ℂ) = ((Real.pi*n/R:ℝ):ℂ) by push_cast; rfl,
        Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul (norm_coefficient_le P n) (frequency_abs_bound hn hR)
        (abs_nonneg _) (norm_nonneg _)
    _=_ := by
      simp only [sum_const,nsmul_eq_mul,card_int_band]
      ring

theorem trigExtension_real_lipschitz (k : ℕ) (R : ℝ) (hR : 0<R)
    (P : CircleFunction) (x y : ℝ) :
    ‖trigExtension k R P x-trigExtension k R P y‖≤
      ((2*k+1:ℕ):ℝ)*‖P‖*(Real.pi*k/R)*|x-y| := by
  have hd (t : ℝ) : HasDerivAt (fun u:ℝ => trigExtension k R P u)
      (trigDerivative k R P t) t := (trigExtension_derivative k R P t).comp_ofReal
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t).hasDerivWithinAt)
      (fun t ht => trigDerivative_real_bound k R hR P t)
      (convex_univ : Convex ℝ (Set.univ:Set ℝ))
      (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using hb

end Erdos1152.V5
