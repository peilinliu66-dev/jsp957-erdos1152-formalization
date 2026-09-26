import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section
open scoped Topology Real
open Complex Set Filter
namespace Erdos1152.V5

/-- Sampling uses normalized sinc; this is distinct from `entireSinc`. -/
def cardinalSinc (x : ℝ) : ℝ := Real.sinc (Real.pi*x)
def samplePoint (t θ : ℝ) (j : ℤ) : ℝ := ((j:ℝ)+θ)/t
def samplingSine (t θ : ℝ) (z : ℂ) : ℂ :=
  Complex.sin (Real.pi*((t:ℂ)*z-θ))
def contourRadius (t : ℝ) (N : ℕ) : ℝ := ((N:ℝ)+1/2)/t

def sineContourConstant : ℝ :=
  min (1/(2*Real.exp Real.pi)) ((1-Real.exp (-Real.pi/2))/2)

theorem sineContourConstant_pos : 0<sineContourConstant := by
  apply lt_min
  · positivity
  · have h : Real.exp (-Real.pi/2)<1 := by
      rw [←Real.exp_zero,Real.exp_lt_exp]
      linarith [Real.pi_pos]
    linarith

private theorem norm_sin_square (z : ℂ) :
    ‖Complex.sin z‖^2=Real.sin z.re^2+Real.sinh z.im^2 := by
  have hre : (Complex.sin z).re=Real.sin z.re*Real.cosh z.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  have him : (Complex.sin z).im=Real.cos z.re*Real.sinh z.im := by
    rw [Complex.sin_eq]
    simp [← Complex.ofReal_sin, ← Complex.ofReal_cos,
      ← Complex.ofReal_sinh, ← Complex.ofReal_cosh]
  rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply,hre,him]
  calc
    _ = Real.sin z.re^2 * Real.cosh z.im^2 +
        Real.cos z.re^2 * Real.sinh z.im^2 := by ring
    _ = Real.sin z.re^2 + (Real.sin z.re^2 + Real.cos z.re^2) *
        Real.sinh z.im^2 := by rw [Real.cosh_sq]; ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

private theorem real_sine_le_complex_sine (z : ℂ) :
    |Real.sin z.re|≤‖Complex.sin z‖ := by
  have h := norm_sin_square z
  nlinarith [sq_nonneg (Real.sinh z.im),sq_abs (Real.sin z.re),norm_nonneg (Complex.sin z)]

private theorem hyperbolic_sine_le_complex_sine (z : ℂ) :
    Real.sinh |z.im|≤‖Complex.sin z‖ := by
  have h := norm_sin_square z
  have he : Real.sinh |z.im|^2=Real.sinh z.im^2 := by
    rcases le_total 0 z.im with h|h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h,Real.sinh_neg]; ring
  have hn : 0≤Real.sinh |z.im| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  nlinarith [sq_nonneg (Real.sin z.re),norm_nonneg (Complex.sin z)]

/-- Half-integer-radius circles stay uniformly away from all sine zeros, including
 the portions close to the real axis. -/
theorem sine_lower_on_half_integer_circle (N : ℕ) (hN : 1≤N) (w : ℂ)
    (hw : ‖w‖=(N:ℝ)+1/2) :
    sineContourConstant*Real.exp (Real.pi*|w.im|)≤‖Complex.sin (Real.pi*w)‖ := by
  have hp := Real.pi_pos
  have hNreal : (1:ℝ)≤N := by exact_mod_cast hN
  by_cases hv : 1/4≤|w.im|
  · have hsmall : Real.exp (-2*(Real.pi*|w.im|))≤Real.exp (-Real.pi/2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hrewrite : Real.sinh (Real.pi*|w.im|)=
        Real.exp (Real.pi*|w.im|)*(1-Real.exp (-2*(Real.pi*|w.im|)))/2 := by
      rw [Real.sinh_eq]
      rw [mul_sub,mul_one,←Real.exp_add]
      congr 2 <;> ring
    have h := hyperbolic_sine_le_complex_sine (Real.pi*w)
    simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,
      abs_mul,abs_of_pos hp] at h
    rw [hrewrite] at h
    apply le_trans _ h
    have hc := min_le_right (1/(2*Real.exp Real.pi)) ((1-Real.exp (-Real.pi/2))/2)
    have hcoeff : sineContourConstant≤
        (1-Real.exp (-2*(Real.pi*|w.im|)))/2 := by
      dsimp [sineContourConstant]
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoeff
      (Real.exp_pos (Real.pi*|w.im|)).le]
  · have hv' : |w.im|≤1/4 := (lt_of_not_ge hv).le
    have hreal : abs (|w.re|-((N:ℝ)+1/2))≤1/8 := by
      have hle : |w.re|≤(N:ℝ)+1/2 := (Complex.abs_re_le_norm w).trans_eq hw
      have heq : w.re^2+w.im^2=((N:ℝ)+1/2)^2 := by
        rw [←hw,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]; ring
      have him2 : w.im^2≤(1/4:ℝ)^2 := by
        rw [← sq_abs w.im]
        exact pow_le_pow_left₀ (abs_nonneg _) hv' 2
      rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      nlinarith [sq_abs w.re,abs_nonneg w.re]
    have hsinhalf : |Real.sin (Real.pi*((N:ℝ)+1/2))|=1 := by
      rw [mul_add, show Real.pi * (1 / 2) = Real.pi / 2 by ring]
      simp [mul_comm Real.pi (N:ℝ),Real.sin_add,Real.cos_nat_mul_pi]
    have hnear := Real.abs_sin_sub_sin_le (Real.pi*|w.re|)
      (Real.pi*((N:ℝ)+1/2))
    have hgap : |Real.pi*|w.re|-Real.pi*((N:ℝ)+1/2)|≤1/2 := by
      rw [←mul_sub,abs_mul,abs_of_pos hp]
      nlinarith [Real.pi_le_four]
    have hsin : 1/2≤|Real.sin (Real.pi*w.re)| := by
      have htri := abs_sub_abs_le_abs_sub (Real.sin (Real.pi*((N:ℝ)+1/2)))
        (Real.sin (Real.pi*|w.re|))
      have he : |Real.sin (Real.pi*|w.re|)|=|Real.sin (Real.pi*w.re)| := by
        rcases le_total 0 w.re with hr|hr
        · rw [abs_of_nonneg hr]
        · rw [abs_of_nonpos hr,mul_neg,Real.sin_neg,abs_neg]
      rw [hsinhalf,he] at htri
      rw [abs_sub_comm] at htri
      linarith [hnear.trans hgap]
    have hcomp := real_sine_le_complex_sine (Real.pi*w)
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hcomp
    apply le_trans _ (hsin.trans hcomp)
    have hexp : Real.exp (Real.pi*|w.im|)≤Real.exp Real.pi := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hc := min_le_left (1/(2*Real.exp Real.pi)) ((1-Real.exp (-Real.pi/2))/2)
    have hbound := mul_le_mul_of_nonneg_right hc
      (le_of_lt (Real.exp_pos (Real.pi*|w.im|)))
    apply hbound.trans
    calc
      _ ≤ (1 / (2 * Real.exp Real.pi)) * Real.exp Real.pi :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = 1 / 2 := by field_simp

theorem samplingSine_lower_on_contour (t θ : ℝ) (ht : 0<t)
    (N : ℕ) (hN : 1≤N) {z : ℂ}
    (hz : z∈Metric.sphere ((θ/t:ℝ):ℂ) (contourRadius t N)) :
    sineContourConstant*Real.exp (Real.pi*t*|z.im|)≤‖samplingSine t θ z‖ := by
  have hw : ‖(t:ℂ)*z-θ‖=(N:ℝ)+1/2 := by
    have he : (t:ℂ)*z-θ=(t:ℂ)*(z-((θ/t:ℝ):ℂ)) := by
      have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      push_cast; field_simp [ht']
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,
      (mem_sphere_iff_norm.mp hz)]
    dsimp [contourRadius]
    field_simp [ht.ne']
  have h := sine_lower_on_half_integer_circle N hN ((t:ℂ)*z-θ) hw
  simpa [samplingSine,abs_mul,abs_of_pos ht,mul_assoc] using h

@[simp] theorem samplingSine_at_grid (t θ : ℝ) (ht : t≠0) (j : ℤ) :
    samplingSine t θ (samplePoint t θ j)=0 := by
  have he : (t:ℂ)*(samplePoint t θ j:ℂ)-θ=(j:ℂ) := by
    have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
    dsimp [samplePoint]; push_cast; field_simp [ht'] <;> ring
  rw [samplingSine,he]
  simpa [mul_comm] using Complex.sin_int_mul_pi j

theorem complex_cos_int_mul_pi (j : ℤ) :
    Complex.cos ((j:ℂ)*Real.pi)=(-1:ℂ)^j := by
  simpa only [Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_intCast,
    Complex.ofReal_zpow, Complex.ofReal_neg, Complex.ofReal_one] using
    congrArg Complex.ofReal (Real.cos_int_mul_pi j)

theorem samplingSine_derivative (t θ : ℝ) (ht : t≠0) (j : ℤ) :
    deriv (samplingSine t θ) (samplePoint t θ j)=
      (Real.pi*t:ℝ)*(-1:ℂ)^j := by
  have hd (z : ℂ) : HasDerivAt (samplingSine t θ)
      ((Real.pi*t:ℝ)*Complex.cos (Real.pi*((t:ℂ)*z-θ))) z := by
    change HasDerivAt (fun w : ℂ => Complex.sin ((Real.pi:ℂ) * ((t:ℂ) * w - (θ:ℂ)))) _ z
    simpa [samplingSine, Function.comp_def, Complex.ofReal_mul, mul_comm, mul_left_comm, mul_assoc] using
      (Complex.hasDerivAt_sin _).comp z
        ((((hasDerivAt_id z).const_mul (t:ℂ)).sub_const (θ:ℂ)).const_mul (Real.pi:ℂ))
  rw [(hd _).deriv]
  have he : (t:ℂ)*(samplePoint t θ j:ℂ)-θ=(j:ℂ) := by
    have ht' : (t:ℂ) ≠ 0 := by exact_mod_cast ht
    dsimp [samplePoint]; push_cast; field_simp [ht'] <;> ring
  rw [he]
  simp [mul_comm (Real.pi:ℂ) (j:ℂ),complex_cos_int_mul_pi]

end Erdos1152.V5
