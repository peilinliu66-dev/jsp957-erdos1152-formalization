import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open scoped Topology Real
open MeasureTheory Set Filter
namespace Erdos1152.V5

/-- Unnormalized entire sinc: `sin z/z`, with its removable value filled in. -/
def entireSinc (z : ℂ) : ℂ := if z=0 then 1 else Complex.sin z/z

theorem entireSinc_eq_dslope : entireSinc=dslope Complex.sin 0 := by
  ext z
  by_cases hz : z=0
  · simp [entireSinc,hz,dslope_same]
  · simp [entireSinc,hz,dslope_of_ne Complex.sin hz,slope,div_eq_mul_inv,mul_comm]

theorem differentiable_entireSinc : Differentiable ℂ entireSinc := by
  rw [entireSinc_eq_dslope]
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (s := univ) (c := 0) (by simp)).mpr
      Complex.differentiable_sin.differentiableOn)

@[simp] theorem entireSinc_zero : entireSinc 0=1 := by simp [entireSinc]

@[simp] theorem entireSinc_real (x : ℝ) : entireSinc (x:ℂ)=(Real.sinc x:ℂ) := by
  by_cases hx : x=0
  · simp [hx]
  · simp [entireSinc,Real.sinc,hx,Complex.ofReal_eq_zero,Complex.ofReal_sin]

theorem norm_complex_sin_le (z : ℂ) : ‖Complex.sin z‖≤Real.exp |z.im| := by
  rw [Complex.sin,norm_div,norm_mul,Complex.norm_I,mul_one]
  norm_num
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_exp,Complex.norm_exp]
  have h1 : (-(z*Complex.I)).re≤|z.im| := by simp; exact le_abs_self _
  have h2 : (z*Complex.I).re≤|z.im| := by simp; exact neg_le_abs _
  linarith [Real.exp_le_exp.mpr h1,Real.exp_le_exp.mpr h2]

theorem norm_complex_cos_le (z : ℂ) : ‖Complex.cos z‖≤Real.exp |z.im| := by
  rw [Complex.cos,norm_div]
  norm_num
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  apply (norm_add_le _ _).trans
  rw [Complex.norm_exp,Complex.norm_exp]
  have h1 : (-(z*Complex.I)).re≤|z.im| := by simp; exact le_abs_self _
  have h2 : (z*Complex.I).re≤|z.im| := by simp; exact neg_le_abs _
  linarith [Real.exp_le_exp.mpr h1,Real.exp_le_exp.mpr h2]

/-- An integral representation valid also at the removable point. -/
theorem entireSinc_integral (z : ℂ) :
    entireSinc z=∫t:ℝ in (0:ℝ)..1,Complex.cos (z*t) := by
  by_cases hz : z=0
  · simp [hz]
  have hd (t : ℝ) : HasDerivAt (fun s:ℝ => Complex.sin (z*s)/z)
      (Complex.cos (z*t)) t := by
    apply HasDerivAt.comp_ofReal (e := fun s:ℂ => Complex.sin (z*s)/z)
    simpa only [Function.comp_def, id_eq, mul_one, mul_div_cancel_right₀ _ hz] using
      ((Complex.hasDerivAt_sin (z*t)).comp (t:ℂ)
        ((hasDerivAt_id (t:ℂ)).const_mul z)).div_const z
  have hi : IntervalIntegrable (fun t:ℝ => Complex.cos (z*t)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t) hi]
  simp [entireSinc,hz]

theorem norm_entireSinc_le_exp (z : ℂ) : ‖entireSinc z‖≤Real.exp |z.im| := by
  rw [entireSinc_integral]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => Complex.cos (z*t))
    (a := (0:ℝ)) (b := 1) (C := Real.exp |z.im|) (fun t ht => ?_)
  · simpa using h
  · apply (norm_complex_cos_le (z*t)).trans
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_add,
      abs_mul,Real.norm_eq_abs]
    have ht' : 0≤t ∧ t≤1 := by
      have htt : 0<t ∧ t≤1 := by
        simpa [Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)] using ht
      exact ⟨htt.1.le,htt.2⟩
    rw [abs_of_nonneg ht'.1]
    exact mul_le_of_le_one_right (abs_nonneg _) ht'.2

/-- Global algebraic decay with the correct exponential type. -/
theorem norm_entireSinc_decay (z : ℂ) :
    ‖entireSinc z‖≤2*Real.exp |z.im|/(1+‖z‖) := by
  by_cases hz : ‖z‖≤1
  · apply (norm_entireSinc_le_exp z).trans
    rw [le_div_iff₀ (by positivity)]
    nlinarith [Real.exp_pos |z.im|]
  · have hn : 0<‖z‖ := by linarith [norm_nonneg z]
    have hzne : z≠0 := norm_pos_iff.mp hn
    rw [entireSinc,if_neg hzne,norm_div]
    apply (div_le_div_of_nonneg_right (norm_complex_sin_le z) hn.le).trans
    rw [div_le_div_iff₀ hn (by positivity)]
    nlinarith [Real.exp_pos |z.im|]

theorem sinc_power_nonneg (γ x : ℝ) : 0≤Real.sinc (γ*x)^4 := by positivity

theorem sinc_power_le_one (γ x : ℝ) : Real.sinc (γ*x)^4≤1 := by
  have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one (γ*x)) 4
  simpa only [show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs,one_pow] using h

theorem exists_sinc_fourth_near_one : ∃η>0,∀x:ℝ,|x|≤η→1/2≤Real.sinc x^4 := by
  have hc := (Real.continuous_sinc.pow 4).continuousAt (x := 0)
  obtain ⟨η,hη,hηc⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  refine ⟨η/2,by positivity,?_⟩
  intro x hx
  have hh := hηc (show dist x 0<η by simpa [Real.dist_eq] using hx.trans_lt (half_lt_self hη))
  simp only [Pi.pow_apply,Real.sinc_zero,one_pow,Real.dist_eq] at hh
  linarith [(abs_lt.mp hh).1]

theorem sinc_fourth_tail {γ d : ℝ} (hγ : 0<γ) (hd : d≠0) :
    Real.sinc (γ*d)^4≤(1/(γ*|d|))^4 := by
  have hgd : γ*d≠0 := mul_ne_zero hγ.ne' hd
  have h : |Real.sinc (γ*d)|≤1/(γ*|d|) := by
    rw [Real.sinc_of_ne_zero hgd,abs_div,abs_mul,abs_of_pos hγ]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
  have hh := pow_le_pow_left₀ (abs_nonneg _) h 4
  simpa only [show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs,one_pow] using hh

end Erdos1152.V5
