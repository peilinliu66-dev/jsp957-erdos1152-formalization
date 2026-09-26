import Erdos1152.V5.GammaAmplitude
import Erdos1152.V5.FiniteSampling
import Erdos1152.ExternalField
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial
namespace Erdos1152.V5

def meshNode (m j : ℕ) : ℝ := -1+(2*(j:ℝ)+1)/(m:ℝ)
def meshPolynomial (m : ℕ) : ℝ[X] :=
  ∏j∈Finset.range m,(Polynomial.X-Polynomial.C (meshNode m j))
def meshBasis (m j : ℕ) : ℝ[X] := Lagrange.basis (Finset.range m) (meshNode m) j

theorem meshNode_injective (m : ℕ) (hm : 0<m) : Function.Injective (meshNode m) := by
  intro j k he
  have hm' : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold meshNode at he
  have hh := (div_left_inj' hm').mp (add_left_cancel he)
  have heq : (j:ℝ)=(k:ℝ) := by linarith
  exact_mod_cast heq

theorem meshNode_mem (m j : ℕ) (hm : 0<m) (hj : j<m) : |meshNode m j|<1 := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have hj' : (j:ℝ)+1≤m := by exact_mod_cast Nat.succ_le_of_lt hj
  rw [meshNode,abs_lt]
  constructor
  · have hpos : 0<(2*(j:ℝ)+1)/(m:ℝ) := by positivity
    linarith
  · have hh : (2*(j:ℝ)+1)/(m:ℝ)<2 := by
      rw [div_lt_iff₀ hm']; linarith
    linarith

private theorem gamma_shift_product (a : ℝ) (n : ℕ)
    (ha : ∀j∈Finset.range n,a+(j:ℝ)≠0) :
    Real.Gamma (a+n)=Real.Gamma a*∏j∈Finset.range n,(a+(j:ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : a+(n:ℝ)≠0 := ha n (by simp)
    have hi := ih (fun j hj => ha j (Finset.mem_range.mpr (by
      have := Finset.mem_range.mp hj; omega)))
    rw [Nat.cast_succ,←add_assoc,Real.Gamma_add_one hn,hi,Finset.prod_range_succ]
    ring

private theorem mesh_scaled_product (m : ℕ) (hm : 0<m) (u : ℝ) :
    (meshPolynomial m).eval u=(2/(m:ℝ))^m*(-1:ℝ)^m*
      ∏j∈Finset.range m,(1/2-(m:ℝ)*(1+u)/2+(j:ℝ)) := by
  have hm' : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  rw [meshPolynomial,Polynomial.eval_prod]
  have he : ∀j∈Finset.range m,u-meshNode m j=
      -(2/(m:ℝ))*(1/2-(m:ℝ)*(1+u)/2+(j:ℝ)) := by
    intro j hj
    unfold meshNode
    field_simp [hm']
    ring
  simp only [Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C]
  rw [Finset.prod_congr rfl he,Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_range]
  rw [neg_pow]
  ring

private theorem mesh_gamma_formula (m : ℕ) (hm : 0<m) (u : ℝ) (hu : u∈Icc (-1:ℝ) 1) :
    (meshPolynomial m).eval u=(2/(m:ℝ))^m*(-1:ℝ)^m*
      Real.Gamma ((m:ℝ)*(1+u)/2+1/2)*Real.Gamma ((m:ℝ)*(1-u)/2+1/2)*
        Real.cos (Real.pi*(m:ℝ)*(1+u)/2)/Real.pi := by
  classical
  let z := (m:ℝ)*(1+u)/2
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have hup : 0≤1+u := by linarith [hu.1]
  have hz0 : 0≤z := by dsimp [z]; positivity
  have hzm : z≤m := by
    dsimp [z]
    have hup2 : 1+u≤2 := by linarith [hu.2]
    calc
      (m:ℝ)*(1+u)/2 ≤ (m:ℝ)*2/2 := by gcongr
      _ = (m:ℝ) := by ring
  by_cases hroot : ∃j∈Finset.range m,u=meshNode m j
  · obtain ⟨j,hj,rfl⟩ := hroot
    have hz : (m:ℝ)*(1+meshNode m j)/2=(j:ℝ)+1/2 := by
      unfold meshNode; field_simp [hm'.ne']; ring
    have hp : (meshPolynomial m).eval (meshNode m j)=0 := by
      rw [meshPolynomial,Polynomial.eval_prod]
      apply Finset.prod_eq_zero hj
      simp
    rw [hp]
    have hcos : Real.cos (Real.pi*(m:ℝ)*(1+meshNode m j)/2)=0 := by
      rw [show Real.pi*(m:ℝ)*(1+meshNode m j)/2=Real.pi*((j:ℝ)+1/2) by
        calc
          _ = Real.pi*((m:ℝ)*(1+meshNode m j)/2) := by ring
          _ = _ := congrArg (fun x : ℝ => Real.pi*x) hz]
      rw [show Real.pi*((j:ℝ)+1/2)=(j:ℝ)*Real.pi+Real.pi/2 by ring]
      simp [Real.cos_add,Real.sin_nat_mul_pi]
    simp [hcos]
  · have ha : ∀j:ℕ,1/2-z≠-(j:ℝ) := by
      intro j hj
      have hjm : j<m := by exact_mod_cast (show (j:ℝ)<m by linarith)
      apply hroot
      refine ⟨j,Finset.mem_range.mpr hjm,?_⟩
      unfold meshNode
      dsimp [z] at hj
      have hnum : 2*(j:ℝ)+1=(u+1)*(m:ℝ) := by nlinarith
      rw [hnum,mul_div_cancel_right₀ _ hm'.ne']
      ring
    have hga : Real.Gamma (1/2-z)≠0 := Real.Gamma_ne_zero ha
    have hgb : Real.Gamma (z+1/2)≠0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
    have hrefl := Real.Gamma_mul_Gamma_one_sub (1/2-z)
    rw [show 1-(1/2-z)=z+1/2 by ring] at hrefl
    have hsin : Real.sin (Real.pi*(1/2-z))=Real.cos (Real.pi*z) := by
      rw [show Real.pi*(1/2-z)=Real.pi/2-Real.pi*z by ring]
      simp [Real.sin_sub]
    rw [hsin] at hrefl
    have hcos : Real.cos (Real.pi*z)≠0 := by
      intro he
      rw [he,div_zero] at hrefl
      exact mul_ne_zero hga hgb hrefl
    have hprod := gamma_shift_product (1/2-z) m (by
      intro j hj he
      exact ha j (by linarith))
    rw [mesh_scaled_product m hm u]
    have he : (∏j∈Finset.range m,(1/2-z+(j:ℝ)))=
        Real.Gamma (z+1/2)*Real.Gamma ((m:ℝ)-z+1/2)*Real.cos (Real.pi*z)/Real.pi := by
      have harg : 1/2-z+(m:ℝ)=(m:ℝ)-z+1/2 := by ring
      rw [harg] at hprod
      have hh := (eq_div_iff hcos).mp hrefl
      apply mul_left_cancel₀ hga
      calc
        _ = Real.Gamma ((m:ℝ)-z+1/2) := hprod.symm
        _ = Real.Gamma ((m:ℝ)-z+1/2)*(Real.pi/Real.pi) := by
          rw [div_self Real.pi_ne_zero, mul_one]
        _ = Real.Gamma ((m:ℝ)-z+1/2)*
            ((Real.Gamma (1/2-z)*Real.Gamma (z+1/2)*Real.cos (Real.pi*z))/Real.pi) := by
          rw [hh]
        _ = _ := by ring
    rw [he]
    have hzB : (m:ℝ)-z+1/2=(m:ℝ)*(1-u)/2+1/2 := by dsimp [z]; ring
    rw [hzB]
    dsimp [z]
    ring

private theorem mul_log_scaled (c x : ℝ) (hc : 0<c) :
    (c*x)*Real.log (c*x)=c*x*Real.log c+c*x*Real.log x := by
  by_cases hx : x=0
  · simp [hx]
  · rw [Real.log_mul hc.ne' hx]; ring

/-- Exact formula, including endpoints.  The auxiliary mesh is chosen by the
 proof and imposes no condition on the original interpolation nodes. -/
theorem meshPolynomial_exact (m : ℕ) (hm : 0<m) (u : ℝ) (hu : u∈Icc (-1:ℝ) 1) :
    (meshPolynomial m).eval u=
      2*(-1:ℝ)^m*Real.exp ((m:ℝ)*(externalField u-1))*meshAmplitude m u*
        Real.cos (Real.pi*(m:ℝ)*(1+u)/2) := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  let a := (m:ℝ)*(1+u)/2
  let b := (m:ℝ)*(1-u)/2
  have hup : 0≤1+u := by linarith [hu.1]
  have hum : 0≤1-u := by linarith [hu.2]
  have ha : 0≤a := by dsimp [a]; positivity
  have hb : 0≤b := by dsimp [b]; positivity
  have hsum : a+b=m := by dsimp [a,b]; ring
  have hlogs : a*Real.log a+b*Real.log b=
      (m:ℝ)*Real.log ((m:ℝ)/2)+(m:ℝ)*externalField u := by
    have h0 := mul_log_scaled ((m:ℝ)/2) (1+u) (by positivity)
    have h1 := mul_log_scaled ((m:ℝ)/2) (1-u) (by positivity)
    dsimp [a,b]
    rw [show (m:ℝ)*(1+u)/2=((m:ℝ)/2)*(1+u) by ring,
      show (m:ℝ)*(1-u)/2=((m:ℝ)/2)*(1-u) by ring,h0,h1]
    unfold externalField
    ring
  have he : Real.exp ((m:ℝ)*(externalField u-1))*
      Real.exp (a-a*Real.log a)*Real.exp (b-b*Real.log b)=(2/(m:ℝ))^m := by
    rw [←Real.exp_add,←Real.exp_add]
    have harg : (m:ℝ)*(externalField u-1)+(a-a*Real.log a)+(b-b*Real.log b)=
        -(m:ℝ)*Real.log ((m:ℝ)/2) := by linarith [hlogs,hsum]
    rw [harg,neg_mul,Real.exp_neg,Real.exp_nat_mul,
      Real.exp_log (show 0<(m:ℝ)/2 by positivity),←inv_pow]
    congr 1
    field_simp [hm'.ne']
  rw [mesh_gamma_formula m hm u hu]
  unfold meshAmplitude gammaAmplitude
  change _=2*(-1:ℝ)^m*Real.exp ((m:ℝ)*(externalField u-1))*
    ((Real.Gamma (a+1/2)*Real.exp (a-a*Real.log a)/Real.sqrt (2*Real.pi))*
     (Real.Gamma (b+1/2)*Real.exp (b-b*Real.log b)/Real.sqrt (2*Real.pi)))*_
  have hsqrt : Real.sqrt (2*Real.pi)^2=2*Real.pi := Real.sq_sqrt (by positivity)
  have hsqrt_mul : Real.sqrt (2*Real.pi)*Real.sqrt (2*Real.pi)=2*Real.pi := by
    simpa only [pow_two] using hsqrt
  rw [div_mul_div_comm, hsqrt_mul, ←he]
  dsimp only [a,b]
  field_simp [Real.pi_ne_zero]

/-- A general exact cardinal identity, proved by factoring the nodal polynomial. -/
theorem basis_derivative_identity (s : Finset ℕ) (v : ℕ→ℝ)
    (hv : Set.InjOn v s) (j : ℕ) (hj : j∈s) (u : ℝ) :
    (u-v j)*(∏i∈s,(Polynomial.X-Polynomial.C (v i))).derivative.eval (v j)*
      (Lagrange.basis s v j).eval u =
      (∏i∈s,(Polynomial.X-Polynomial.C (v i))).eval u := by
  have hfactor : (∏i∈s,(Polynomial.X-Polynomial.C (v i)))=
      (Polynomial.X-Polynomial.C (v j))*∏i∈s.erase j,(Polynomial.X-Polynomial.C (v i)) := by
    rw [←Finset.mul_prod_erase s (fun i => Polynomial.X-Polynomial.C (v i)) hj]
  have hd : (∏i∈s,(Polynomial.X-Polynomial.C (v i))).derivative.eval (v j)=
      ∏i∈s.erase j,(v j-v i) := by
    rw [hfactor,Polynomial.derivative_mul]
    simp [Polynomial.eval_prod]
  have hn : ∏i∈s.erase j,(v j-v i)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (fun he => (Finset.mem_erase.mp hi).1
      (hv (Finset.mem_erase.mp hi).2 hj he.symm))
  rw [hd,hfactor,Polynomial.eval_mul,Lagrange.basis]
  simp only [Lagrange.basisDivisor,Polynomial.eval_prod,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_sub,Polynomial.eval_X]
  rw [Finset.prod_mul_distrib,Finset.prod_inv_distrib]
  field_simp [hn]

private theorem meshAmplitude_differentiable (m : ℕ) (hm : 0<m) (u : ℝ) (hu : |u|<1) :
    DifferentiableAt ℝ (meshAmplitude m) u := by
  have hup : 0<1+u := by linarith [(abs_lt.mp hu).1]
  have hum : 0<1-u := by linarith [(abs_lt.mp hu).2]
  have h0 : 0<(m:ℝ)*(1+u)/2 := by
    positivity
  have h1 : 0<(m:ℝ)*(1-u)/2 := by
    positivity
  unfold meshAmplitude gammaAmplitude
  fun_prop (disch := first | positivity | intro n; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

theorem meshPolynomial_derivative_at_node (m j : ℕ) (hm : 0<m) (hj : j<m) :
    (meshPolynomial m).derivative.eval (meshNode m j)=
      -((-1:ℝ)^m*(-1:ℝ)^j)*(Real.pi*m)*
        Real.exp ((m:ℝ)*(externalField (meshNode m j)-1))*meshAmplitude m (meshNode m j) := by
  have hm' : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  let τ := meshNode m j
  have hτ := meshNode_mem m j hm hj
  have heq : (fun u => (meshPolynomial m).eval u) =ᶠ[𝓝 τ]
      fun u => 2*(-1:ℝ)^m*Real.exp ((m:ℝ)*(externalField u-1))*meshAmplitude m u*
        Real.cos (Real.pi*(m:ℝ)*(1+u)/2) := by
    filter_upwards [Ioo_mem_nhds (abs_lt.mp hτ).1 (abs_lt.mp hτ).2] with u hu
    exact meshPolynomial_exact m hm u ⟨hu.1.le,hu.2.le⟩
  have hphase : Real.pi*(m:ℝ)*(1+τ)/2=(j:ℝ)*Real.pi+Real.pi/2 := by
    dsimp [τ,meshNode]; field_simp [hm']; ring
  have hcos : Real.cos (Real.pi*(m:ℝ)*(1+τ)/2)=0 := by rw [hphase]; simp [Real.cos_add]
  have hsin : Real.sin (Real.pi*(m:ℝ)*(1+τ)/2)=(-1:ℝ)^j := by
    rw [hphase]
    simp [Real.sin_add,Real.cos_nat_mul_pi]
  have hfirst : DifferentiableAt ℝ
      (fun u => 2*(-1:ℝ)^m*Real.exp ((m:ℝ)*(externalField u-1))*meshAmplitude m u) τ := by
    exact (((differentiableAt_const (2*(-1:ℝ)^m)).mul
      (((externalField_derivative (abs_lt.mp hτ)).sub_const 1).const_mul (m:ℝ)).differentiableAt.exp).mul
        (meshAmplitude_differentiable m hm τ hτ))
  have hlast : HasDerivAt (fun u:ℝ => Real.cos (Real.pi*(m:ℝ)*(1+u)/2))
      (-Real.sin (Real.pi*(m:ℝ)*(1+τ)/2)*(Real.pi*m/2)) τ := by
    convert! (Real.hasDerivAt_cos _).comp τ
      (((hasDerivAt_id τ).const_add 1).const_mul (Real.pi*m) |>.div_const 2) using 1
    dsimp only [id_eq]
    ring
  have hd := hfirst.hasDerivAt.mul hlast
  have hdeq := (hd.congr_of_eventuallyEq heq).deriv
  rw [Polynomial.deriv] at hdeq
  rw [hcos,hsin] at hdeq
  simpa [τ] using (hdeq.trans (by ring))

/-- The cardinal kernel is sinc times a positive amplitude ratio, exactly. -/
theorem meshKernel_exact (m j : ℕ) (hm : 0<m) (hj : j<m)
    (u : ℝ) (hu : u∈Icc (-1:ℝ) 1) :
    Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))*(meshBasis m j).eval u=
      cardinalSinc ((m:ℝ)*(u-meshNode m j)/2)*meshAmplitude m u/meshAmplitude m (meshNode m j) := by
  have hm' : (m:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hm
  have hτ := meshNode_mem m j hm hj
  have hτp : 0<1+meshNode m j := by linarith [(abs_lt.mp hτ).1]
  have hτm : 0<1-meshNode m j := by linarith [(abs_lt.mp hτ).2]
  have hA : 0<meshAmplitude m (meshNode m j) := by
    unfold meshAmplitude
    exact mul_pos (gammaAmplitude_pos _ (by positivity))
      (gammaAmplitude_pos _ (by positivity))
  by_cases heq : u=meshNode m j
  · subst u
    simp [meshBasis,Lagrange.eval_basis_self (meshNode_injective m hm).injOn
      (Finset.mem_range.mpr hj),cardinalSinc,hA.ne']
  · have hp := basis_derivative_identity (Finset.range m) (meshNode m)
      (meshNode_injective m hm).injOn j (Finset.mem_range.mpr hj) u
    change (u-meshNode m j)*(meshPolynomial m).derivative.eval (meshNode m j)*
      (meshBasis m j).eval u=(meshPolynomial m).eval u at hp
    rw [meshPolynomial_derivative_at_node m j hm hj,meshPolynomial_exact m hm u hu] at hp
    have hphase : Real.pi*(m:ℝ)*(1+u)/2=
        Real.pi*((m:ℝ)*(u-meshNode m j)/2)+((j:ℝ)*Real.pi+Real.pi/2) := by
      unfold meshNode; field_simp [hm']; ring
    have hcos : Real.cos (Real.pi*(m:ℝ)*(1+u)/2)=
        -(-1:ℝ)^j*Real.sin (Real.pi*((m:ℝ)*(u-meshNode m j)/2)) := by
      rw [hphase,Real.cos_add]
      simp [Real.cos_add,Real.sin_add,Real.cos_nat_mul_pi]
      ring
    rw [hcos] at hp
    have hξ : Real.pi*((m:ℝ)*(u-meshNode m j)/2)≠0 := by
      exact mul_ne_zero Real.pi_ne_zero (div_ne_zero
        (mul_ne_zero (by exact_mod_cast hm.ne') (sub_ne_zero.mpr heq)) (by norm_num))
    rw [cardinalSinc,Real.sinc_of_ne_zero hξ]
    have hexp : Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))*
      Real.exp ((m:ℝ)*(externalField u-1))=
      Real.exp ((m:ℝ)*(externalField (meshNode m j)-1)) := by
      rw [←Real.exp_add]; congr 1; ring
    let D := (u-meshNode m j)*(Real.pi*(m:ℝ))*meshAmplitude m (meshNode m j)
    have hD : D≠0 := mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr heq) (mul_ne_zero Real.pi_ne_zero hm')) hA.ne'
    have hsign : -((-1:ℝ)^m*(-1:ℝ)^j)≠0 := neg_ne_zero.mpr
      (mul_ne_zero (pow_ne_zero m (by norm_num)) (pow_ne_zero j (by norm_num)))
    have hp' : D*Real.exp ((m:ℝ)*(externalField (meshNode m j)-1))*(meshBasis m j).eval u=
        2*Real.exp ((m:ℝ)*(externalField u-1))*meshAmplitude m u*
          Real.sin (Real.pi*((m:ℝ)*(u-meshNode m j)/2)) := by
      apply mul_left_cancel₀ hsign
      calc
        _ = (u-meshNode m j)*
            (-((-1:ℝ)^m*(-1:ℝ)^j)*(Real.pi*m)*
              Real.exp ((m:ℝ)*(externalField (meshNode m j)-1))*meshAmplitude m (meshNode m j))*
            (meshBasis m j).eval u := by dsimp [D]; ring
        _ = 2*(-1:ℝ)^m*Real.exp ((m:ℝ)*(externalField u-1))*meshAmplitude m u*
            (-(-1:ℝ)^j*Real.sin (Real.pi*((m:ℝ)*(u-meshNode m j)/2))) := hp
        _ = _ := by ring
    have hmain : D*(Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))*
        (meshBasis m j).eval u)=
        2*meshAmplitude m u*Real.sin (Real.pi*((m:ℝ)*(u-meshNode m j)/2)) := by
      apply mul_left_cancel₀ (Real.exp_ne_zero ((m:ℝ)*(externalField (meshNode m j)-1)))
      calc
        _ = Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))*
            (D*Real.exp ((m:ℝ)*(externalField (meshNode m j)-1))*(meshBasis m j).eval u) := by ring
        _ = Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))*
            (2*Real.exp ((m:ℝ)*(externalField u-1))*meshAmplitude m u*
              Real.sin (Real.pi*((m:ℝ)*(u-meshNode m j)/2))) := by rw [hp']
        _ = (Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))*
            Real.exp ((m:ℝ)*(externalField u-1)))*
            (2*meshAmplitude m u*Real.sin (Real.pi*((m:ℝ)*(u-meshNode m j)/2))) := by ring
        _ = _ := by rw [hexp]
    calc
      _ = (2*meshAmplitude m u*Real.sin (Real.pi*((m:ℝ)*(u-meshNode m j)/2)))/D :=
        (eq_div_iff hD).mpr (by rw [mul_comm]; exact hmain)
      _ = _ := by
        dsimp [D]
        field_simp [hm',hA.ne',Real.pi_ne_zero,sub_ne_zero.mpr heq]

end Erdos1152.V5
