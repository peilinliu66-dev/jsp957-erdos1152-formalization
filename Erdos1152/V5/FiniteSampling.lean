import Erdos1152.V5.SamplingFormula

noncomputable section
open scoped Topology Real
open Complex MeasureTheory Set Filter
namespace Erdos1152.V5

def realSign (j : ℤ) : ℝ := (-1:ℝ)^j
def realSamples (g : ℂ→ℂ) (t θ : ℝ) (j : ℤ) : ℝ := (g (samplePoint t θ j)).re

def sampleMoment (g : ℂ→ℂ) (t θ : ℝ) (N d : ℕ) : ℝ :=
  ∑j∈symmetricIndices N,realSign j*(samplePoint t θ j)^d*realSamples g t θ j

def correctionLeft (g : ℂ→ℂ) (t θ : ℝ) (N : ℕ) : ℝ :=
  (samplePoint t θ 1*sampleMoment g t θ N 0-sampleMoment g t θ N 1)/
    (samplePoint t θ 0-samplePoint t θ 1)
def correctionRight (g : ℂ→ℂ) (t θ : ℝ) (N : ℕ) : ℝ :=
  (sampleMoment g t θ N 1-samplePoint t θ 0*sampleMoment g t θ N 0)/
    (samplePoint t θ 0-samplePoint t θ 1)
def correctedSample (g : ℂ→ℂ) (t θ : ℝ) (N : ℕ) (j : ℤ) : ℝ :=
  realSamples g t θ j + if j=0 then correctionLeft g t θ N
    else if j=1 then -correctionRight g t θ N else 0

def finiteSincSum (t θ : ℝ) (N : ℕ) (c : ℤ→ℝ) (ξ : ℝ) : ℝ :=
  ∑j∈symmetricIndices N,c j*cardinalSinc (t*(ξ-samplePoint t θ j))

private theorem grid_gap (t θ : ℝ) (ht : t≠0) :
    samplePoint t θ 0-samplePoint t θ 1=-1/t := by
  dsimp [samplePoint]; norm_num; field_simp; ring

/-- The correction has two disjoint singleton supports. -/
private theorem correction_indicator_split (j : ℤ) (a b : ℝ) :
    (if j=0 then a else if j=1 then -b else 0) =
      (if j=0 then a else 0)+(if j=1 then -b else 0) := by
  by_cases hj : j=0
  · subst j
    norm_num
  · simp only [if_neg hj,zero_add]

theorem corrected_moments (g : ℂ→ℂ) (t θ : ℝ) (ht : t≠0)
    (N : ℕ) (hN : 1≤N) :
    (∑j∈symmetricIndices N,realSign j*correctedSample g t θ N j)=0 ∧
    (∑j∈symmetricIndices N,realSign j*samplePoint t θ j*correctedSample g t θ N j)=0 := by
  have ha : samplePoint t θ 0-samplePoint t θ 1≠0 := by
    rw [grid_gap t θ ht]; exact div_ne_zero (by norm_num) ht
  have h0 : (0:ℤ)∈symmetricIndices N := by simp [symmetricIndices]
  have h1 : (1:ℤ)∈symmetricIndices N := by simp [symmetricIndices]; omega
  have hm0 : correctionLeft g t θ N+correctionRight g t θ N =
      -sampleMoment g t θ N 0 := by
    unfold correctionLeft correctionRight
    field_simp [ha]
    ring
  have hm1 : samplePoint t θ 0*correctionLeft g t θ N+
      samplePoint t θ 1*correctionRight g t θ N =-sampleMoment g t θ N 1 := by
    unfold correctionLeft correctionRight
    field_simp [ha]
    ring
  constructor
  · simp only [correctedSample,mul_add,Finset.sum_add_distrib,ite_add_ite]
    have hh : (∑j∈symmetricIndices N,realSign j*
        (if j=0 then correctionLeft g t θ N else if j=1 then -correctionRight g t θ N else 0))=
        correctionLeft g t θ N+correctionRight g t θ N := by
      simp only [correction_indicator_split,mul_add,Finset.sum_add_distrib]
      simp [mul_ite,h0,h1,realSign]
    rw [hh, hm0]
    simp only [sampleMoment, pow_zero, mul_one, add_neg_cancel]
  · simp only [correctedSample,mul_add,Finset.sum_add_distrib]
    have hh : (∑j∈symmetricIndices N,realSign j*samplePoint t θ j*
        (if j=0 then correctionLeft g t θ N else if j=1 then -correctionRight g t θ N else 0))=
        samplePoint t θ 0*correctionLeft g t θ N+
          samplePoint t θ 1*correctionRight g t θ N := by
      simp only [correction_indicator_split,mul_add,Finset.sum_add_distrib]
      simp [mul_ite,h0,h1,realSign]
    rw [hh, hm1]
    simp only [sampleMoment, pow_one, add_neg_cancel]

private theorem partial_moment_bound
    (g : ℂ→ℂ) (hgd : Differentiable ℂ g) (C σ t θ : ℝ)
    (hC : 0≤C) (ht : 0<t) (ht1 : t≤1) (hθ : |θ|≤1/2)
    (hσ : σ<Real.pi*t)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (N d : ℕ) (hd : d≤1) :
    |sampleMoment g t θ N d|≤16*C*samplingTail N := by
  have hm := hasSum_alternating_moment g hgd C σ t θ hC ht ht1 hθ hσ hg d hd
  have hb := norm_tsum_sub_symmetric_le (D := 16*C) (by positivity)
    (fun j => show ‖(-1:ℂ)^j*(samplePoint t θ j:ℂ)^d*g (samplePoint t θ j)‖≤_ by
      simpa [norm_mul,mul_assoc] using
        sample_moment_bound g C σ t θ hC ht ht1 hθ hg d (by omega) j) N
  rw [hm.tsum_eq,zero_sub,norm_neg] at hb
  apply le_trans _ hb
  have he : sampleMoment g t θ N d =
      (∑j∈symmetricIndices N,(-1:ℂ)^j*(samplePoint t θ j:ℂ)^d*g (samplePoint t θ j)).re := by
    unfold sampleMoment
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjc : (-1:ℂ)^j = (realSign j : ℂ) := by simp [realSign]
    rw [hjc, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    simp only [realSamples, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [he]
  exact Complex.abs_re_le_norm _

def correctionBudget (C t₀ : ℝ) : ℝ := 64*C*(1+2/t₀)

theorem correction_bound
    (g : ℂ→ℂ) (hgd : Differentiable ℂ g) (C σ t₀ t θ : ℝ)
    (hC : 0≤C) (ht₀ : 0<t₀) (ht : t₀≤t) (ht1 : t≤1) (hθ : |θ|≤1/2)
    (hσ : σ<Real.pi*t₀)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6) (N : ℕ) :
    |correctionLeft g t θ N|+|correctionRight g t θ N|≤
      correctionBudget C t₀*samplingTail N := by
  have htpos := ht₀.trans_le ht
  have htype : σ<Real.pi*t := hσ.trans_le (mul_le_mul_of_nonneg_left ht Real.pi_pos.le)
  have hM0 := partial_moment_bound g hgd C σ t θ hC htpos ht1 hθ htype hg N 0 (by norm_num)
  have hM1 := partial_moment_bound g hgd C σ t θ hC htpos ht1 hθ htype hg N 1 (by norm_num)
  have ha : |samplePoint t θ 0|≤2/t₀ := by
    simp only [samplePoint,Int.cast_zero,zero_add,abs_div,abs_of_pos htpos]
    apply (div_le_div₀ (by norm_num) (by linarith) ht₀ ht)
  have hb : |samplePoint t θ 1|≤2/t₀ := by
    have hn : |(1:ℝ)+θ|≤2 := (abs_add_le _ _).trans (by norm_num; linarith)
    simp only [samplePoint,Int.cast_one,abs_div,abs_of_pos htpos]
    exact div_le_div₀ (by norm_num) hn ht₀ ht
  have hgap : 1≤|samplePoint t θ 0-samplePoint t θ 1| := by
    rw [grid_gap t θ htpos.ne',abs_div,abs_neg,abs_one,abs_of_pos htpos]
    exact (le_div_iff₀ htpos).mpr (by simpa using ht1)
  have hl : |correctionLeft g t θ N|≤
      (2/t₀+1)*(16*C*samplingTail N) := by
    rw [correctionLeft,abs_div]
    apply (div_le_self (abs_nonneg _) hgap).trans
    apply (abs_sub _ _).trans
    rw [abs_mul]
    nlinarith [mul_le_mul hb hM0 (abs_nonneg _) (by positivity)]
  have hr : |correctionRight g t θ N|≤
      (2/t₀+1)*(16*C*samplingTail N) := by
    rw [correctionRight,abs_div]
    apply (div_le_self (abs_nonneg _) hgap).trans
    apply (abs_sub _ _).trans
    rw [abs_mul]
    nlinarith [mul_le_mul ha hM0 (abs_nonneg _) (by positivity)]
  unfold correctionBudget
  nlinarith [mul_nonneg (mul_nonneg hC
    (show 0 ≤ 1+2/t₀ by positivity)) (samplingTail_nonneg N)]

/-- Uniform approximation for the actual corrected finite coefficients. -/
theorem corrected_sampling_approximation
    (g : ℂ→ℂ) (hgd : Differentiable ℂ g) (hreal : ∀x:ℝ,(g x).im=0)
    (C σ t₀ t θ : ℝ) (hC : 0≤C) (ht₀ : 0<t₀) (ht : t₀≤t) (ht1 : t≤1)
    (hθ : |θ|≤1/2) (hσ : σ<Real.pi*t₀)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (N : ℕ) (hN : 1≤N) (ξ : ℝ) :
    |finiteSincSum t θ N (correctedSample g t θ N) ξ-(g ξ).re|≤
      (16*C+correctionBudget C t₀)*samplingTail N := by
  have htpos := ht₀.trans_le ht
  have htype : σ<Real.pi*t := hσ.trans_le (mul_le_mul_of_nonneg_left ht Real.pi_pos.le)
  have hs := hasSum_shannon g hgd C σ t θ hC htpos ht1 hθ htype hg ξ
  have hb := norm_tsum_sub_symmetric_le (D := 16*C) (by positivity)
    (fun j => show ‖g (samplePoint t θ j)*(cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ)‖≤_ by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_of_le_one_right (norm_nonneg _) (Real.abs_sinc_le_one _)).trans
      simpa using sample_moment_bound g C σ t θ hC htpos ht1 hθ hg 0 (by norm_num) j) N
  rw [hs.tsum_eq] at hb
  have hbase : |finiteSincSum t θ N (realSamples g t θ) ξ-(g ξ).re|≤16*C*samplingTail N := by
    have hh := Complex.abs_re_le_norm
      (g ξ-∑j∈symmetricIndices N,g (samplePoint t θ j)*(cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ))
    simp only [Complex.sub_re,Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,mul_zero,sub_zero] at hh
    rw [abs_sub_comm] at hh
    exact hh.trans hb
  have h0 : (0:ℤ)∈symmetricIndices N := by simp [symmetricIndices]
  have h1 : (1:ℤ)∈symmetricIndices N := by simp [symmetricIndices]; omega
  have he : finiteSincSum t θ N (correctedSample g t θ N) ξ-
      finiteSincSum t θ N (realSamples g t θ) ξ =
      correctionLeft g t θ N*cardinalSinc (t*(ξ-samplePoint t θ 0))-
      correctionRight g t θ N*cardinalSinc (t*(ξ-samplePoint t θ 1)) := by
    simp only [finiteSincSum,correctedSample,correction_indicator_split,
      add_mul,Finset.sum_add_distrib]
    simp [ite_mul,h0,h1] <;> ring
  have hdiff : |finiteSincSum t θ N (correctedSample g t θ N) ξ-
      finiteSincSum t θ N (realSamples g t θ) ξ|≤correctionBudget C t₀*samplingTail N := by
    rw [he]
    apply (abs_sub _ _).trans
    simp only [abs_mul]
    apply le_trans _ (correction_bound g hgd C σ t₀ t θ hC ht₀ ht ht1 hθ hσ hg N)
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one _))
      (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one _))
  have htri := abs_sub_le
    (finiteSincSum t θ N (correctedSample g t θ N) ξ)
    (finiteSincSum t θ N (realSamples g t θ) ξ) (g ξ).re
  nlinarith

/-- The partial-fraction identity producing a cubic, absolutely summable tail. -/
theorem finite_sinc_cubic_tail (t θ : ℝ) (ht : 0<t) (N : ℕ) (c : ℤ→ℝ)
    (hm0 : (∑j∈symmetricIndices N,realSign j*c j)=0)
    (hm1 : (∑j∈symmetricIndices N,realSign j*samplePoint t θ j*c j)=0)
    (T : ℝ) (hT : 0<T) (hv : ∀j∈symmetricIndices N,|samplePoint t θ j|≤T)
    (ξ : ℝ) (hξ : 2*T≤|ξ|) :
    |finiteSincSum t θ N c ξ|≤
      (2/(Real.pi*t))*(∑j∈symmetricIndices N,|c j| *(samplePoint t θ j)^2)/|ξ|^3 := by
  have hξabs : 0 < |ξ| := lt_of_lt_of_le (by positivity : 0<2*T) hξ
  have hξ0 : ξ≠0 := abs_pos.mp hξabs
  have hsep (j : ℤ) (hj : j∈symmetricIndices N) :
      |ξ|/2≤|ξ-samplePoint t θ j| := by
    have hh := abs_sub_abs_le_abs_sub ξ (samplePoint t θ j)
    linarith [hv j hj]
  have hden (j : ℤ) (hj : j∈symmetricIndices N) : ξ-samplePoint t θ j≠0 := by
    apply abs_pos.mp
    exact lt_of_lt_of_le (by positivity) (hsep j hj)
  have hfrac (v : ℝ) (hv : ξ-v≠0) :
      1/(ξ-v)=1/ξ+v/ξ^2+v^2/(ξ^2*(ξ-v)) := by
    field_simp [hξ0,hv]; ring
  have hsinc (j : ℤ) (hj : j∈symmetricIndices N) :
      cardinalSinc (t*(ξ-samplePoint t θ j))=
        Real.sin (Real.pi*(t*ξ-θ))/(Real.pi*t)*realSign j/(ξ-samplePoint t θ j) := by
    have hgrid : t*samplePoint t θ j=(j:ℝ)+θ := by dsimp [samplePoint]; field_simp
    rw [cardinalSinc,Real.sinc_of_ne_zero
      (mul_ne_zero Real.pi_ne_zero (mul_ne_zero ht.ne' (hden j hj)))]
    have he : Real.pi*(t*(ξ-samplePoint t θ j))=Real.pi*(t*ξ-θ)-(j:ℝ)*Real.pi := by
      linear_combination -Real.pi*hgrid
    have hs : Real.sin (Real.pi*(t*(ξ-samplePoint t θ j))) =
        Real.sin (Real.pi*(t*ξ-θ))*realSign j := by
      rw [he, Real.sin_sub]
      simp only [Real.sin_int_mul_pi, mul_zero, sub_zero, Real.cos_int_mul_pi, realSign]
    rw [hs]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  let A := Real.sin (Real.pi*(t*ξ-θ))/(Real.pi*t)
  have hsum0 : (∑j∈symmetricIndices N,realSign j*c j/ξ)=0 := by
    rw [←Finset.sum_div,hm0,zero_div]
  have hsum1 : (∑j∈symmetricIndices N,
      realSign j*c j*samplePoint t θ j/ξ^2)=0 := by
    rw [←Finset.sum_div]
    have hh : (∑j∈symmetricIndices N,realSign j*c j*samplePoint t θ j)=0 := by
      convert hm1 using 1
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hh,zero_div]
  have heq : finiteSincSum t θ N c ξ=
      Real.sin (Real.pi*(t*ξ-θ))/(Real.pi*t*ξ^2)*
        ∑j∈symmetricIndices N,realSign j*c j*(samplePoint t θ j)^2/(ξ-samplePoint t θ j) := by
    calc
      _=A*∑j∈symmetricIndices N,realSign j*c j/(ξ-samplePoint t θ j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hsinc j hj]
        dsimp [A]
        ring
      _=A*((∑j∈symmetricIndices N,realSign j*c j/ξ)+
          (∑j∈symmetricIndices N,realSign j*c j*samplePoint t θ j/ξ^2)+
          (∑j∈symmetricIndices N,realSign j*c j*(samplePoint t θ j)^2/
            (ξ^2*(ξ-samplePoint t θ j)))) := by
        congr 1
        rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hh := congrArg (fun a:ℝ => realSign j*c j*a)
          (hfrac (samplePoint t θ j) (hden j hj))
        convert hh using 1 <;> ring
      _=A*(1/ξ^2)*(∑j∈symmetricIndices N,
          realSign j*c j*(samplePoint t θ j)^2/(ξ-samplePoint t θ j)) := by
        rw [hsum0,hsum1,zero_add,zero_add]
        rw [mul_assoc]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _=_ := by dsimp [A]; ring
  rw [heq,abs_mul,abs_div]
  have hb : |∑j∈symmetricIndices N,realSign j*c j*(samplePoint t θ j)^2/(ξ-samplePoint t θ j)|≤
      (2/|ξ|)*∑j∈symmetricIndices N,|c j| *(samplePoint t θ j)^2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simp only [abs_div,abs_mul,realSign,abs_zpow,abs_neg,abs_one,one_zpow,one_mul,abs_sq]
    have hh := div_le_div_of_nonneg_left
      (mul_nonneg (abs_nonneg (c j)) (sq_nonneg (samplePoint t θ j)))
      (by positivity) (hsep j hj)
    convert hh using 1 <;> field_simp <;> ring
  have hs := Real.abs_sin_le_one (Real.pi*(t*ξ-θ))
  simp only [abs_mul,abs_of_pos ht,abs_of_pos Real.pi_pos,abs_sq]
  apply le_trans (mul_le_mul (div_le_div_of_nonneg_right hs (by positivity)) hb
    (abs_nonneg _) (by positivity))
  apply le_of_eq
  rw [←sq_abs ξ]
  field_simp [Real.pi_ne_zero,ht.ne',hξabs.ne']
  <;> ring

end Erdos1152.V5
