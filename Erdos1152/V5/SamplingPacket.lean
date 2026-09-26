import Erdos1152.V5.FiniteSampling

noncomputable section
open scoped Topology Real
open Complex MeasureTheory Set Filter
namespace Erdos1152.V5

/-- All finite truncation constants are selected before the function, grid phase,
 or center.  The finite coefficients themselves are given by `correctedSample`. -/
theorem uniform_corrected_sampling
    (C σ t₀ ε : ℝ) (hC : 0<C) (ht₀ : 0<t₀) (ht₁ : t₀≤1)
    (hσ : σ<Real.pi*t₀) (hε : 0<ε) :
    ∃N:ℕ,1≤N ∧ ∃T K:ℝ,0<T ∧ 0<K ∧
      ∀t θ:ℝ,t₀≤t→t≤1→|θ|≤1/2→
      ∀g:ℂ→ℂ,Differentiable ℂ g→(∀x:ℝ,(g x).im=0)→
      (∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)→
      ∃c:ℤ→ℝ,
        (∀j∈symmetricIndices N,|samplePoint t θ j|≤T) ∧
        (∑j∈symmetricIndices N,realSign j*c j)=0 ∧
        (∑j∈symmetricIndices N,realSign j*samplePoint t θ j*c j)=0 ∧
        (∀ξ:ℝ,|finiteSincSum t θ N c ξ-(g ξ).re|≤ε) ∧
        (∀ξ:ℝ,2*T≤|ξ|→|finiteSincSum t θ N c ξ|≤K/|ξ|^3) := by
  let A := 16*C+correctionBudget C t₀
  have hA : 0<A := by dsimp [A,correctionBudget]; positivity
  have hlim := samplingTail_tendsto.const_mul A
  simp only [mul_zero] at hlim
  have hsmall : ∀ᶠN in atTop,A*samplingTail N<ε := by
    simpa using hlim.eventually_lt_const hε
  obtain ⟨N,hN,hNerr⟩ := (Filter.eventually_ge_atTop 1 |>.and hsmall).exists
  let T := ((N:ℝ)+2)/t₀
  let W := ∑'j:ℤ,latticeWeight j
  let D := ((2*N+1:ℕ):ℝ)*(C+correctionBudget C t₀*W)*T^2
  let K := 2*D/(Real.pi*t₀)
  have hT : 0<T := by dsimp [T]; positivity
  have hW : 0≤W := tsum_nonneg (fun j => latticeWeight_nonneg j)
  have hD : 0<D := by dsimp [D,correctionBudget]; positivity
  have hK : 0<K := by dsimp [K]; positivity
  refine ⟨N,hN,T,K,hT,hK,?_⟩
  intro t θ ht ht1 hθ g hgd hreal hg
  let c := correctedSample g t θ N
  have htpos := ht₀.trans_le ht
  have hv : ∀j∈symmetricIndices N,|samplePoint t θ j|≤T := by
    intro j hj
    have hjabs : |(j:ℝ)|≤N := by
      have hh := Finset.mem_Icc.mp hj
      exact abs_le.mpr ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2⟩
    have hadd : |(j:ℝ)+θ|≤(N:ℝ)+2 := (abs_add_le _ _).trans (by linarith)
    unfold samplePoint T
    rw [abs_div,abs_of_pos htpos]
    exact div_le_div₀ (by positivity) hadd ht₀ ht
  have htail : samplingTail N≤W := by
    dsimp [samplingTail,W]
    exact sub_le_self _ (Finset.sum_nonneg (fun j hj => latticeWeight_nonneg j))
  have hcorr : |correctionLeft g t θ N|+|correctionRight g t θ N|≤
      correctionBudget C t₀*W := by
    apply (correction_bound g hgd C σ t₀ t θ hC.le ht₀ ht ht1 hθ hσ hg N).trans
    exact mul_le_mul_of_nonneg_left htail (by dsimp [correctionBudget]; positivity)
  have hc : ∀j,|c j|≤C+correctionBudget C t₀*W := by
    intro j
    have hsample : |realSamples g t θ j|≤C := by
      apply (Complex.abs_re_le_norm _).trans
      have hb := hg (samplePoint t θ j:ℂ)
      simp only [Complex.ofReal_im,abs_zero,mul_zero,Real.exp_zero,mul_one] at hb
      apply hb.trans
      apply div_le_self hC.le
      exact one_le_pow₀ (by linarith [norm_nonneg (samplePoint t θ j : ℂ)] : 1≤1+‖(samplePoint t θ j:ℂ)‖)
    dsimp [c,correctedSample]
    apply (abs_add_le _ _).trans
    by_cases hj0 : j=0
    · simp only [if_pos hj0]
      linarith [abs_nonneg (correctionRight g t θ N)]
    · by_cases hj1 : j=1
      · simp only [if_neg hj0,if_pos hj1,abs_neg]
        linarith [abs_nonneg (correctionLeft g t θ N)]
      · simp only [if_neg hj0,if_neg hj1,abs_zero,add_zero]
        linarith [abs_nonneg (correctionLeft g t θ N),abs_nonneg (correctionRight g t θ N)]
  have hmoment2 : (∑j∈symmetricIndices N,|c j| *(samplePoint t θ j)^2)≤D := by
    have hterm : ∀j∈symmetricIndices N,|c j| *(samplePoint t θ j)^2≤
        (C+correctionBudget C t₀*W)*T^2 := by
      intro j hj
      apply mul_le_mul (hc j)
      · rw [← sq_abs (samplePoint t θ j)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hv j hj) 2
      · exact sq_nonneg _
      · dsimp [correctionBudget]
        positivity
    have hh := Finset.sum_le_sum hterm
    have hcard : (symmetricIndices N).card=2*N+1 := by
      simp only [symmetricIndices, Int.card_Icc]
      omega
    simpa [D,hcard,mul_assoc] using hh
  obtain ⟨hm0,hm1⟩ := corrected_moments g t θ htpos.ne' N hN
  refine ⟨c,hv,hm0,hm1,?_,?_⟩
  · intro ξ
    exact (corrected_sampling_approximation g hgd hreal C σ t₀ t θ hC.le ht₀ ht ht1
      hθ hσ hg N hN ξ).trans hNerr.le
  · intro ξ hξ
    have he := finite_sinc_cubic_tail t θ htpos N c hm0 hm1 T hT hv ξ hξ
    apply he.trans
    have hden : 0 < |ξ|^3 := by
      have hx : 0 < |ξ| := by linarith
      exact pow_pos hx _
    apply div_le_div_of_nonneg_right _ hden.le
    dsimp [K]
    calc
      (2/(Real.pi*t))*(∑j∈symmetricIndices N,|c j| *(samplePoint t θ j)^2)
        ≤(2/(Real.pi*t₀))*D := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
              (mul_le_mul_of_nonneg_left ht Real.pi_pos.le)
          · exact hmoment2
          · exact Finset.sum_nonneg (fun j hj => mul_nonneg (abs_nonneg _) (sq_nonneg _))
          · positivity
      _=2*D/(Real.pi*t₀) := by ring

end Erdos1152.V5
