import Erdos1152.V5.LocalBernstein

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
namespace Erdos1152.V5

private theorem exists_sinc_sixth_near_one : ∃η>0,∀x:ℝ,|x|≤η→1/2≤Real.sinc x^6 := by
  have hc := (Real.continuous_sinc.pow 6).continuousAt (x := 0)
  obtain ⟨η,hη,hcη⟩ := Metric.continuousAt_iff.mp hc (1/2) (by norm_num)
  refine ⟨η/2,by positivity,?_⟩
  intro x hx
  have hdist : dist x 0 < η := by
    simpa [Real.dist_eq] using hx.trans_lt (half_lt_self hη)
  have h := hcη hdist
  simp only [Pi.pow_apply,Real.sinc_zero,one_pow,Real.dist_eq] at h
  linarith [(abs_lt.mp h).1]

private theorem sixth_window_decay {ε : ℝ} (hε : 0<ε) (z : ℂ) :
    ‖entireSinc ((ε:ℂ)*z)^6‖≤
      (2/min 1 ε)^6 * Real.exp (6*ε*|z.im|)/(1+‖z‖)^6 := by
  let c := min 1 ε
  have hc : 0<c := lt_min (by norm_num) hε
  have hd : c*(1+‖z‖)≤1+ε*‖z‖ := by
    have h1 : c≤1 := min_le_left _ _
    have h2 : c≤ε := min_le_right _ _
    nlinarith [mul_le_mul_of_nonneg_right h2 (norm_nonneg z)]
  have hb := norm_entireSinc_decay ((ε:ℂ)*z)
  simp only [Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re,zero_mul,add_zero,
    abs_mul,abs_of_pos hε,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hb
  have hb' : ‖entireSinc ((ε:ℂ)*z)‖≤
      (2/c)*Real.exp (ε*|z.im|)/(1+‖z‖) := by
    apply hb.trans
    have hdn : 0<c*(1+‖z‖) := by positivity
    calc
      2*Real.exp (ε*|z.im|)/(1+ε*‖z‖)
          ≤2*Real.exp (ε*|z.im|)/(c*(1+‖z‖)) := by
            exact div_le_div_of_nonneg_left (by positivity) hdn hd
      _=(2/c)*Real.exp (ε*|z.im|)/(1+‖z‖) := by field_simp
  have hh := pow_le_pow_left₀ (norm_nonneg _) hb' 6
  rw [←norm_pow,div_pow,mul_pow,←Real.exp_nat_mul] at hh
  convert hh using 1 <;> congr 2 <;> ring

/-- The exact decay class used by the sampling and moment-correction construction.
The bandwidth includes the sixth-power window before the auxiliary mesh is chosen. -/
theorem local_bernstein_decay_exists (B : ℝ) (hB : 1<B) :
    ∃ρ : ℕ,∃σ M ℓ C : ℝ,
      0<ρ ∧ 0<σ ∧ σ<Real.pi ∧ 0<M ∧ 0<ℓ ∧ 0<C ∧
      ∀Λ : Finset ℝ,(∀x∈Λ,x∈Icc (-(ρ:ℝ)) ρ)→Λ.card≤2*ρ+1→
      ∃g : ℂ→ℂ,∃a b : ℝ,
        Differentiable ℂ g ∧ (∀x:ℝ,(g x).im=0) ∧
        (∀x:ℝ,‖g x‖≤M) ∧
        (∀x∈Λ,‖g x‖≤1) ∧ (∀x:ℝ,(ρ:ℝ)≤|x|→‖g x‖≤1) ∧
        a<b ∧ b-a=ℓ ∧ Icc a b⊆Icc (-(ρ:ℝ)) ρ ∧
        (∀x∈Icc a b,B≤(g x).re) ∧
        (∀z:ℂ,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6) := by
  obtain ⟨ρ,σ₀,M,ℓ,K,hρ,hσ₀,hσπ,hM,hℓ,hK,hdata⟩ := local_bernstein_exists B hB
  obtain ⟨η,hη,hηs⟩ := exists_sinc_sixth_near_one
  let ε := min ((Real.pi-σ₀)/12) (η/(2*(ρ+1)))
  have hε : 0<ε := by dsimp [ε]; positivity
  have hεσ : σ₀+6*ε<Real.pi := by
    have h := min_le_left ((Real.pi-σ₀)/12) (η/(2*(ρ+1)))
    dsimp [ε] at *
    linarith
  have hερ : ε*(ρ:ℝ)≤η := by
    have hh : ε≤η/(2*(ρ+1)) := min_le_right _ _
    have hh' := (le_div_iff₀ (by positivity : 0<2*((ρ:ℝ)+1))).mp hh
    nlinarith
  let C := K*(2/min 1 ε)^6
  refine ⟨ρ,σ₀+6*ε,M,ℓ,C,hρ,by positivity,hεσ,hM,hℓ,by dsimp [C]; positivity,?_⟩
  intro Λ hΛ hcard
  obtain ⟨g₀,a,b,hd,hr,hbound,hnodes,hext,hab,hbl,hsub,hpeak,hgrowth⟩ := hdata Λ hΛ hcard
  let g : ℂ→ℂ := fun z => g₀ z*entireSinc ((ε:ℂ)*z)^6
  have hreal (x : ℝ) : g x=g₀ x*(Real.sinc (ε*x)^6:ℝ) := by
    dsimp [g]
    rw [show (ε:ℂ)*(x:ℂ)=((ε*x:ℝ):ℂ) by push_cast; rfl,entireSinc_real]
    norm_cast
  have hs (x : ℝ) : 0≤Real.sinc (ε*x)^6 ∧ Real.sinc (ε*x)^6≤1 := by
    refine ⟨by positivity,?_⟩
    have hp := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sinc_le_one (ε*x)) 6
    have hp' : |Real.sinc (ε*x)^6| ≤ 1 := by
      simpa only [abs_pow,one_pow] using hp
    exact (le_abs_self _).trans hp'
  have hn (x : ℝ) : ‖g x‖≤‖g₀ x‖ := by
    rw [hreal,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hs x).1]
    exact mul_le_of_le_one_right (norm_nonneg _) (hs x).2
  refine ⟨g,a,b,hd.mul ((differentiable_entireSinc.comp (by fun_prop)).pow 6),?_,
    fun x=>(hn x).trans (hbound x),fun x hx=>(hn x).trans (hnodes x hx),
    fun x hx=>(hn x).trans (hext x hx),hab,hbl,hsub,?_,?_⟩
  · intro x
    rw [hreal]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hr,
      mul_zero,zero_mul,add_zero]
  · intro x hx
    have hxρ : |x|≤ρ := abs_le.mpr (hsub hx)
    have hw : 1/2≤Real.sinc (ε*x)^6 := by
      apply hηs
      rw [abs_mul,abs_of_pos hε]
      exact (mul_le_mul_of_nonneg_left hxρ hε.le).trans hερ
    rw [hreal,Complex.mul_re]
    simp only [Complex.ofReal_im,mul_zero,sub_zero,Complex.ofReal_re]
    have hp := hpeak x hx
    nlinarith [mul_le_mul hp hw (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤(g₀ x).re)]
  · intro z
    have hw := sixth_window_decay hε z
    dsimp [g]
    rw [norm_mul]
    calc
      _≤(K*Real.exp (σ₀*|z.im|))*
          ((2/min 1 ε)^6*Real.exp (6*ε*|z.im|)/(1+‖z‖)^6) :=
        mul_le_mul (hgrowth z) hw (norm_nonneg _) (by positivity)
      _=C*Real.exp ((σ₀+6*ε)*|z.im|)/(1+‖z‖)^6 := by
        dsimp [C]
        rw [add_mul,Real.exp_add]
        ring

end Erdos1152.V5
