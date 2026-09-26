import Erdos1152.V5.TrigExtension

/-!
Actual local Bernstein functions from finite trigonometric interpolation.
This is the finite version of the Olevskii--Ulanovskii argument (OWP2013-16,
Theorem 3* and its Privalov proof).  Using fixed parameters depending on `B`
avoids formalizing the infinite periodic-set density theorem.  It does not
change the original interpolation nodes or assume a common separation bound.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real Topology
open MeasureTheory Set Finset Filter
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private theorem fourth_tail_budget {M γ q d : ℝ}
    (hM : 1≤M) (hγ : 0<γ) (hq : M≤γ*q) (hd : q≤|d|) :
    M*Real.sinc (γ*d)^4≤1 := by
  have hq0 : 0<q := by nlinarith
  have hd0 : d≠0 := by intro h; simp [h] at hd; linarith
  have hb := sinc_fourth_tail hγ hd0
  have hx : 1≤γ*|d| := by nlinarith
  have hm : M≤γ*|d| := by nlinarith
  have hp : γ*|d|≤(γ*|d|)^4 := by
    nlinarith [sq_nonneg (γ*|d|-1),sq_nonneg ((γ*|d|)^2-1)]
  calc
    M*Real.sinc (γ*d)^4≤M*(1/(γ*|d|))^4 :=
      mul_le_mul_of_nonneg_left hb (by linarith)
    _≤1 := by
      rw [div_pow,one_pow,mul_one_div,div_le_one (by positivity)]
      exact hm.trans hp

/-- Complete finite-node Bernstein conclusion, including the whole exterior
`|x| ≥ ρ`, a uniform positive-length peak interval, and a complex exponential
bound.  All constants precede the arbitrary finite node set. -/
theorem local_bernstein_exists (B : ℝ) (hB : 1<B) :
    ∃ρ : ℕ,∃σ M ℓ K : ℝ,
      0<ρ ∧ 0<σ ∧ σ<Real.pi ∧ 0<M ∧ 0<ℓ ∧ 0<K ∧
      ∀Λ : Finset ℝ,(∀x∈Λ,x∈Icc (-(ρ:ℝ)) ρ)→Λ.card≤2*ρ+1→
      ∃g : ℂ→ℂ,∃a b : ℝ,
        Differentiable ℂ g ∧ (∀x:ℝ,(g x).im=0) ∧
        (∀x:ℝ,‖g x‖≤M) ∧
        (∀x∈Λ,‖g x‖≤1) ∧ (∀x:ℝ,(ρ:ℝ)≤|x|→‖g x‖≤1) ∧
        a<b ∧ b-a=ℓ ∧ Icc a b⊆Icc (-(ρ:ℝ)) ρ ∧
        (∀x∈Icc a b,2*B≤(g x).re) ∧
        (∀z:ℂ,‖g z‖≤K*Real.exp (σ*|z.im|)) := by
  let M : ℝ := 8*B
  have hM : 1≤M := by dsimp [M]; linarith
  have hM0 : 0<M := by linarith
  obtain ⟨A,hA,hheight⟩ := exists_harmonicHeight_ge (3*probeNormalization*M)
  have hsampling : M≤harmonicHeight A/(3*probeNormalization) := by
    rw [le_div_iff₀ (mul_pos (by norm_num) probeNormalization_pos)]
    nlinarith
  let γ := localizationGamma A
  have hγ : 0<γ := (localization_gap A).2
  obtain ⟨q,hq⟩ := exists_nat_gt (max 1 (M/γ))
  have hq0 : 0<q := by
    have hqpos : (0:ℝ)<q := lt_trans zero_lt_one
      (lt_of_le_of_lt (le_max_left _ _) hq)
    exact_mod_cast hqpos
  have hqM : M≤γ*q := by
    have h := lt_of_le_of_lt (le_max_right 1 (M/γ)) hq
    rw [div_lt_iff₀ hγ] at h
    nlinarith
  let k := localizationDegree A q
  let ρ := localizationRadius A q
  let R := localizationInner A q
  let σ := localizationBandwidth A+4*γ
  have hR : 0<R := by dsimp [R,localizationInner]; positivity
  have hρ : 0<ρ := by dsimp [ρ,localizationRadius]; omega
  have hmargin : (ρ:ℝ)-R=q := localization_margin A q
  have hσ0 : 0<σ := by
    dsimp [σ,localizationBandwidth]
    positivity
  have hσπ : σ<Real.pi := by
    have hg := (localization_gap A).1
    dsimp [σ,γ] at *
    linarith [(localization_gap A).2]
  let D : ℝ := (2*k+1:ℕ)*M*(Real.pi*k/R)
  have hD : 0≤D := by dsimp [D]; positivity
  obtain ⟨η,hη,hηs⟩ := exists_sinc_fourth_near_one
  let δ : ℝ := min ((q:ℝ)/2) (min (M/(4*(D+1))) (η/(2*γ)))
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδq : δ≤(q:ℝ)/2 := min_le_left _ _
  have hδD : D*δ≤M/4 := by
    have hb : δ≤M/(4*(D+1)) := (min_le_right _ _).trans (min_le_left _ _)
    have hb' := (le_div_iff₀ (by positivity : 0<4*(D+1))).mp hb
    nlinarith
  have hδγ : γ*δ≤η := by
    have hb : δ≤η/(2*γ) := (min_le_right _ _).trans (min_le_right _ _)
    have hb' := (le_div_iff₀ (by positivity : 0<2*γ)).mp hb
    nlinarith
  let K : ℝ := (2*k+1:ℕ)*M
  refine ⟨ρ,σ,M,2*δ,K,hρ,hσ0,hσπ,hM0,by positivity,by dsimp [K]; positivity,?_⟩
  intro Λ hΛ hΛcard
  let θ : ℝ→FourierCircle := fun x => ((Real.pi*x/R:ℝ):FourierCircle)
  let Γ := Λ.image θ
  have hΓ : Γ.card≤2*localizationRadius A q+1 :=
    (Finset.card_image_le).trans hΛcard
  obtain ⟨P,t₀,hP,hP0,hPreal,hPnorm,hPnodes⟩ :=
    real_trig_sampling A q hA hq0 Γ hΓ M hM0 hsampling
  have hPn : ‖P‖≤M := (ContinuousMap.norm_le P hM0.le).mpr hPnorm
  let t := AddCircle.equivIco (2*Real.pi) (-Real.pi) t₀
  have ht : |(t:ℝ)|≤Real.pi := by
    have ht₁ := t.2.1
    have ht₂ := t.2.2
    rw [abs_le]
    constructor <;> linarith
  have htc : ((t:ℝ):FourierCircle)=t₀ :=
    (AddCircle.equivIco (2*Real.pi) (-Real.pi)).symm_apply_apply _
  let u₀ : ℝ := R*(t:ℝ)/Real.pi
  have hu₀ : |u₀|≤R := by
    dsimp [u₀]
    rw [abs_div,abs_mul,abs_of_pos hR,abs_of_pos Real.pi_pos,
      div_le_iff₀ Real.pi_pos]
    nlinarith
  have hθu : θ u₀=t₀ := by
    rw [←htc]
    congr 1
    dsimp [θ,u₀]
    field_simp
  let F := trigExtension k R P
  have hFreal (x : ℝ) : F x=P (θ x) := trigExtension_real k R P hP x
  have hFu : F u₀=(M:ℂ) := by rw [hFreal,hθu,hP0]
  have hFnorm (x : ℝ) : ‖F x‖≤M := by rw [hFreal]; exact hPnorm _
  have hFlipschitz (x : ℝ) : ‖F x-F u₀‖≤D*|x-u₀| := by
    apply (trigExtension_real_lipschitz k R hR P x u₀).trans
    dsimp [D]
    gcongr
  let g : ℂ→ℂ := fun z => F z * entireSinc ((γ:ℂ)*(z-u₀))^4
  have greal (x : ℝ) : g x=F x*(Real.sinc (γ*(x-u₀))^4:ℝ) := by
    dsimp [g]
    rw [show (γ:ℂ)*((x:ℂ)-(u₀:ℂ))=((γ*(x-u₀):ℝ):ℂ) by push_cast; rfl,
      entireSinc_real]
    norm_cast
  have gnorm (x : ℝ) : ‖g x‖=‖F x‖*Real.sinc (γ*(x-u₀))^4 := by
    rw [greal,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (sinc_power_nonneg γ (x-u₀))]
  refine ⟨g,u₀-δ,u₀+δ,?_,?_,?_,?_,?_,by linarith,by ring,?_,?_,?_⟩
  · exact (trigExtension_entire k R P).mul
      ((differentiable_entireSinc.comp (by fun_prop)).pow 4)
  · intro x
    rw [greal,hFreal]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hPreal,
      mul_zero,zero_mul,add_zero]
  · intro x
    rw [gnorm]
    exact (mul_le_mul (hFnorm x) (sinc_power_le_one γ (x-u₀))
      (sinc_power_nonneg γ (x-u₀)) hM0.le).trans_eq (mul_one M)
  · intro x hx
    rw [gnorm,hFreal]
    exact (mul_le_mul (hPnodes _ (mem_image_of_mem θ hx))
      (sinc_power_le_one γ (x-u₀)) (sinc_power_nonneg γ (x-u₀)) zero_le_one).trans_eq
      (one_mul 1)
  · intro x hx
    rw [gnorm]
    have hd : (q:ℝ)≤|x-u₀| := by
      have htri := abs_sub_le x u₀
      have htri' : |x|≤|x-u₀|+|u₀| := by
        simpa using abs_add_le (x-u₀) u₀
      linarith
    exact (mul_le_mul_of_nonneg_right (hFnorm x) (sinc_power_nonneg γ (x-u₀))).trans
      (fourth_tail_budget hM hγ hqM hd)
  · intro x hx
    have hu := abs_le.mp hu₀
    simp only [Set.mem_Icc] at hx ⊢
    constructor <;> linarith
  · intro x hx
    have hxd : |x-u₀|≤δ := by
      rw [abs_le]
      constructor <;> linarith [hx.1,hx.2]
    have hdiff : |(F x).re-M|≤M/4 := by
      have hh := (Complex.abs_re_le_norm (F x-F u₀)).trans
        ((hFlipschitz x).trans (mul_le_mul_of_nonneg_left hxd hD))
      rw [hFu] at hh
      simpa using hh.trans hδD
    have hs : 1/2≤Real.sinc (γ*(x-u₀))^4 := by
      apply hηs
      rw [abs_mul,abs_of_pos hγ]
      exact (mul_le_mul_of_nonneg_left hxd hγ.le).trans hδγ
    rw [greal,Complex.mul_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    have hf : 3*M/4≤(F x).re := by linarith [(abs_le.mp hdiff).1]
    have hb := mul_le_mul hf hs (by norm_num : (0:ℝ)≤1/2) (by linarith : 0≤(F x).re)
    dsimp [M] at *
    nlinarith
  · intro z
    have ht := trigExtension_bound k R hR P z
    have hs := norm_entireSinc_le_exp ((γ:ℂ)*(z-u₀))
    have him : |((γ:ℂ)*(z-u₀)).im|=γ*|z.im| := by
      simp [abs_mul,abs_of_pos hγ]
    rw [him] at hs
    have hs4 := pow_le_pow_left₀ (norm_nonneg _) hs 4
    rw [←norm_pow,←Real.exp_nat_mul] at hs4
    dsimp [g]
    rw [norm_mul]
    calc
      _≤((2*k+1:ℕ)*M*Real.exp ((Real.pi*k/R)*|z.im|))*
          Real.exp (4*(γ*|z.im|)) := by
            apply mul_le_mul
            · exact ht.trans (by gcongr)
            · convert hs4 using 1 <;> norm_num
            · positivity
            · positivity
      _=K*Real.exp (σ*|z.im|) := by
        rw [mul_assoc,←Real.exp_add]
        dsimp [K,σ,k,R]
        rw [localization_frequency A q hq0]
        congr 2
        ring

end Erdos1152.V5
