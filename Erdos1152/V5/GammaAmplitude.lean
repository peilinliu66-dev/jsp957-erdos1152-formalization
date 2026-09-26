import Erdos1152.GammaIncrementBounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Topology.Algebra.Order.Floor

noncomputable section
open scoped Topology Real
open Real Set Filter
namespace Erdos1152.V5

def stirlingRemainder (x : ℝ) : ℝ :=
  Real.log (Real.Gamma (x+1))-(x+1/2)*Real.log x+x-Real.log (2*Real.pi)/2

def gammaAmplitude (a : ℝ) : ℝ :=
  Real.Gamma (a+1/2)*Real.exp (a-a*Real.log a)/Real.sqrt (2*Real.pi)

def meshAmplitude (m : ℕ) (u : ℝ) : ℝ :=
  gammaAmplitude ((m:ℝ)*(1+u)/2)*gammaAmplitude ((m:ℝ)*(1-u)/2)

private theorem log_lower (x : ℝ) (hx : 0<x) : 1-1/x≤Real.log x := by
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at h
  simpa [one_div] using (neg_le_neg h)

private theorem stirlingRemainder_nat (n : ℕ) (hn : 0<n) :
    stirlingRemainder n=Real.log (Stirling.stirlingSeq n)-Real.log (Real.sqrt Real.pi) := by
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  rw [stirlingRemainder,Real.Gamma_nat_eq_factorial,
    Stirling.log_stirlingSeq_formula,Real.log_sqrt Real.pi_pos.le,
    Real.log_mul (by norm_num : (2:ℝ)≠0) hn'.ne',
    Real.log_div hn'.ne' (Real.exp_ne_zero 1),Real.log_exp,
    Real.log_mul (by norm_num : (2:ℝ)≠0) Real.pi_ne_zero]
  ring

private theorem stirlingRemainder_nat_tendsto :
    Tendsto (fun n:ℕ => stirlingRemainder n) atTop (𝓝 0) := by
  have hs := (Real.continuousAt_log (by positivity : Real.sqrt Real.pi≠0)).tendsto.comp
    Stirling.tendsto_stirlingSeq_sqrt_pi
  have hh := hs.sub_const (Real.log (Real.sqrt Real.pi))
  simp only [sub_self] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (stirlingRemainder_nat n (by omega)).symm

/-- Uniform interpolation between consecutive factorial arguments. -/
theorem stirlingRemainder_fraction (n t : ℝ) (hn : 1≤n) (ht : t∈Icc 0 1) :
    |stirlingRemainder (n+t)-stirlingRemainder n|≤2/n := by
  have hn0 : 0<n := by linarith
  have ht0 : 0 ≤ t := ht.1
  have he := Erdos1152.logGamma_increment_error n t hn0 ht
  have hlogU : Real.log (1+t/n)≤t/n := by
    simpa using Real.log_le_sub_one_of_pos (show 0<1+t/n by positivity)
  have hlogL : t/(n+t)≤Real.log (1+t/n) := by
    have hl := log_lower (1+t/n) (by positivity)
    convert hl using 1
    field_simp
    ring
  have hidentity : stirlingRemainder (n+t)-stirlingRemainder n=
      (Real.log (Real.Gamma (n+1+t))-Real.log (Real.Gamma (n+1))-t*Real.log n)+
        t-(n+t+1/2)*Real.log (1+t/n) := by
    have hlog : Real.log (n+t)=Real.log n+Real.log (1+t/n) := by
      rw [←Real.log_mul hn0.ne' (by positivity)]
      congr 1
      field_simp
    unfold stirlingRemainder
    rw [hlog, show n + t + 1 = n + 1 + t by ring]
    ring
  rw [hidentity,abs_le]
  have hnt : 0<n+t := by linarith [ht.1]
  have hc : 0<n+t+1/2 := by linarith
  have hU := mul_le_mul_of_nonneg_left hlogU hc.le
  have hL := mul_le_mul_of_nonneg_left hlogL hc.le
  have hUeq : (n+t+1/2)*(t/n)=t+(t^2+t/2)/n := by field_simp; ring
  have hLeq : (n+t+1/2)*(t/(n+t))=t+t/(2*(n+t)) := by field_simp
  rw [hUeq] at hU
  rw [hLeq] at hL
  have hpoly : t^2+t/2≤2 := by nlinarith [ht.1,ht.2]
  have hsmall := div_le_div_of_nonneg_right hpoly hn0.le
  have hnonneg : 0≤t/(2*(n+t)) := by positivity
  have hinvle : 1/n≤2/n := div_le_div_of_nonneg_right (by norm_num) hn0.le
  constructor <;> nlinarith [he.1,he.2]

theorem stirlingRemainder_tendsto : Tendsto stirlingRemainder atTop (𝓝 0) := by
  have hf : Tendsto (fun x:ℝ => (⌊x⌋₊:ℕ)) atTop atTop := tendsto_nat_floor_atTop
  have hnat := stirlingRemainder_nat_tendsto.comp hf
  have hinv : Tendsto (fun x:ℝ => 2/(⌊x⌋₊:ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat 2).comp hf
  have herr : Tendsto (fun x:ℝ => stirlingRemainder x-stirlingRemainder (⌊x⌋₊:ℝ))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x:ℝ => 2/(⌊x⌋₊:ℝ))
    · filter_upwards [eventually_ge_atTop (2:ℝ)] with x hx
      have hn : 1≤⌊x⌋₊ := (Nat.le_floor_iff (by positivity)).mpr
        (by simpa only [Nat.cast_one] using (show (1 : ℝ) ≤ x by linarith))
      have hfloor : (⌊x⌋₊:ℝ)≤x := Nat.floor_le (by linarith)
      have hlt : x<(⌊x⌋₊:ℝ)+1 := Nat.lt_floor_add_one x
      simpa only [Real.norm_eq_abs,add_sub_cancel] using
        stirlingRemainder_fraction (⌊x⌋₊:ℝ) (x-⌊x⌋₊) (by exact_mod_cast hn)
          ⟨by linarith,by linarith⟩
    · exact hinv
  simpa using herr.add hnat

theorem gammaAmplitude_pos (a : ℝ) (ha : 0≤a) : 0<gammaAmplitude a := by
  unfold gammaAmplitude
  exact div_pos (mul_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.exp_pos _))
    (Real.sqrt_pos.mpr (by positivity))

private theorem scaled_log_tendsto :
    Tendsto (fun a:ℝ => a*Real.log (1-1/(2*a))) atTop (𝓝 (-1/2)) := by
  have ht0 : Tendsto (fun a:ℝ => -1/(2*a)) atTop (𝓝 0) := by
    have hi : Tendsto (fun a : ℝ => (-1 / 2 : ℝ) * a⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_inv_atTop_zero.const_mul (-1 / 2 : ℝ))
    convert hi using 1
    ext a
    ring
  have ht : Tendsto (fun a:ℝ => -1/(2*a)) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨ht0,?_⟩
    filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
    exact div_ne_zero (by norm_num) (mul_ne_zero (by norm_num) ha.ne')
  have hs := (Real.hasDerivAt_log one_ne_zero).tendsto_slope_zero.comp ht
  have hh := hs.const_mul (-1/2)
  simp only [inv_one, mul_one] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with a ha
  simp only [Function.comp_apply,Real.log_one,sub_zero,smul_eq_mul]
  rw [show (1 : ℝ) + -1 / (2 * a) = 1 - 1 / (2 * a) by ring]
  field_simp [ha.ne']

theorem gammaAmplitude_tendsto_one : Tendsto gammaAmplitude atTop (𝓝 1) := by
  have hshift : Tendsto (fun a:ℝ => a-(1/2:ℝ)) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro R
    filter_upwards [eventually_ge_atTop (R+(1/2:ℝ))] with a ha
    linarith
  have hD := stirlingRemainder_tendsto.comp hshift
  have hlogS : Tendsto (fun a => Real.log (gammaAmplitude a)) atTop (𝓝 0) := by
    have hh := (hD.add scaled_log_tendsto).add_const (1/2:ℝ)
    rw [show (0 : ℝ) + -1 / 2 + 1 / 2 = 0 by ring] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1:ℝ)] with a ha
    have ha0 : 0<a := by linarith
    have ham : 0<a-1/2 := by linarith
    have hg := Real.Gamma_pos_of_pos (show 0<a+1/2 by linarith)
    rw [gammaAmplitude,Real.log_div (by positivity) (by positivity),
      Real.log_mul hg.ne' (Real.exp_ne_zero _),Real.log_exp,
      Real.log_sqrt (by positivity)]
    have hratio : Real.log (1-1/(2*a))=Real.log (a-1/2)-Real.log a := by
      rw [←Real.log_div ham.ne' ha0.ne']
      congr 1
      field_simp
    simp only [Function.comp_apply]
    rw [hratio,stirlingRemainder]
    rw [show a - 1 / 2 + 1 = a + 1 / 2 by ring]
    ring
  have hs := Real.continuous_exp.continuousAt.tendsto.comp hlogS
  simp only [Real.exp_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with a ha
  exact Real.exp_log (gammaAmplitude_pos a ha)

theorem gammaAmplitude_continuousOn : ContinuousOn gammaAmplitude (Ici 0) := by
  apply ContinuousOn.div_const
  apply ContinuousOn.mul
  · intro a ha
    have ha0 : 0 ≤ a := ha
    exact (Real.differentiableAt_Gamma (s := a + 1 / 2)
      (fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])).continuousAt.comp
      (f := fun x : ℝ => x + 1 / 2) (x := a)
      ((continuousAt_id.add_const (1/2:ℝ))) |>.continuousWithinAt
  · apply Continuous.continuousOn
    apply Real.continuous_exp.comp
    exact continuous_id.sub Real.continuous_mul_log

/-- Absolute positive bounds, including the two endpoints of the mesh interval. -/
theorem gammaAmplitude_global_bounds : ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀a,0≤a→c≤gammaAmplitude a ∧ gammaAmplitude a≤C := by
  have hev := gammaAmplitude_tendsto_one.eventually
    (Ioo_mem_nhds (by norm_num : (1/2:ℝ)<1) (by norm_num : (1:ℝ)<2))
  obtain ⟨A,hA⟩ := eventually_atTop.mp hev
  let R := max 1 A
  have hR : 0≤R := by dsimp [R]; positivity
  have hc := gammaAmplitude_continuousOn.mono (Icc_subset_Ici_self : Icc 0 R⊆Ici 0)
  obtain ⟨a,ha,ham⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hR) hc
  obtain ⟨b,hb,hbM⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hR) hc
  refine ⟨min (gammaAmplitude a) (1/2),max (gammaAmplitude b) 2,
    lt_min (gammaAmplitude_pos a ha.1) (by norm_num),by positivity,?_⟩
  intro x hx
  by_cases hxR : x≤R
  · exact ⟨(min_le_left _ _).trans (ham ⟨hx,hxR⟩),
      (hbM ⟨hx,hxR⟩).trans (le_max_left _ _)⟩
  · have hAx : A≤x := (le_max_right 1 A).trans (le_of_not_ge hxR)
    have hh := hA x hAx
    exact ⟨(min_le_right _ _).trans hh.1.le,hh.2.le.trans (le_max_right _ _)⟩

theorem meshAmplitude_global_bounds : ∃c C:ℝ,0<c ∧ 0<C ∧
    ∀m:ℕ,∀u∈Icc (-1:ℝ) 1,c≤meshAmplitude m u ∧ meshAmplitude m u≤C := by
  obtain ⟨c,C,hc,hC,hbounds⟩ := gammaAmplitude_global_bounds
  refine ⟨c^2,C^2,by positivity,by positivity,?_⟩
  intro m u hu
  have huL : 0 ≤ 1 + u := by linarith [hu.1]
  have huR : 0 ≤ 1 - u := by linarith [hu.2]
  have ha : 0≤(m:ℝ)*(1+u)/2 := by positivity
  have hb : 0≤(m:ℝ)*(1-u)/2 := by positivity
  obtain ⟨hl0,hu0⟩ := hbounds _ ha
  obtain ⟨hl1,hu1⟩ := hbounds _ hb
  constructor
  · simpa [meshAmplitude,pow_two] using
      (mul_le_mul hl0 hl1 hc.le (gammaAmplitude_pos _ ha).le)
  · simpa [meshAmplitude,pow_two] using
      (mul_le_mul hu0 hu1 (gammaAmplitude_pos _ hb).le hC.le)

/-- The amplitude converges uniformly on every fixed strict interior interval. -/
theorem meshAmplitude_uniform_one (b : ℝ) (hb0 : 0≤b) (hb1 : b<1) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠm:ℕ in atTop,∀u,|u|≤b→|meshAmplitude m u-1|<ε := by
  let η := min (1/2:ℝ) (ε/4)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  obtain ⟨A,hA⟩ := eventually_atTop.mp
    ((Metric.tendsto_nhds.mp gammaAmplitude_tendsto_one) η hη)
  have hm : Tendsto (fun m:ℕ => (m:ℝ)*(1-b)/2) atTop atTop :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const (by linarith)).atTop_div_const (by norm_num)
  filter_upwards [hm.eventually_ge_atTop A] with m hmA
  intro u hu
  have hh0 : A≤(m:ℝ)*(1+u)/2 := by
    have hu' := (abs_le.mp hu).1
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hh1 : A≤(m:ℝ)*(1-u)/2 := by
    have hu' := (abs_le.mp hu).2
    nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have h0 := hA _ hh0
  have h1 := hA _ hh1
  simp only [Real.dist_eq] at h0 h1
  have huL : 0 ≤ 1 + u := by linarith [(abs_le.mp hu).1]
  have huR : 0 ≤ 1 - u := by linarith [(abs_le.mp hu).2]
  have hpos0 := gammaAmplitude_pos ((m:ℝ)*(1+u)/2) (by positivity)
  have hpos1 := gammaAmplitude_pos ((m:ℝ)*(1-u)/2) (by positivity)
  have hηhalf : η≤1/2 := min_le_left _ _
  have hηε : η≤ε/4 := min_le_right _ _
  have hab := abs_sub_le
    (gammaAmplitude ((m:ℝ)*(1+u)/2)*gammaAmplitude ((m:ℝ)*(1-u)/2))
    (gammaAmplitude ((m:ℝ)*(1+u)/2)) 1
  rw [←mul_sub_one,abs_mul,abs_of_pos hpos0] at hab
  have hg0 := (abs_lt.mp h0).2
  dsimp [meshAmplitude]
  nlinarith [mul_lt_mul_of_pos_left h1 hpos0]

end Erdos1152.V5
