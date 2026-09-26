import Erdos1152.V5.SamplingDecay
import Mathlib.MeasureTheory.Integral.CircleIntegral

noncomputable section
open scoped Topology Real
open Complex MeasureTheory Set Filter
namespace Erdos1152.V5

def sampleNodes (t θ : ℝ) (N : ℕ) : Finset ℂ :=
  (symmetricIndices N).image (fun j => (samplePoint t θ j:ℂ))

theorem samplePoint_injective (t θ : ℝ) (ht : t≠0) :
    Function.Injective (fun j:ℤ => (samplePoint t θ j:ℂ)) := by
  intro j k h
  have hr : samplePoint t θ j=samplePoint t θ k := Complex.ofReal_injective h
  dsimp [samplePoint] at hr
  exact_mod_cast (add_right_cancel ((div_left_inj' ht).mp hr))

theorem sampleNodes_inside (t θ : ℝ) (ht : 0<t) (N : ℕ) :
    ∀a∈sampleNodes t θ N,a∈Metric.ball ((θ/t:ℝ):ℂ) (contourRadius t N) := by
  intro a ha
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
  have hj' : |(j:ℝ)|≤N := by
    have hh := Finset.mem_Icc.mp hj
    exact abs_le.mpr ⟨by exact_mod_cast hh.1,by exact_mod_cast hh.2⟩
  rw [Metric.mem_ball,dist_eq_norm]
  have he : (samplePoint t θ j:ℂ)-((θ/t:ℝ):ℂ)=((j:ℝ)/t:ℝ) := by
    dsimp [samplePoint]; push_cast; field_simp; ring
  rw [he,Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos ht]
  exact (div_lt_div_iff_of_pos_right ht).mpr (by linarith)

theorem samplingSine_zero_iff (t θ : ℝ) (ht : t≠0) (z : ℂ) :
    samplingSine t θ z=0 ↔ ∃j:ℤ,z=(samplePoint t θ j:ℂ) := by
  constructor
  · intro hz
    obtain ⟨j,hj⟩ := Complex.sin_eq_zero_iff.mp hz
    refine ⟨j,?_⟩
    have hπ : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
    have ht' : (t:ℂ)≠0 := by exact_mod_cast ht
    dsimp [samplePoint]
    push_cast
    field_simp [ht']
    apply mul_left_cancel₀ hπ
    linear_combination hj
  · rintro ⟨j,rfl⟩
    exact samplingSine_at_grid t θ ht j

theorem samplingSine_all_zeros_in_disk (t θ : ℝ) (ht : 0<t) (N : ℕ) :
    ∀z∈Metric.closedBall ((θ/t:ℝ):ℂ) (contourRadius t N),
      samplingSine t θ z=0→z∈sampleNodes t θ N := by
  intro z hz hzero
  obtain ⟨j,rfl⟩ := (samplingSine_zero_iff t θ ht.ne' z).mp hzero
  apply Finset.mem_image.mpr
  refine ⟨j,?_,rfl⟩
  have hdist := Metric.mem_closedBall.mp hz
  have he : dist (samplePoint t θ j:ℂ) ((θ/t:ℝ):ℂ)=|(j:ℝ)|/t := by
    rw [dist_eq_norm]
    have hh : (samplePoint t θ j:ℂ)-((θ/t:ℝ):ℂ)=((j:ℝ)/t:ℝ) := by
      dsimp [samplePoint]; push_cast; field_simp; ring
    rw [hh]; simp [abs_div,abs_of_pos ht]
  rw [he] at hdist
  have hj : |(j:ℝ)|≤(N:ℝ)+1/2 :=
    (div_le_div_iff_of_pos_right ht).mp hdist
  have hj' := abs_le.mp hj
  have hupper : j≤N := by
    have hi : j<(N:ℤ)+1 := by
      exact_mod_cast (show (j:ℝ)<(N:ℝ)+1 by linarith)
    omega
  have hlower : -(N:ℤ)≤j := by
    have : -(N:ℝ)-1<(j:ℝ) := by linarith
    have hi : -(N:ℤ)-1<j := by exact_mod_cast this
    omega
  exact Finset.mem_Icc.mpr ⟨hlower,hupper⟩

theorem sampleNodes_simple (t θ : ℝ) (ht : 0<t) (N : ℕ) :
    ∀a∈sampleNodes t θ N,deriv (samplingSine t θ) a≠0 := by
  intro a ha
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
  rw [samplingSine_derivative t θ ht.ne' j]
  apply mul_ne_zero
  · exact_mod_cast mul_ne_zero Real.pi_ne_zero ht.ne'
  · exact zpow_ne_zero _ (by norm_num)

theorem sampling_contour_geometry (t θ : ℝ) (ht : 0<t) (ht1 : t≤1)
    (hθ : |θ|≤1/2) (N : ℕ) {z : ℂ}
    (hz : z∈Metric.sphere ((θ/t:ℝ):ℂ) (contourRadius t N)) :
    (N:ℝ)≤‖z‖ ∧ ‖z‖≤((N:ℝ)+1)/t := by
  have ha : ‖((θ/t:ℝ):ℂ)‖≤1/(2*t) := by
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos ht]
    exact (div_le_div_of_nonneg_right hθ ht.le).trans_eq (by ring)
  have he : ‖z-((θ/t:ℝ):ℂ)‖=((N:ℝ)+1/2)/t := mem_sphere_iff_norm.mp hz
  have htN : (N:ℝ)*t≤N := mul_le_of_le_one_right (Nat.cast_nonneg N) ht1
  constructor
  · have hn := norm_sub_le z ((θ/t:ℝ):ℂ)
    rw [he] at hn
    have h := (div_le_iff₀ ht).mp hn
    have h2 := mul_le_mul_of_nonneg_right ha ht.le
    have hcancel : (1/(2*t))*t=1/2 := by field_simp
    rw [hcancel] at h2
    nlinarith
  · have hn := norm_add_le (z-((θ/t:ℝ):ℂ)) ((θ/t:ℝ):ℂ)
    rw [sub_add_cancel,he] at hn
    apply hn.trans
    calc
      _≤((N:ℝ)+1/2)/t+1/(2*t) := add_le_add_right ha _
      _=((N:ℝ)+1)/t := by field_simp; ring

/-- The integral estimates are uniform on the entire contour, not merely on its
 high-imaginary portions. -/
theorem moment_integrand_contour_bound
    (g : ℂ→ℂ) (C σ t θ : ℝ) (hC : 0≤C) (ht : 0<t) (ht1 : t≤1)
    (hθ : |θ|≤1/2) (hσ : σ≤Real.pi*t)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (d : ℕ) (hd : d≤1) (N : ℕ) (hN : 1≤N) {z : ℂ}
    (hz : z∈Metric.sphere ((θ/t:ℝ):ℂ) (contourRadius t N)) :
    ‖z^d*g z/samplingSine t θ z‖≤
      ((N:ℝ)+1)/t*(C/sineContourConstant)/((N:ℝ)+1)^6 := by
  have hc := sineContourConstant_pos
  have hlow := samplingSine_lower_on_contour t θ ht N hN hz
  have hgeo := sampling_contour_geometry t θ ht ht1 hθ N hz
  have hpos : 0<sineContourConstant*Real.exp (Real.pi*t*|z.im|) := by positivity
  have he : Real.exp (σ*|z.im|)≤Real.exp (Real.pi*t*|z.im|) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
  have hb : ‖g z/samplingSine t θ z‖≤
      (C/sineContourConstant)/((N:ℝ)+1)^6 := by
    rw [norm_div]
    calc
      _≤(C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)/
          (sineContourConstant*Real.exp (Real.pi*t*|z.im|)) :=
        div_le_div₀ (by positivity) (hg z) hpos hlow
      _≤(C*Real.exp (Real.pi*t*|z.im|)/((N:ℝ)+1)^6)/
          (sineContourConstant*Real.exp (Real.pi*t*|z.im|)) := by
        apply div_le_div_of_nonneg_right _ hpos.le
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left he hC)
          (by positivity)
        exact pow_le_pow_left₀ (by positivity) (by linarith [hgeo.1]) 6
      _=(C/sineContourConstant)/((N:ℝ)+1)^6 := by
        field_simp
  have hpow : ‖z‖^d≤((N:ℝ)+1)/t := by
    interval_cases d
    · norm_num
      rw [le_div_iff₀ ht]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    · simpa using hgeo.2
  calc
    ‖z^d*g z/samplingSine t θ z‖ = ‖z‖^d * ‖g z/samplingSine t θ z‖ := by
      rw [mul_div_assoc, norm_mul, norm_pow]
    _ ≤ (((N:ℝ)+1)/t)*((C/sineContourConstant)/((N:ℝ)+1)^6) :=
      mul_le_mul hpow hb (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem vanishing_contour_bound (C t : ℝ) :
    Tendsto (fun N:ℕ => (2*Real.pi*C/(sineContourConstant*t^2))*
      (1/((N:ℝ)+1))^4) atTop (𝓝 0) := by
  simpa only [zero_pow (by decide : 4 ≠ 0), mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 4 |>.const_mul
      (2*Real.pi*C/(sineContourConstant*t^2))

theorem moment_contour_tendsto_zero
    (g : ℂ→ℂ) (C σ t θ : ℝ) (hC : 0≤C) (ht : 0<t) (ht1 : t≤1)
    (hθ : |θ|≤1/2) (hσ : σ≤Real.pi*t)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (d : ℕ) (hd : d≤1) :
    Tendsto (fun N => ∮z in C(((θ/t:ℝ):ℂ),contourRadius t N),
      z^d*g z/samplingSine t θ z) atTop (𝓝 0) := by
  have hc := sineContourConstant_pos
  apply squeeze_zero_norm' (a := fun N:ℕ =>
    (2*Real.pi*C/(sineContourConstant*t^2))*(1/((N:ℝ)+1))^4)
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have h := circleIntegral.norm_integral_le_of_norm_le_const
      (f := fun z : ℂ => z^d*g z/samplingSine t θ z)
      (c := ((θ/t:ℝ):ℂ)) (R := contourRadius t N)
      (by dsimp [contourRadius]; positivity)
      (fun z hz => moment_integrand_contour_bound g C σ t θ hC ht ht1 hθ hσ hg d hd N hN hz)
    apply h.trans
    have hr : contourRadius t N≤((N:ℝ)+1)/t := by
      dsimp [contourRadius]; gcongr <;> norm_num
    calc
      _≤2*Real.pi*(((N:ℝ)+1)/t)*
          (((N:ℝ)+1)/t*(C/sineContourConstant)/((N:ℝ)+1)^6) := by gcongr <;> positivity
      _=(2*Real.pi*C/(sineContourConstant*t^2))*(1/((N:ℝ)+1))^4 := by
        field_simp
  · exact vanishing_contour_bound C t

theorem cauchy_contour_tendsto_zero
    (g : ℂ→ℂ) (C σ t θ : ℝ) (hC : 0≤C) (ht : 0<t) (ht1 : t≤1)
    (hθ : |θ|≤1/2) (hσ : σ≤Real.pi*t)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6) (ξ : ℂ) :
    Tendsto (fun N => ∮z in C(((θ/t:ℝ):ℂ),contourRadius t N),
      (g z/samplingSine t θ z)/(z-ξ)) atTop (𝓝 0) := by
  obtain ⟨N₀,hN₀⟩ := exists_nat_gt (‖ξ‖+1)
  have hc := sineContourConstant_pos
  apply squeeze_zero_norm' (a := fun N:ℕ =>
    (2*Real.pi*C/(sineContourConstant*t^2))*(1/((N:ℝ)+1))^4)
  · filter_upwards [eventually_ge_atTop (max 1 N₀)] with N hN
    have hN1 : 1≤N := (le_max_left _ _).trans hN
    have hrad : 0<contourRadius t N := by dsimp [contourRadius]; positivity
    have hp (z : ℂ) (hz : z∈Metric.sphere ((θ/t:ℝ):ℂ) (contourRadius t N)) :
        ‖(g z/samplingSine t θ z)/(z-ξ)‖≤
          ((N:ℝ)+1)/t*(C/sineContourConstant)/((N:ℝ)+1)^6 := by
      have hgeo := sampling_contour_geometry t θ ht ht1 hθ N hz
      have hnn : (N₀:ℝ)≤N := by exact_mod_cast (le_max_right 1 N₀).trans hN
      have hdist : 1≤‖z-ξ‖ := by
        have hh := norm_sub_norm_le z ξ
        nlinarith
      rw [norm_div]
      apply (div_le_self (norm_nonneg _) hdist).trans
      simpa using moment_integrand_contour_bound g C σ t θ hC ht ht1 hθ hσ hg 0
        (by norm_num) N hN1 hz
    have hi := circleIntegral.norm_integral_le_of_norm_le_const
      (f := fun z : ℂ => (g z/samplingSine t θ z)/(z-ξ))
      (c := ((θ/t:ℝ):ℂ)) (R := contourRadius t N) hrad.le hp
    apply hi.trans
    have hr : contourRadius t N≤((N:ℝ)+1)/t := by
      dsimp [contourRadius]; gcongr <;> norm_num
    calc
      _≤2*Real.pi*(((N:ℝ)+1)/t)*
        (((N:ℝ)+1)/t*(C/sineContourConstant)/((N:ℝ)+1)^6) := by gcongr <;> positivity
      _=(2*Real.pi*C/(sineContourConstant*t^2))*(1/((N:ℝ)+1))^4 := by
        field_simp
  · exact vanishing_contour_bound C t

end Erdos1152.V5
