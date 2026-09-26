import Erdos1152.ExternalField
import Mathlib.Analysis.Convex.Deriv

noncomputable section
open scoped Topology Real
open Set Filter Real
namespace Erdos1152.V5

/-- Supporting-line inequality from the derivative's monotonicity, using MVT
 on the actual segment between the two arguments. -/
theorem tangent_of_monotone_derivative (I : Set ℝ) (hI : Convex ℝ I)
    (F F₁ : ℝ→ℝ) (hF : ∀x∈I,HasDerivAt F (F₁ x) x)
    (hm : MonotoneOn F₁ I) {x y : ℝ} (hx : x∈I) (hy : y∈I) :
    F x+F₁ x*(y-x)≤F y := by
  rcases lt_trichotomy x y with hxy|rfl|hyx
  · have hsub : Icc x y⊆I := hI.ordConnected.out hx hy
    obtain ⟨z,hz,hzF⟩ := exists_hasDerivAt_eq_slope F F₁ hxy
      (fun z hz => (hF z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => hF z (hsub ⟨hz.1.le,hz.2.le⟩))
    have hmono := hm hx (hsub ⟨hz.1.le,hz.2.le⟩) hz.1.le
    rw [hzF] at hmono
    have hh := (le_div_iff₀ (sub_pos.mpr hxy)).mp hmono
    linarith
  · simp
  · have hsub : Icc y x⊆I := hI.ordConnected.out hy hx
    obtain ⟨z,hz,hzF⟩ := exists_hasDerivAt_eq_slope F F₁ hyx
      (fun z hz => (hF z (hsub hz)).continuousAt.continuousWithinAt)
      (fun z hz => hF z (hsub ⟨hz.1.le,hz.2.le⟩))
    have hmono := hm (hsub ⟨hz.1.le,hz.2.le⟩) hx hz.2.le
    rw [hzF] at hmono
    have hh := (div_le_iff₀ (sub_pos.mpr hyx)).mp hmono
    nlinarith

theorem convex_tangent_line (I : Set ℝ) (F : ℝ→ℝ) (hc : ConvexOn ℝ I F)
    (x y d : ℝ) (hx : x∈I) (hy : y∈I) (hd : HasDerivAt F d x) :
    F x+d*(y-x)≤F y := by
  rcases lt_trichotomy x y with hxy|rfl|hyx
  · have h := hc.le_slope_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hxy)).mp h
    linarith
  · simp
  · have h := hc.slope_le_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hyx)).mp h
    nlinarith

theorem tangent_of_second_nonneg (I : Set ℝ) (hI : Convex ℝ I)
    (F F₁ F₂ : ℝ→ℝ) (hF : ∀x∈I,HasDerivAt F (F₁ x) x)
    (hF₁ : ∀x∈I,HasDerivAt F₁ (F₂ x) x) (hF₂ : ∀x∈I,0≤F₂ x)
    {x y : ℝ} (hx : x∈I) (hy : y∈I) : F x+F₁ x*(y-x)≤F y := by
  apply tangent_of_monotone_derivative I hI F F₁ hF _ hx hy
  exact monotoneOn_of_hasDerivWithinAt_nonneg hI
    (fun x hx => (hF₁ x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hF₁ x (interior_subset hx)).hasDerivWithinAt)
    (fun x hx => hF₂ x (interior_subset hx))

/-- A quadratic remainder bound; the nonoptimal factor avoids any higher
 smoothness assumptions or second-order mean-value API. -/
theorem quadratic_remainder_bound (I : Set ℝ) (hI : Convex ℝ I)
    (F F₁ F₂ : ℝ→ℝ) (hF : ∀x∈I,HasDerivAt F (F₁ x) x)
    (hF₁ : ∀x∈I,HasDerivAt F₁ (F₂ x) x)
    (C : ℝ) (hC : 0≤C) (hbound : ∀x∈I,|F₂ x|≤C)
    {x y : ℝ} (hx : x∈I) (hy : y∈I) :
    |F y-F x-F₁ x*(y-x)|≤C*(y-x)^2 := by
  let J := uIcc x y
  have hJI : J⊆I := hI.ordConnected.uIcc_subset hx hy
  have hd (z : ℝ) (hz : z∈J) : |F₁ z-F₁ x|≤C*|y-x| := by
    have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun w hw => (hF₁ w (hJI hw)).hasDerivWithinAt)
      (fun w hw => by simpa [Real.norm_eq_abs] using hbound w (hJI hw))
      (left_mem_uIcc) hz
    simp only [Real.norm_eq_abs] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ hC
    rcases le_total x y with hxy | hyx
    · have hz' : x≤z ∧ z≤y := by simpa only [J,uIcc_of_le hxy,mem_Icc] using hz
      rw [abs_of_nonneg (sub_nonneg.mpr hz'.1),abs_of_nonneg (sub_nonneg.mpr hxy)]
      exact sub_le_sub_right hz'.2 x
    · have hz' : y≤z ∧ z≤x := by simpa only [J,uIcc_of_ge hyx,mem_Icc] using hz
      rw [abs_of_nonpos (sub_nonpos.mpr hz'.2),abs_of_nonpos (sub_nonpos.mpr hyx)]
      linarith
  let E : ℝ → ℝ := fun z => F z-F x-F₁ x*(z-x)
  have hE (z : ℝ) (hz : z∈J) : HasDerivAt E (F₁ z-F₁ x) z := by
    convert! ((hF z (hJI hz)).sub_const (F x)).sub
      (((hasDerivAt_id z).sub_const x).const_mul (F₁ x)) using 1
    ring
  have h := (convex_uIcc x y).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (hE z hz).hasDerivWithinAt)
    (fun z hz => by simpa [Real.norm_eq_abs] using hd z hz) left_mem_uIcc right_mem_uIcc
  calc
    |F y-F x-F₁ x*(y-x)|≤(C*|y-x|)*|y-x| := by
      simpa only [E,sub_self,mul_zero,sub_zero,Real.norm_eq_abs] using h
    _=C*(y-x)^2 := by rw [mul_assoc,←pow_two,sq_abs]

theorem model_strong_support (y u : ℝ) (hy : |y|<1) (hu : |u|<1) :
    (u-y)^2/2≤externalField u-externalField y-Real.artanh y*(u-y) := by
  let F : ℝ → ℝ := fun x => externalField x-x^2/2
  let F₁ : ℝ → ℝ := fun x => Real.artanh x-x
  let F₂ : ℝ → ℝ := fun x => 1/(1-x^2)-1
  have hd (x : ℝ) (hx : x∈Ioo (-1:ℝ) 1) : HasDerivAt F (F₁ x) x := by
    convert! (externalField_derivative hx).sub
      (((hasDerivAt_id x).pow 2).div_const 2) using 1
    dsimp only [F₁, id_eq]
    ring
  have hd1 (x : ℝ) (hx : x∈Ioo (-1:ℝ) 1) : HasDerivAt F₁ (F₂ x) x :=
    (artanh_derivative hx).sub (hasDerivAt_id x)
  have hd2 (x : ℝ) (hx : x∈Ioo (-1:ℝ) 1) : 0≤F₂ x := by
    have hpos : 0<1-x^2 := by nlinarith [hx.1,hx.2]
    dsimp [F₂]
    rw [sub_nonneg,le_div_iff₀ hpos]
    nlinarith [sq_nonneg x]
  have hs := tangent_of_second_nonneg (Ioo (-1:ℝ) 1) (convex_Ioo _ _) F F₁ F₂
    hd hd1 hd2 (abs_lt.mp hy) (abs_lt.mp hu)
  dsimp [F,F₁] at hs
  nlinarith

theorem artanh_central_bound (y : ℝ) (hy : |y|≤1/4) : |Real.artanh y|≤1/3 := by
  have h := (convex_Icc (-(1/4:ℝ)) (1/4)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (artanh_derivative (show x∈Ioo (-1:ℝ) 1 by
      constructor <;> linarith [hx.1,hx.2])).hasDerivWithinAt)
    (C := (16/15:ℝ))
    (fun x hx => show ‖1/(1-x^2)‖≤16/15 by
      have hp : 0<1-x^2 := by nlinarith [hx.1,hx.2]
      rw [Real.norm_eq_abs,abs_of_pos (by positivity),div_le_iff₀ hp]
      nlinarith [hx.1,hx.2]) (by norm_num : (0:ℝ)∈Icc (-(1/4:ℝ)) (1/4)) (abs_le.mp hy)
  simp only [Real.artanh_zero,sub_zero,Real.norm_eq_abs] at h
  nlinarith

@[simp] theorem externalField_neg (x : ℝ) : externalField (-x)=externalField x := by
  unfold externalField
  ring_nf

/-- The endpoint tangent remainder of the uniform-model field. -/
theorem model_endpoint_remainder (b u : ℝ) (hb : 0<b) (hb1 : b<1)
    (hu : b≤u) (hu1 : u<1) :
    externalField u-externalField b-Real.artanh b*(u-b)≤Real.log (2/(1+b)) := by
  have hmono : MonotoneOn Real.artanh (Ioo (-1:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo _ _)
      (fun x hx => (artanh_derivative hx).continuousAt.continuousWithinAt)
      (fun x hx => (artanh_derivative (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    have hp : 0<1-x^2 := by nlinarith [hx'.1,hx'.2]
    positivity
  let R := fun x => externalField x-externalField b-Real.artanh b*(x-b)
  have hRc : Continuous R := by
    have hQ : Continuous externalField := by
      unfold externalField
      fun_prop
    exact (hQ.sub continuous_const).sub (continuous_const.mul (continuous_id.sub continuous_const))
  have hRm : MonotoneOn R (Icc b 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc b 1) hRc.continuousOn
      (f' := fun x => Real.artanh x-Real.artanh b)
    · intro x hx
      have hx' : x∈Ioo b 1 := by simpa [interior_Icc] using hx
      convert!
        (((externalField_derivative ⟨by linarith [hx'.1],hx'.2⟩).sub_const (externalField b)).sub
          (((hasDerivAt_id x).sub_const b).const_mul (Real.artanh b))).hasDerivWithinAt
            (s := interior (Icc b 1)) using 1
      ring
    · intro x hx
      have hx' : x∈Ioo b 1 := by simpa [interior_Icc] using hx
      exact sub_nonneg.mpr (hmono ⟨by linarith,hb1⟩ ⟨by linarith [hx'.1],hx'.2⟩ hx'.1.le)
  have hs := hRm ⟨hu,hu1.le⟩ ⟨hb1.le,le_rfl⟩ hu1.le
  have he : R 1=Real.log (2/(1+b)) := by
    unfold R externalField
    rw [Real.artanh_eq_half_log ⟨by linarith,hb1.le⟩,
      Real.log_div (by positivity : 1+b≠0) (by positivity : 1-b≠0),
      Real.log_div (by norm_num : (2:ℝ)≠0) (by positivity : 1+b≠0)]
    norm_num
    ring
  rw [he] at hs
  exact hs

end Erdos1152.V5
