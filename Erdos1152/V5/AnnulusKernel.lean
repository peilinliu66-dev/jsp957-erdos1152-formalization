import Erdos1152.V5.TangentIntegration
import Erdos1152.V4.UniformLocalPotential
import Erdos1152.V5.ModelJet

/-!
# A fixed, explicitly integrated, scaled annulus

The continuous clipped kernel agrees with (R v-u)^(-2) outside the inner
interval.  Its uniform-measure integral is evaluated by the elementary
antiderivative -(R (R v-u))^(-1).  These are the actual finite-annulus terms
in the second derivative of the local external field.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V5
open V4

noncomputable def annulusKernel (R b : ℝ) (z : Segment × Segment) : ℝ :=
  (max ((1-b)^2) ((R*(z.2 : ℝ)-b*(z.1 : ℝ))^2))⁻¹

noncomputable def annulusModel (R u : ℝ) : ℝ :=
  (1/(1-u)+1/(1+u)-1/(R-u)-1/(R+u))/2

@[fun_prop] theorem continuous_annulusKernel (R b : ℝ) (hb : b < 1) :
    Continuous (annulusKernel R b) := by
  unfold annulusKernel
  have hp : 0 < (1-b)^2 := sq_pos_of_pos (sub_pos.mpr hb)
  have hc : Continuous (fun z : Segment × Segment =>
      max ((1-b)^2) ((R*(z.2 : ℝ)-b*(z.1 : ℝ))^2)) := by fun_prop
  exact hc.inv₀ (fun z => (hp.trans_le (le_max_left _ _)).ne')

theorem annulusKernel_nonneg (R b : ℝ) (z : Segment × Segment) :
    0 ≤ annulusKernel R b z := by unfold annulusKernel; positivity

theorem annulusKernel_le (R b : ℝ) (hb : b < 1) (z : Segment × Segment) :
    annulusKernel R b z ≤ ((1-b)^2)⁻¹ := by
  apply inv_anti₀ (sq_pos_of_pos (sub_pos.mpr hb)) (le_max_left _ _)

/-- A lower bound on |R v-u| on the entire source annulus, including its
inner endpoints. No separation among the original nodes is involved. -/
theorem annulus_gap (R b : ℝ) (hR : 0 < R) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (z t : Segment) (ht : t ∉ sourceInterval (-(1/R)) (1/R)) :
    1-b ≤ |R*(t : ℝ)-b*(z : ℝ)| := by
  have htv : (t : ℝ) ≤ -(1/R) ∨ 1/R ≤ (t : ℝ) := by
    by_cases h : (t : ℝ) ≤ -(1/R)
    · exact Or.inl h
    · exact Or.inr (le_of_not_gt (fun hh => ht ⟨lt_of_not_ge h,hh⟩))
  have hRne := hR.ne'
  have hone : R*(1/R)=1 := by field_simp
  have hzu : -b ≤ b*(z : ℝ) ∧ b*(z : ℝ) ≤ b := by
    constructor <;> nlinarith [z.property.1,z.property.2]
  rcases htv with ht | ht
  · have hm := mul_le_mul_of_nonneg_left ht hR.le
    have hneg : R * (-(1/R)) = -1 := by rw [mul_neg,hone]
    rw [hneg] at hm
    exact (by linarith : 1-b ≤ -(R*(t : ℝ)-b*(z : ℝ))).trans (neg_le_abs _)
  · have hm := mul_le_mul_of_nonneg_left ht hR.le
    rw [hone] at hm
    exact (by linarith : 1-b ≤ R*(t : ℝ)-b*(z : ℝ)).trans (le_abs_self _)

theorem annulusKernel_eq (R b : ℝ) (hR : 0 < R) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (z t : Segment) (ht : t ∉ sourceInterval (-(1/R)) (1/R)) :
    annulusKernel R b (z,t) = 1/(R*(t : ℝ)-b*(z : ℝ))^2 := by
  have hg := annulus_gap R b hR hb0 hb1 z t ht
  have hs : (1-b)^2 ≤ (R*(t : ℝ)-b*(z : ℝ))^2 := by
    nlinarith [sq_abs (R*(t : ℝ)-b*(z : ℝ)),sq_nonneg (|R*(t : ℝ)-b*(z : ℝ)|-(1-b))]
  simp only [annulusKernel,max_eq_right hs,one_div]

/-- Uniform probability on Segment has exactly half the usual real integral. -/
theorem integral_uniform_exterior_real (f : ℝ → ℝ) (hf : Measurable f) (a b : ℝ) :
    (∫ t in (sourceInterval a b)ᶜ,f (t : ℝ) ∂(uniformSegmentProbability : Measure Segment)) =
      (1/2 : ℝ)*∫ v in Segment \ Ioo a b,f v := by
  rw [← integral_indicator (measurableSet_sourceInterval a b).compl,
    integral_uniformSegment (((sourceInterval a b)ᶜ).indicator (fun t : Segment => f (t : ℝ)))
      (by exact ((hf.comp measurable_subtype_coe).indicator
        (measurableSet_sourceInterval a b).compl))]
  have he : (fun v => ((sourceInterval a b)ᶜ).indicator
      (fun t : Segment => f (t : ℝ)) (clampSegment v)) =ᵐ[baseMeasure]
      ((Ioo a b)ᶜ).indicator f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    have hc : (clampSegment v : ℝ)=v := by
      simp only [clampSegment,Set.projIcc_of_mem _ hv,Subtype.coe_mk]
    by_cases hvab : v ∈ Ioo a b <;> simp [sourceInterval,hc,hvab]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioo.compl]
  congr 1
  change (∫ v,f v ∂((volume.restrict Segment).restrict (Ioo a b)ᶜ)) = _
  rw [Measure.restrict_restrict measurableSet_Ioo.compl, Set.inter_comm]
  rfl

/-- Elementary antiderivative, with every possible pole explicitly excluded. -/
theorem reciprocal_square_integral (R u a b : ℝ) (hR : R ≠ 0) (hab : a ≤ b)
    (hn : ∀ v ∈ Icc a b,R*v-u ≠ 0) :
    (∫ v in Icc a b,(1 : ℝ)/(R*v-u)^2) =
      -(1/R)/(R*b-u) + (1/R)/(R*a-u) := by
  have hd (v : ℝ) (hv : v ∈ Icc a b) :
      HasDerivAt (fun t : ℝ => -(1/R)/(R*t-u)) (1/(R*v-u)^2) v := by
    have h := (hasDerivAt_const v (-(1/R))).div
      (((hasDerivAt_id v).const_mul R).sub_const u) (hn v hv)
    convert h using 1 <;> (try rfl) <;>
      (try simp only [id_eq, mul_one, zero_mul, zero_sub]) <;>
      field_simp [hR, hn v hv]
  have hc : ContinuousOn (fun v : ℝ => (1 : ℝ)/(R*v-u)^2) (Icc a b) := by
    apply continuousOn_const.div (by fun_prop)
    intro v hv
    exact pow_ne_zero 2 (hn v hv)
  have hi : IntervalIntegrable (fun v : ℝ => (1 : ℝ)/(R*v-u)^2) volume a b :=
    hc.intervalIntegrable_of_Icc hab
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v hv => hd v (by simpa only [uIcc_of_le hab] using hv)) hi
  simpa only [neg_div,sub_neg_eq_add] using hFTC

/-- Exact finite-annulus model integral. -/
theorem uniform_annulus_integral (R u : ℝ) (hR : 2 ≤ R) (hu : |u| < 1) :
    (∫ t in (sourceInterval (-(1/R)) (1/R))ᶜ,
      1/(R*(t : ℝ)-u)^2 ∂(uniformSegmentProbability : Measure Segment)) =
      annulusModel R u/R := by
  have hR0 : 0 < R := by linarith
  have hRne := hR0.ne'
  have hr : 0 < 1/R := one_div_pos.mpr hR0
  have hr1 : 1/R ≤ 1 := (div_le_one hR0).mpr (by linarith)
  have hul : -1 < u := (abs_lt.mp hu).1
  have hur : u < 1 := (abs_lt.mp hu).2
  let f : ℝ → ℝ := fun v => 1/(R*v-u)^2
  have hnL : ∀ v ∈ Icc (-1 : ℝ) (-(1/R)),R*v-u ≠ 0 := by
    intro v hv
    have hm := mul_le_mul_of_nonneg_left hv.2 hR0.le
    have he : R * (-(1/R)) = -1 := by field_simp
    rw [he] at hm
    linarith
  have hnR : ∀ v ∈ Icc (1/R) (1 : ℝ),R*v-u ≠ 0 := by
    intro v hv
    have hm := mul_le_mul_of_nonneg_left hv.1 hR0.le
    have he : R*(1/R)=1 := by field_simp
    rw [he] at hm
    linarith
  have hiL : IntegrableOn f (Icc (-1 : ℝ) (-(1/R))) volume := by
    refine (ContinuousOn.div continuousOn_const (by fun_prop)
      (fun v hv => pow_ne_zero 2 (hnL v hv))).integrableOn_compact isCompact_Icc
  have hiR : IntegrableOn f (Icc (1/R) (1 : ℝ)) volume := by
    refine (ContinuousOn.div continuousOn_const (by fun_prop)
      (fun v hv => pow_ne_zero 2 (hnR v hv))).integrableOn_compact isCompact_Icc
  have hset : Segment \ Ioo (-(1/R)) (1/R) =
      Icc (-1 : ℝ) (-(1/R)) ∪ Icc (1/R) (1 : ℝ) := by
    ext v
    simp only [Segment,Set.mem_sdiff,Set.mem_Icc,Set.mem_Ioo,Set.mem_union]
    constructor
    · rintro ⟨⟨hl,hr⟩,hn⟩
      by_cases hv : v ≤ -(1/R)
      · exact Or.inl ⟨hl,hv⟩
      · exact Or.inr ⟨le_of_not_gt (fun hv' => hn ⟨lt_of_not_ge hv,hv'⟩),hr⟩
    · rintro (hv|hv)
      · refine ⟨⟨hv.1,by linarith [hv.2]⟩,?_⟩
        intro hi
        linarith [hv.2,hi.1]
      · refine ⟨⟨by linarith [hv.1],hv.2⟩,?_⟩
        intro hi
        linarith [hv.1,hi.2]
  have hdis : Disjoint (Icc (-1 : ℝ) (-(1/R))) (Icc (1/R) (1 : ℝ)) := by
    apply Set.disjoint_left.mpr
    intro v hvL hvR
    linarith [hvL.2,hvR.1]
  rw [integral_uniform_exterior_real (fun v : ℝ => 1/(R*v-u)^2) (by fun_prop),hset,
    setIntegral_union hdis measurableSet_Icc hiL hiR]
  rw [reciprocal_square_integral R u (-1) (-(1/R)) hRne (by linarith) hnL,
    reciprocal_square_integral R u (1/R) 1 hRne hr1 hnR]
  unfold annulusModel
  have h1 : 1-u ≠ 0 := by linarith
  have h2 : 1+u ≠ 0 := by linarith
  have h3 : R-u ≠ 0 := by linarith
  have h4 : R+u ≠ 0 := by linarith
  have h5 : -1-u ≠ 0 := by linarith
  have h6 : -R-u ≠ 0 := by linarith
  have he : R * (-(1/R)) = -1 := by field_simp
  rw [he]
  simp only [mul_neg, mul_one]
  field_simp [hRne, h1, h2, h3, h4, h5, h6]
  ring

theorem uniform_annulusKernel (R b : ℝ) (hR : 2 ≤ R)
    (hb0 : 0 ≤ b) (hb1 : b < 1) (z : Segment) :
    (∫ t in (sourceInterval (-(1/R)) (1/R))ᶜ,annulusKernel R b (z,t)
      ∂(uniformSegmentProbability : Measure Segment)) = annulusModel R (b*(z : ℝ))/R := by
  have hu : |b*(z : ℝ)| < 1 := by
    rw [abs_mul,abs_of_nonneg hb0]
    have hz : |(z : ℝ)| ≤ 1 := abs_le.mpr z.property
    exact (mul_le_mul_of_nonneg_left hz hb0).trans_lt (by simpa using hb1)
  rw [← uniform_annulus_integral R (b*(z : ℝ)) hR hu]
  apply setIntegral_congr_fun (measurableSet_sourceInterval _ _).compl
  intro t ht
  exact annulusKernel_eq R b (by linarith) hb0 hb1 z t ht

/-- The tails of the model itself are at most 2/R, uniformly on |u|≤1
away from the two endpoints where the complete model is singular. -/
theorem annulusModel_error (R u : ℝ) (hR : 2 ≤ R) (hu : |u| < 1) :
    |annulusModel R u - 1/(1-u^2)| ≤ 2/R := by
  have hl := (abs_lt.mp hu).1
  have hr := (abs_lt.mp hu).2
  have hR0 : 0 < R := by linarith
  have hu2 : u^2 < 1 := by nlinarith [sq_nonneg u]
  have hd : 0 < R^2-u^2 := by nlinarith
  have he : annulusModel R u-1/(1-u^2) = -R/(R^2-u^2) := by
    unfold annulusModel
    have h₁ : 1-u ≠ 0 := by linarith
    have h₂ : 1+u ≠ 0 := by linarith
    have h₃ : R-u ≠ 0 := by linarith
    have h₄ : R+u ≠ 0 := by linarith
    have h₅ : 1-u^2 ≠ 0 := by linarith
    field_simp
    ring
  rw [he,abs_div,abs_neg,abs_of_pos hR0,abs_of_pos hd]
  apply (div_le_div_iff₀ hd hR0).mpr
  nlinarith

end Erdos1152.V5
