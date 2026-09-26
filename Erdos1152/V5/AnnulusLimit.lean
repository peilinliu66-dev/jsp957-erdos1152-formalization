import Erdos1152.V5.AnnulusKernel
import Erdos1152.V4.LimitFieldRegularity
import Erdos1152.V4.ExternalTail

/-!
# The h -> 0 limit of the actual second external-field derivative

A fixed enlarged tangent measure supplies the finite annulus.  The V4 remote
estimate supplies its complement.  The last theorem has no assumed tangent,
annulus or tail convergence: they are obtained from the original measure at
almost every actual remaining minimum point.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V5
open V4

noncomputable def annulusIntegral (μ : ProbabilityMeasure Segment) (x h R u : ℝ) : ℝ :=
  ∫ t in sourceInterval (x-R*h) (x+R*h) \ sourceInterval (x-h) (x+h),
    h^2/(x+h*u-(t : ℝ))^2 ∂(μ : Measure Segment)

theorem sourceBall_eq_interval (x h : ℝ) :
    sourceBall x h = sourceInterval (x-h) (x+h) := by
  ext t
  simp only [sourceBall,sourceInterval,Set.mem_setOf_eq,Set.mem_preimage,Set.mem_Ioo,abs_lt]
  constructor <;> rintro ⟨hl,hr⟩ <;> constructor <;> linarith

theorem radius_mul_tendsto (R : ℝ) (hR : 0 < R) :
    Tendsto (fun h : ℝ => R*h) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa only [mul_zero] using (show Continuous (fun h : ℝ => R*h) from by fun_prop).continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_pos hR hh

/-- Exact interval membership after rescaling by R h. -/
theorem rescale_inner_iff (x h R t : ℝ) (hh : 0 < h) (hR : 0 < R) :
    (t-x)/(R*h) ∈ Ioo (-(1/R)) (1/R) ↔ t ∈ Ioo (x-h) (x+h) := by
  have hrh : 0 < R*h := mul_pos hR hh
  have he₁ : (-(1/R))*(R*h) = -h := by field_simp [hR.ne']
  have he₂ : (1/R)*(R*h) = h := by field_simp [hR.ne']
  simp only [Set.mem_Ioo,lt_div_iff₀ hrh,div_lt_iff₀ hrh,he₁,he₂]
  constructor <;> rintro ⟨hl,hr⟩ <;> constructor <;> linarith

/-- The near term is an integral against the actual enlarged tangent
probability, with the normalization explicitly accounted for. -/
theorem annulusIntegral_tangent (μ : ProbabilityMeasure Segment) (x h R b : ℝ)
    (hh : 0 < h) (hR : 2 ≤ R) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hmR : 0 < localMass μ x (R*h)) (z : Segment) :
    annulusIntegral μ x h R (b*(z : ℝ)) = localMass μ x (R*h) *
      (∫ t in (sourceInterval (-(1/R)) (1/R))ᶜ,annulusKernel R b (z,t)
        ∂(tangentProbability μ x (R*h) : Measure Segment)) := by
  let I := sourceInterval (x-h) (x+h)
  let J := sourceInterval (x-R*h) (x+R*h)
  let A := (sourceInterval (-(1/R)) (1/R))ᶜ
  let f : Segment → ℝ := A.indicator (fun t => annulusKernel R b (z,t))
  have hf : Measurable f :=
    ((continuous_annulusKernel R b hb1).comp (continuous_const.prodMk continuous_id)).measurable.indicator
      (measurableSet_sourceInterval _ _).compl
  have hR0 : 0 < R := by linarith
  have hu : |b*(z : ℝ)| < 1 := by
    rw [abs_mul,abs_of_nonneg hb0]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr z.property) hb0).trans_lt (by simpa using hb1)
  have he : (fun t : Segment => f (clampSegment (((t : ℝ)-x)/(R*h)))) =ᵐ[(μ : Measure Segment).restrict J]
      Iᶜ.indicator (fun t : Segment => h^2/(x+h*(b*(z : ℝ))-(t : ℝ))^2) := by
    filter_upwards [ae_restrict_mem (measurableSet_sourceInterval (x-R*h) (x+R*h))] with t ht
    let v := clampSegment (((t : ℝ)-x)/(R*h))
    have hc : (v : ℝ)=((t : ℝ)-x)/(R*h) := clamp_rescale_coe x (R*h) (mul_pos hR0 hh) t ht
    have hv : v ∈ sourceInterval (-(1/R)) (1/R) ↔ t ∈ I := by
      change (v : ℝ) ∈ Ioo (-(1/R)) (1/R) ↔ (t : ℝ) ∈ Ioo (x-h) (x+h)
      rw [hc]
      exact rescale_inner_iff x h R t hh hR0
    by_cases htI : t ∈ I
    · have hvA : v ∉ A := fun hvnot => hvnot (hv.mpr htI)
      simp only [f,v,Set.indicator_of_notMem hvA,Set.indicator_of_notMem
        (show t ∉ Iᶜ from fun htNot => htNot htI)]
    · have hvA : v ∈ A := fun hv' => htI (hv.mp hv')
      change f v = _
      rw [Set.indicator_of_mem (show t ∈ Iᶜ from htI)]
      dsimp only [f]
      rw [Set.indicator_of_mem hvA,annulusKernel_eq R b hR0 hb0 hb1 z v hvA,hc]
      have hn := exterior_point_nonzero hh hu htI
      have heq : R*(((t : ℝ)-x)/(R*h))-b*(z : ℝ) =
          -(x+h*(b*(z : ℝ))-(t : ℝ))/h := by field_simp [hR0.ne', hh.ne']; ring
      rw [heq,div_pow,neg_sq]
      field_simp [hh.ne', hn]
  have hn := integral_tangentProbability μ x (R*h) hmR f hf
  have hfIntegral : (∫ t, f t ∂(tangentProbability μ x (R*h) : Measure Segment)) =
      ∫ t in A, annulusKernel R b (z,t)
        ∂(tangentProbability μ x (R*h) : Measure Segment) := by
    dsimp only [f]
    exact integral_indicator (measurableSet_sourceInterval _ _).compl
  rw [hfIntegral,integral_congr_ae he,
    integral_indicator (measurableSet_sourceInterval (x-h) (x+h)).compl,
    Measure.restrict_restrict (measurableSet_sourceInterval (x-h) (x+h)).compl] at hn
  have hset : Iᶜ ∩ J = J \ I := by ext t; simp [and_comm]
  rw [hset] at hn
  have hn' := (eq_div_iff hmR.ne').mp hn
  dsimp only [annulusIntegral,J,I,A] at hn' ⊢
  nlinarith

/-- Partition the original exterior integral, not a replacement kernel. -/
theorem second_jet_partition (μ : ProbabilityMeasure Segment) (x h R u : ℝ)
    (hh : 0 < h) (hR : 2 ≤ R) (hu : |u| < 1) :
    limitFieldJet μ 2 x h u =
      (annulusIntegral μ x h R u + remoteSecondIntegral μ x h R u)/localMass μ x h := by
  let I := sourceInterval (x-h) (x+h)
  let J := sourceInterval (x-R*h) (x+R*h)
  have hsub : I ⊆ J := by
    intro t ht
    constructor <;> nlinarith [ht.1,ht.2]
  have hset : Iᶜ = (J \ I) ∪ Jᶜ := by
    ext t
    simp only [Set.mem_compl_iff,Set.mem_union,Set.mem_sdiff]
    constructor
    · intro ht
      by_cases htJ : t ∈ J
      · exact Or.inl ⟨htJ,ht⟩
      · exact Or.inr htJ
    · rintro (ht|ht)
      · exact ht.2
      · exact fun htI => ht (hsub htI)
  have hdis : Disjoint (J \ I) Jᶜ := Set.disjoint_left.mpr (fun _ ht hj => hj ht.1)
  have hi : IntegrableOn (fun t : Segment => h^2/(x+h*u-(t : ℝ))^2) Iᶜ (μ : Measure Segment) := by
    simpa [rawFieldJet,I] using
      rawFieldJet_integrable_exterior μ 2 x h u hh hu
  unfold limitFieldJet
  simp only [rawFieldJet,Fin.isValue,reduceCtorEq,ite_false]
  change (∫ t in Iᶜ,h^2/(x+h*u-(t : ℝ))^2 ∂(μ : Measure Segment))/localMass μ x h = _
  rw [hset,setIntegral_union hdis (measurableSet_sourceInterval _ _).compl
    (hi.mono_set (fun _ ht => ht.2)) (hi.mono_set (fun _ ht hi => ht (hsub hi)))]
  simp only [annulusIntegral,remoteSecondIntegral,sourceBall_eq_interval,J,I]

private theorem exterior_kernel_bound (ν : ProbabilityMeasure Segment) (R b : ℝ)
    (hb : b < 1) (z : Segment) :
    |∫ t in (sourceInterval (-(1/R)) (1/R))ᶜ,annulusKernel R b (z,t) ∂(ν : Measure Segment)|
      ≤ ((1-b)^2)⁻¹ := by
  let A := (sourceInterval (-(1/R)) (1/R))ᶜ
  let C := ((1-b)^2)⁻¹
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hc : Continuous (fun t : Segment => annulusKernel R b (z,t)) :=
    (continuous_annulusKernel R b hb).comp (continuous_const.prodMk continuous_id)
  have hi : IntegrableOn (fun t => annulusKernel R b (z,t)) A (ν : Measure Segment) :=
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).restrict (s := A)
  rw [abs_of_nonneg (integral_nonneg (fun t => annulusKernel_nonneg R b (z,t)))]
  calc
    _ ≤ ∫ _t in A,C ∂(ν : Measure Segment) :=
      integral_mono_ae hi (integrable_const _) (Filter.Eventually.of_forall (fun t => annulusKernel_le R b hb (z,t)))
    _ = (ν : Measure Segment).real A * C := by simp [integral_const,smul_eq_mul]
    _ ≤ C := mul_le_of_le_one_left hC (by
      have h := ENNReal.toReal_mono (measure_ne_top (ν : Measure Segment) univ)
        (measure_mono (Set.subset_univ A))
      simpa only [measure_univ,ENNReal.toReal_one,Measure.real] using h)

/-- Uniform convergence on a fixed finite annulus, from the actual CDF derivative. -/
theorem annulus_limit (μ : ProbabilityMeasure Segment) (hfloor : potentialFloor μ ≠ ⊥)
    (x w R b : ℝ) (hw : 0 < w) (hx : HasDerivAt (sourceCDF μ) w x)
    (hR : 2 ≤ R) (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ u, |u| ≤ b →
      |annulusIntegral μ x h R u/localMass μ x h-annulusModel R u| < ε := by
  have hR0 : 0 < R := by linarith
  have hτ := (tangentProbability_tendsto μ hfloor x w hw hx).comp (radius_mul_tendsto R hR0)
  have hratio : Tendsto (fun h => localMass μ x (R*h)/localMass μ x h) (𝓝[>] 0) (𝓝 R) := by
    have h := local_relative_interval_mass μ hfloor x w (-R) R hw (by linarith) hx
    have hlim : (R-(-R))/2 = R := by ring
    rw [hlim] at h
    have he (r : ℝ) : sourceInterval (x-R*r) (x+R*r) =
        sourceInterval (x+r*(-R)) (x+r*R) := by
      congr 1 <;> ring
    simpa only [localMass,he] using h
  have hm : ∀ᶠ h : ℝ in 𝓝[>] 0,0 < localMass μ x h :=
    (eventually_local_mass_and_central_fraction μ hfloor x w hw hx 1 (by norm_num)).mono
      (fun h hh => hh.1)
  have hmR := (radius_mul_tendsto R hR0).eventually hm
  let C := ((1-b)^2)⁻¹
  have hC : 0 < C := inv_pos.mpr (sq_pos_of_pos (sub_pos.mpr hb1))
  intro ε hε
  let η := ε/(2*(R+C+2))
  have hη : 0 < η := div_pos hε (by positivity)
  have hηeq : 2*(R+C+2)*η=ε := by dsimp [η]; field_simp
  have hr := hratio.eventually (Metric.ball_mem_nhds R (lt_min hη zero_lt_one))
  have hk := weak_exterior_kernel_filter (fun h => tangentProbability μ x (R*h))
    uniformSegmentProbability hτ (-(1/R)) (1/R)
    (uniformSegment_interval_null_frontier _ _ (by
      have hr : 0 < 1/R := one_div_pos.mpr hR0
      linarith))
    (annulusKernel R b) (continuous_annulusKernel R b hb1) η hη
  filter_upwards [self_mem_nhdsWithin,hm,hmR,hr,hk] with h hh hmh hmRh hrh hkh
  intro u hu
  have huz : u/b ∈ Segment := by
    apply abs_le.mp
    rw [abs_div,abs_of_pos hb0]
    exact (div_le_one hb0).mpr hu
  let z : Segment := ⟨u/b,huz⟩
  have hzu : b*(z : ℝ)=u := by dsimp [z]; field_simp [hb0.ne']
  let a := localMass μ x (R*h)/localMass μ x h
  let J := ∫ t in (sourceInterval (-(1/R)) (1/R))ᶜ,
    annulusKernel R b (z,t) ∂(uniformSegmentProbability : Measure Segment)
  let Jh := ∫ t in (sourceInterval (-(1/R)) (1/R))ᶜ,
    annulusKernel R b (z,t) ∂(tangentProbability μ x (R*h) : Measure Segment)
  have haη : |a-R| < η := (Metric.mem_ball.mp hrh).trans_le (min_le_left _ _)
  have ha1 : |a-R| < 1 := (Metric.mem_ball.mp hrh).trans_le (min_le_right _ _)
  have ha : |a| ≤ R+1 := by
    have := abs_sub_le a R 0
    simp only [sub_zero,abs_of_pos hR0] at this
    linarith
  have hJ : |J| ≤ C := exterior_kernel_bound uniformSegmentProbability R b hb1 z
  have hJh : |Jh-J| < η := hkh z
  have he : annulusIntegral μ x h R u/localMass μ x h-annulusModel R u =
      a*(Jh-J)+(a-R)*J := by
    have hn := annulusIntegral_tangent μ x h R b hh hR hb0.le hb1 hmRh z
    rw [hzu] at hn
    have hnJ := uniform_annulusKernel R b hR hb0.le hb1 z
    rw [hzu] at hnJ
    have hRJ : R*J=annulusModel R u := by dsimp [J]; rw [hnJ]; field_simp [hR0.ne']
    dsimp only [a,Jh]
    rw [hn,← hRJ]
    ring
  rw [he]
  calc
    _ ≤ |a| * |Jh-J|+|a-R| * |J| := by simpa only [abs_mul] using abs_add_le (a*(Jh-J)) ((a-R)*J)
    _ ≤ (R+1)*|Jh-J|+|a-R| * C := add_le_add
      (mul_le_mul_of_nonneg_right ha (abs_nonneg _))
      (mul_le_mul_of_nonneg_left hJ (abs_nonneg _))
    _ < (R+1)*η+η*C := add_lt_add
      (mul_lt_mul_of_pos_left hJh (by positivity)) (mul_lt_mul_of_pos_right haη hC)
    _ < ε := by nlinarith

/-- The remote bound is used only as a helper input. The next public theorem
supplies it from the original source measure and retains no such hypothesis. -/
theorem second_limit_of_annulus_tail (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w K : ℝ) (hw : 0 < w)
    (hx : HasDerivAt (sourceCDF μ) w x) (hK : 0 < K)
    (htail : ∀ᶠ h : ℝ in 𝓝[>] 0,0 < localMass μ x h ∧
      ∀ R,2 ≤ R → ∀ u,|u| ≤ 1 → remoteSecondIntegral μ x h R u/localMass μ x h ≤ K/R)
    (b : ℝ) (hb0 : 0 < b) (hb1 : b < 1) :
    ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ), ∀ u, |u| ≤ b →
      |limitFieldJet μ 2 x h u-1/(1-u^2)| < ε := by
  intro ε hε
  let R := 2+4*(K+2)/ε
  have hR : 2 ≤ R := by
    dsimp only [R]
    exact le_add_of_nonneg_right (by positivity)
  have hR0 : 0 < R := by linarith
  have hsmall : (K+2)/R < ε/4 := by
    rw [div_lt_iff₀ hR0]
    dsimp [R]
    field_simp
    nlinarith
  filter_upwards [self_mem_nhdsWithin,htail,
    annulus_limit μ hfloor x w R b hw hx hR hb0 hb1 (ε/2) (half_pos hε)] with h hh ht hn
  intro u hu
  have hu1 : |u| < 1 := hu.trans_lt hb1
  have hpart := second_jet_partition μ x h R u hh hR hu1
  have hremote := ht.2 R hR u hu1.le
  have hnonneg : 0 ≤ remoteSecondIntegral μ x h R u/localMass μ x h := by
    unfold remoteSecondIntegral
    exact div_nonneg (integral_nonneg (fun _ => by positivity)) ht.1.le
  have hmodel := annulusModel_error R u hR hu1
  have hn' := hn u hu
  rw [hpart,add_div]
  have he : annulusIntegral μ x h R u/localMass μ x h+
      remoteSecondIntegral μ x h R u/localMass μ x h-1/(1-u^2) =
      (annulusIntegral μ x h R u/localMass μ x h-annulusModel R u)+
      (remoteSecondIntegral μ x h R u/localMass μ x h)+
      (annulusModel R u-1/(1-u^2)) := by ring
  rw [he]
  have htri := (abs_add_le
    ((annulusIntegral μ x h R u/localMass μ x h-annulusModel R u)+
      remoteSecondIntegral μ x h R u/localMass μ x h)
    (annulusModel R u-1/(1-u^2))).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  rw [abs_of_nonneg hnonneg] at htri
  have hsum : K/R+2/R=(K+2)/R := by ring
  linarith

/-- Actual h -> 0, compact-uniform second derivative limit at almost every
point left over from the constructed high-potential cover. -/
theorem ae_minimum_second_small_scale (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure,x ∉ highPotentialRegion μ →
      ∀ b,0 < b → b < 1 → ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] (0 : ℝ),
        ∀ u,|u| ≤ b → |limitFieldJet μ 2 x h u-1/(1-u^2)| < ε := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    ae_positive_CDF_derivative_on_minimum μ,ae_minimum_remote_second_tail μ]
    with x hx hder htail
  intro hnot b hb0 hb1
  have hfloor : potentialFloor μ ≠ ⊥ := by
    intro hbot
    exact hnot (by rw [highPotentialRegion_of_floor_bot μ hbot]; exact hx)
  obtain ⟨hd,hw⟩ := hder hnot
  obtain ⟨K,hK,hKtail⟩ := htail hnot
  exact second_limit_of_annulus_tail μ hfloor x (sourceDensity μ x) K hw hd hK hKtail b hb0 hb1

end Erdos1152.V5
