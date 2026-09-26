import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section
open scoped Topology Real
open Complex MeasureTheory Set Filter
namespace Erdos1152.V5

/-- The explicitly filled remainder after subtracting a finite list of simple poles. -/
def poleRemainder (f h : ℂ → ℂ) (s : Finset ℂ) (z : ℂ) : ℂ :=
  if z ∈ s then
    deriv (fun w => f w / dslope h z w) z -
      ∑ a ∈ s.erase z, (f a / deriv h a) / (z-a)
  else f z / h z - ∑ a ∈ s, (f a / deriv h a) / (z-a)

private theorem differentiableAt_dslope_of_entire (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (a z : ℂ) : DifferentiableAt ℂ (dslope f a) z := by
  exact (differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope (s := univ) (c := a) (by simp)).mpr
      hf.differentiableOn)) z

private theorem local_quotient_sub_pole {f h : ℂ → ℂ} {a z : ℂ}
    (ha : h a=0) (hda : deriv h a≠0) (hz : z≠a) (hhz : dslope h a z≠0) :
    f z/h z-(f a/deriv h a)/(z-a)=
      dslope (fun w => f w/dslope h a w) a z := by
  have hfact : h z=(z-a)*dslope h a z := by
    simpa [smul_eq_mul,ha] using (sub_smul_dslope h a z).symm
  rw [dslope_of_ne (fun w => f w/dslope h a w) hz]
  simp only [slope,dslope_same,smul_eq_mul,vsub_eq_sub]
  rw [hfact]
  field_simp [sub_ne_zero.mpr hz,hda,hhz]
  <;> ring

/-- The remainder is holomorphic at each actual simple zero.  No general residue
 theorem is assumed: the local formula is a divided difference of `f / dslope h a`. -/
theorem differentiableAt_poleRemainder_at_node
    (f h : ℂ → ℂ) (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (s : Finset ℂ) {a : ℂ} (ha : a∈s) (hzero : h a=0)
    (hsimple : deriv h a≠0) : DifferentiableAt ℂ (poleRemainder f h s) a := by
  classical
  let q : ℂ → ℂ := fun z => f z/dslope h a z
  have hds := differentiableAt_dslope_of_entire h hh a a
  have hq : DifferentiableAt ℂ q a :=
    (hf a).div hds (by simpa using hsimple)
  have hqnear : ∀ᶠz in 𝓝 a, DifferentiableAt ℂ q z := by
    filter_upwards [hds.continuousAt.eventually_ne (by simpa using hsimple)] with z hz
    exact (hf z).div (differentiableAt_dslope_of_entire h hh a z) hz
  have hdsq : DifferentiableAt ℂ (dslope q a) a := by
    obtain ⟨U,hUs,hU,haU⟩ := mem_nhds_iff.mp hqnear
    exact ((Complex.differentiableOn_dslope (hU.mem_nhds haU)).mpr
      (fun z hz => (hUs hz).differentiableWithinAt)).differentiableAt (hU.mem_nhds haU)
  have havoid : ∀ᶠz in 𝓝 a, ∀b∈s.erase a,z≠b := by
    apply (Filter.eventually_all_finset _).mpr
    intro b hb
    exact eventually_ne_nhds (Finset.mem_erase.mp hb).1.symm
  have hdn : ∀ᶠz in 𝓝 a, dslope h a z≠0 :=
    hds.continuousAt.eventually_ne (by simpa using hsimple)
  have heq : poleRemainder f h s =ᶠ[𝓝 a]
      fun z => dslope q a z-∑b∈s.erase a,(f b/deriv h b)/(z-b) := by
    filter_upwards [havoid,hdn] with z hz hdz
    by_cases hza : z=a
    · subst z
      simp [poleRemainder,ha,q,dslope_same]
    · have hzs : z∉s := by
        intro hmem
        exact hz z (Finset.mem_erase.mpr ⟨hza,hmem⟩) rfl
      rw [poleRemainder,if_neg hzs,←Finset.add_sum_erase s
        (fun b => (f b/deriv h b)/(z-b)) ha]
      rw [←sub_sub]
      congr 1
      exact local_quotient_sub_pole hzero hsimple hza hdz
  apply DifferentiableAt.congr_of_eventuallyEq _ heq
  apply hdsq.sub
  apply DifferentiableAt.fun_sum
  intro b hb
  exact (differentiableAt_const (f b/deriv h b)).div
    ((hasDerivAt_id a).sub_const b).differentiableAt
    (sub_ne_zero.mpr (Finset.mem_erase.mp hb).1.symm)

private theorem differentiableAt_poleRemainder_off_nodes
    (f h : ℂ → ℂ) (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (s : Finset ℂ) {z : ℂ} (hz : z∉s) (hhz : h z≠0) :
    DifferentiableAt ℂ (poleRemainder f h s) z := by
  classical
  have havoid : ∀ᶠw in 𝓝 z,w∉s := s.finite_toSet.isClosed.isOpen_compl.mem_nhds hz
  have heq : poleRemainder f h s =ᶠ[𝓝 z]
      fun w => f w/h w-∑a∈s,(f a/deriv h a)/(w-a) := by
    filter_upwards [havoid] with w hw
    simp [poleRemainder,hw]
  apply DifferentiableAt.congr_of_eventuallyEq _ heq
  refine ((hf z).div (hh z) hhz).sub ?_
  apply DifferentiableAt.fun_sum
  intro a ha
  exact (differentiableAt_const (f a/deriv h a)).div
    ((hasDerivAt_id z).sub_const a).differentiableAt
    (sub_ne_zero.mpr (fun h => hz (h.symm ▸ ha)))

/-- A finite simple-pole formula on a disk, derived by explicit pole subtraction. -/
theorem circleIntegral_finite_simple_poles
    (f h : ℂ → ℂ) (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (s : Finset ℂ) (c : ℂ) (R : ℝ) (hR : 0<R)
    (hin : ∀a∈s,a∈Metric.ball c R)
    (hzero : ∀a∈s,h a=0) (hsimple : ∀a∈s,deriv h a≠0)
    (hall : ∀z∈Metric.closedBall c R,h z=0→z∈s) :
    ∮z in C(c,R), f z/h z = (2*Real.pi*Complex.I)*∑a∈s,f a/deriv h a := by
  classical
  have hd : ∀z∈Metric.closedBall c R,
      DifferentiableAt ℂ (poleRemainder f h s) z := by
    intro z hz
    by_cases hzs : z∈s
    · exact differentiableAt_poleRemainder_at_node f h hf hh s hzs
        (hzero z hzs) (hsimple z hzs)
    · exact differentiableAt_poleRemainder_off_nodes f h hf hh s hzs
        (fun hh0 => hzs (hall z hz hh0))
  have hrem : ∮z in C(c,R),poleRemainder f h s z=0 := by
    apply DiffContOnCl.circleIntegral_eq_zero hR.le
    refine ⟨fun z hz => (hd z (Metric.ball_subset_closedBall hz)).differentiableWithinAt,?_⟩
    rw [closure_ball c hR.ne']
    exact fun z hz => (hd z hz).continuousAt.continuousWithinAt
  have haway (z : ℂ) (hz : z∈Metric.sphere c R) : z∉s := by
    intro hzs
    exact Metric.sphere_disjoint_ball.ne_of_mem hz (hin z hzs) rfl
  have hnonzero (z : ℂ) (hz : z∈Metric.sphere c R) : h z≠0 :=
    fun hz0 => haway z hz (hall z (Metric.sphere_subset_closedBall hz) hz0)
  have hfi : CircleIntegrable (fun z => f z/h z) c R :=
    ContinuousOn.circleIntegrable hR.le
      (hf.continuous.continuousOn.div hh.continuous.continuousOn hnonzero)
  have hpi (a : ℂ) (ha : a∈s) :
      CircleIntegrable (fun z => (f a/deriv h a)/(z-a)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
      (fun z hz => sub_ne_zero.mpr (Metric.sphere_disjoint_ball.ne_of_mem hz (hin a ha)))
  have hp := CircleIntegrable.fun_sum s (fun a ha => hpi a ha)
  have hex : ∮z in C(c,R),poleRemainder f h s z =
      (∮z in C(c,R),f z/h z)-∑a∈s,∮z in C(c,R),(f a/deriv h a)/(z-a) := by
    rw [circleIntegral.integral_congr hR.le (fun z hz =>
      show poleRemainder f h s z=f z/h z-∑a∈s,(f a/deriv h a)/(z-a) by
        simp [poleRemainder,haway z hz]),
      circleIntegral.integral_sub hfi hp,circleIntegral.integral_fun_sum]
    exact fun a ha => hpi a ha
  rw [hex] at hrem
  apply sub_eq_zero.mp at hrem
  rw [hrem]
  have hterm : ∀a∈s,(∮z in C(c,R),(f a/deriv h a)/(z-a)) =
      (f a/deriv h a)*(2*Real.pi*Complex.I) := by
    intro a ha
    simp_rw [div_eq_mul_inv,circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_inv_of_mem_ball (hin a ha)]
  rw [Finset.sum_congr rfl hterm,←Finset.sum_mul,mul_comm]

/-- Cauchy interpolation with the same finite simple poles. -/
theorem cauchy_finite_simple_poles
    (f h : ℂ → ℂ) (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (s : Finset ℂ) (c ξ : ℂ) (R : ℝ) (hR : 0<R)
    (hξ : ξ∈Metric.ball c R) (hξh : h ξ≠0)
    (hin : ∀a∈s,a∈Metric.ball c R)
    (hzero : ∀a∈s,h a=0) (hsimple : ∀a∈s,deriv h a≠0)
    (hall : ∀z∈Metric.closedBall c R,h z=0→z∈s) :
    (2*Real.pi*Complex.I)⁻¹*(∮z in C(c,R),(f z/h z)/(z-ξ)) =
      f ξ/h ξ-∑a∈s,(f a/deriv h a)/(ξ-a) := by
  classical
  let H : ℂ→ℂ := fun z => h z*(z-ξ)
  have hξs : ξ∉s := fun hhx => hξh (hzero ξ hhx)
  have hH (a : ℂ) : deriv H a=deriv h a*(a-ξ)+h a := by
    simpa only [H, mul_one, Pi.mul_def, id_eq] using
      ((hh a).hasDerivAt.mul ((hasDerivAt_id a).sub_const ξ)).deriv
  have hin' : ∀a∈insert ξ s,a∈Metric.ball c R := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · exact hξ
    · exact hin a ha
  have hzero' : ∀a∈insert ξ s,H a=0 := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl|ha
    · simp [H]
    · simp [H,hzero a ha]
  have hsimple' : ∀a∈insert ξ s,deriv H a≠0 := by
    intro a ha
    rw [hH]
    rcases Finset.mem_insert.mp ha with rfl|ha
    · simpa using hξh
    · rw [hzero a ha,add_zero]
      exact mul_ne_zero (hsimple a ha) (sub_ne_zero.mpr (fun haξ => hξs (haξ ▸ ha)))
  have hall' : ∀z∈Metric.closedBall c R,H z=0→z∈insert ξ s := by
    intro z hz hhz
    rcases mul_eq_zero.mp hhz with hhz|hhz
    · exact Finset.mem_insert_of_mem (hall z hz hhz)
    · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp hhz))
  have heq := circleIntegral_finite_simple_poles f H hf
    (hh.mul (differentiable_id.sub_const ξ)) (insert ξ s) c R hR
    hin' hzero' hsimple' hall'
  have h2π : (2*Real.pi*Complex.I:ℂ)≠0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  rw [Finset.sum_insert hξs,hH] at heq
  simp only [sub_self,mul_zero,zero_add] at heq
  have hterms : ∑a∈s,f a/deriv H a = -∑a∈s,(f a/deriv h a)/(ξ-a) := by
    rw [←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [hH,hzero a ha,add_zero,←neg_sub ξ a]
    simp only [mul_neg,div_neg,div_div]
  rw [hterms] at heq
  have hfun : (fun z => (f z/h z)/(z-ξ))=(fun z => f z/H z) := by
    ext z
    simp only [H,div_div]
  rw [hfun,heq,←mul_assoc,inv_mul_cancel₀ h2π,one_mul]
  exact (sub_eq_add_neg _ _).symm

end Erdos1152.V5
