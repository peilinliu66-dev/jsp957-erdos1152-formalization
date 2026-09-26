import Erdos1152.V4.ExternalFieldLimit

/-!
# The limiting kernels are the actual first two derivatives

This removes a possible ambiguity in a statement of "C² convergence":
`limitFieldJet μ 1` and `limitFieldJet μ 2` are proved to be the derivatives
of the integral defining `limitFieldJet μ 0`, rather than just three unrelated
kernel integrals. No smoothness of the source probability measure is assumed.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

namespace Erdos1152.V4

theorem exterior_point_gap {a h u : ℝ} {t : Segment}
    (hh : 0 < h) (hu : |u| < 1) (ht : t ∉ sourceInterval (a-h) (a+h)) :
    h*(1-|u|) ≤ |a+h*u-(t : ℝ)| := by
  have hside : (t : ℝ) ≤ a-h ∨ a+h ≤ (t : ℝ) := by
    by_cases hl : (t : ℝ) ≤ a-h
    · exact Or.inl hl
    · exact Or.inr (le_of_not_gt (fun hr => ht ⟨lt_of_not_ge hl,hr⟩))
  rcases hside with hl | hr
  · have hm := mul_le_mul_of_nonneg_left (neg_le_abs u) hh.le
    exact (by nlinarith : h*(1-|u|) ≤ a+h*u-(t : ℝ)).trans (le_abs_self _)
  · have hm := mul_le_mul_of_nonneg_left (le_abs_self u) hh.le
    exact (by nlinarith : h*(1-|u|) ≤ -(a+h*u-(t : ℝ))).trans (neg_le_abs _)

theorem exterior_point_nonzero {a h u : ℝ} {t : Segment}
    (hh : 0 < h) (hu : |u| < 1) (ht : t ∉ sourceInterval (a-h) (a+h)) :
    a+h*u-(t : ℝ) ≠ 0 :=
  abs_pos.mp ((mul_pos hh (sub_pos.mpr hu)).trans_le (exterior_point_gap hh hu ht))

theorem rawFieldJet_hasDeriv_zero (a h u : ℝ) (t : Segment)
    (hh : 0 < h) (hu : |u| < 1) (ht : t ∉ sourceInterval (a-h) (a+h)) :
    HasDerivAt (fun v => rawFieldJet 0 a h v (t : ℝ))
      (rawFieldJet 1 a h u (t : ℝ)) u := by
  have hn := exterior_point_nonzero hh hu ht
  have hd := (((hasDerivAt_id u).const_mul h).const_add a).sub_const (t : ℝ)
  convert! ((hd.log hn).sub_const (Real.log (a-(t : ℝ)))).neg using 1 <;>
    simp [rawFieldJet, neg_div]

theorem rawFieldJet_hasDeriv_one (a h u : ℝ) (t : Segment)
    (hh : 0 < h) (hu : |u| < 1) (ht : t ∉ sourceInterval (a-h) (a+h)) :
    HasDerivAt (fun v => rawFieldJet 1 a h v (t : ℝ))
      (rawFieldJet 2 a h u (t : ℝ)) u := by
  have hn := exterior_point_nonzero hh hu ht
  convert! (hasDerivAt_const u (-h)).div
    ((((hasDerivAt_id u).const_mul h).const_add a).sub_const (t : ℝ)) hn using 1 <;>
    simp [rawFieldJet, pow_two]

theorem rawFieldJet_continuousAt (j : Fin 3) (a h u : ℝ) (t : Segment)
    (hh : 0 < h) (hu : |u| < 1) (ht : t ∉ sourceInterval (a-h) (a+h)) :
    ContinuousAt (fun v => rawFieldJet j a h v (t : ℝ)) u := by
  have hn := exterior_point_nonzero hh hu ht
  fin_cases j <;> simp [rawFieldJet]
  all_goals fun_prop (disch := first | exact hn | exact pow_ne_zero 2 hn)

theorem rawFieldJet_integrable_exterior (μ : ProbabilityMeasure Segment) (j : Fin 3)
    (a h u : ℝ) (hh : 0 < h) (hu : |u| < 1) :
    IntegrableOn (fun t : Segment => rawFieldJet j a h u (t : ℝ))
      (sourceInterval (a-h) (a+h))ᶜ (μ : Measure Segment) := by
  let b : ℝ := (1+|u|)/2
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hub : |u| ≤ b := by dsimp [b]; linarith
  have hx : u/b ∈ Segment := by
    constructor
    · exact (le_div_iff₀ hb0).mpr (by nlinarith [neg_le_abs u])
    · exact (div_le_one hb0).mpr ((le_abs_self u).trans hub)
  let x : Segment := ⟨u/b,hx⟩
  have hbx : b*(x : ℝ)=u := by dsimp [x]; field_simp
  have hc : Continuous (fun t : Segment => clippedFieldJet j a h b (x,t)) :=
    (continuous_clippedFieldJet j a h b hh hb1).comp (continuous_const.prodMk continuous_id)
  have hi := (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    (μ := (μ : Measure Segment))).integrableOn (s := (sourceInterval (a-h) (a+h))ᶜ)
  apply hi.congr
  filter_upwards [ae_restrict_mem (measurableSet_sourceInterval (a-h) (a+h)).compl] with t ht
  simpa only [hbx] using clippedFieldJet_eq_exterior j a h b x t hh hb0.le hb1 ht

/-- Compact parameter/source boundedness is used only after an explicit
continuous extension has been proved to agree with the exterior kernel. -/
theorem rawFieldJet_local_uniform_bound (j : Fin 3) (a h b : ℝ)
    (hh : 0 < h) (hb0 : 0 < b) (hb1 : b < 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u, |u| ≤ b → ∀ t : Segment,
      t ∉ sourceInterval (a-h) (a+h) → |rawFieldJet j a h u (t : ℝ)| ≤ M := by
  obtain ⟨C,hC⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Segment × Segment))).exists_bound_of_continuousOn
    (continuous_clippedFieldJet j a h b hh hb1).continuousOn
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro u hu t ht
  have hx : u/b ∈ Segment := by
    constructor
    · exact (le_div_iff₀ hb0).mpr (by nlinarith [neg_le_abs u])
    · exact (div_le_one hb0).mpr ((le_abs_self u).trans hu)
  let x : Segment := ⟨u/b,hx⟩
  have hbx : b*(x : ℝ)=u := by dsimp [x]; field_simp
  have he := clippedFieldJet_eq_exterior j a h b x t hh hb0.le hb1 ht
  rw [hbx] at he
  rw [← he]
  have hbound : |clippedFieldJet j a h b (x,t)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (x,t) (Set.mem_univ _)
  exact hbound.trans (le_max_right _ _)

/-- Every limiting jet is continuous at every interior local coordinate. -/
theorem continuousAt_limitFieldJet (μ : ProbabilityMeasure Segment) (j : Fin 3)
    (a h u : ℝ) (hh : 0 < h) (hu : |u| < 1) :
    ContinuousAt (limitFieldJet μ j a h) u := by
  let b : ℝ := (1+|u|)/2
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hub : |u| < b := by dsimp [b]; linarith
  have hn : Ioo (-b) b ∈ 𝓝 u := Ioo_mem_nhds (by linarith [neg_le_abs u])
    ((le_abs_self u).trans_lt hub)
  obtain ⟨M,hM0,hM⟩ := rawFieldJet_local_uniform_bound j a h b hh hb0 hb1
  have hc : ContinuousAt (fun v => ∫ t in (sourceInterval (a-h) (a+h))ᶜ,
      rawFieldJet j a h v (t : ℝ) ∂(μ : Measure Segment)) u := by
    apply continuousAt_of_dominated
      (bound := fun _ : Segment => M)
    · filter_upwards with v
      apply Measurable.aestronglyMeasurable
      fin_cases j <;> simp [rawFieldJet] <;> fun_prop
    · filter_upwards [hn] with v hv
      filter_upwards [ae_restrict_mem (measurableSet_sourceInterval (a-h) (a+h)).compl] with t ht
      simpa only [Real.norm_eq_abs] using hM v (abs_le.mpr ⟨hv.1.le,hv.2.le⟩) t ht
    · exact integrable_const _
    · filter_upwards [ae_restrict_mem (measurableSet_sourceInterval (a-h) (a+h)).compl] with t ht
      exact rawFieldJet_continuousAt j a h u t hh hu ht
  exact hc.div_const _

private theorem hasDerivAt_integral_field_step (μ : ProbabilityMeasure Segment)
    (i j : Fin 3) (a h u : ℝ) (hh : 0 < h) (hu : |u| < 1)
    (hstep : ∀ v, |v| < 1 → ∀ t : Segment, t ∉ sourceInterval (a-h) (a+h) →
      HasDerivAt (fun z => rawFieldJet i a h z (t : ℝ)) (rawFieldJet j a h v (t : ℝ)) v) :
    HasDerivAt (limitFieldJet μ i a h) (limitFieldJet μ j a h u) u := by
  let b : ℝ := (1+|u|)/2
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hb1 : b < 1 := by dsimp [b]; linarith
  have hub : |u| < b := by dsimp [b]; linarith
  have hn : Ioo (-b) b ∈ 𝓝 u := Ioo_mem_nhds (by linarith [neg_le_abs u])
    ((le_abs_self u).trans_lt hub)
  obtain ⟨M,hM0,hM⟩ := rawFieldJet_local_uniform_bound j a h b hh hb0 hb1
  have hd : HasDerivAt
      (fun v => ∫ t in (sourceInterval (a-h) (a+h))ᶜ, rawFieldJet i a h v (t : ℝ) ∂(μ : Measure Segment))
      (∫ t in (sourceInterval (a-h) (a+h))ᶜ, rawFieldJet j a h u (t : ℝ) ∂(μ : Measure Segment)) u := by
    apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := (μ : Measure Segment).restrict (sourceInterval (a-h) (a+h))ᶜ)
      (F := fun v (t : Segment) => rawFieldJet i a h v (t : ℝ))
      (F' := fun v (t : Segment) => rawFieldJet j a h v (t : ℝ))
      (bound := fun _ : Segment => M) hn ?_
      (rawFieldJet_integrable_exterior μ i a h u hh hu)
      (rawFieldJet_integrable_exterior μ j a h u hh hu).aestronglyMeasurable ?_
      (integrable_const _) ?_).2
    · filter_upwards [hn] with v hv
      exact (rawFieldJet_integrable_exterior μ i a h v hh
        ((abs_lt.mpr hv).trans hb1)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem (measurableSet_sourceInterval (a-h) (a+h)).compl] with t ht
      intro v hv
      simpa only [Real.norm_eq_abs] using hM v (abs_le.mpr ⟨hv.1.le,hv.2.le⟩) t ht
    · filter_upwards [ae_restrict_mem (measurableSet_sourceInterval (a-h) (a+h)).compl] with t ht
      intro v hv
      exact hstep v ((abs_lt.mpr hv).trans hb1) t ht
  exact hd.div_const _

/-- Derivative statements actually instantiate the private step lemma with
proved elementary log/reciprocal derivatives; no derivative input remains. -/
theorem hasDerivAt_limitField (μ : ProbabilityMeasure Segment) (a h u : ℝ)
    (hh : 0 < h) (hu : |u| < 1) :
    HasDerivAt (limitFieldJet μ 0 a h) (limitFieldJet μ 1 a h u) u :=
  hasDerivAt_integral_field_step μ 0 1 a h u hh hu
    (fun v hv t ht => rawFieldJet_hasDeriv_zero a h v t hh hv ht)

theorem hasDerivAt_limitFieldFirst (μ : ProbabilityMeasure Segment) (a h u : ℝ)
    (hh : 0 < h) (hu : |u| < 1) :
    HasDerivAt (limitFieldJet μ 1 a h) (limitFieldJet μ 2 a h u) u :=
  hasDerivAt_integral_field_step μ 1 2 a h u hh hu
    (fun v hv t ht => rawFieldJet_hasDeriv_one a h v t hh hv ht)

end Erdos1152.V4
