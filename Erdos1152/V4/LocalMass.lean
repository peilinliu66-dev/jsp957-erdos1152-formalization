import Erdos1152.V4.ExternalFieldLimit
import Mathlib.Probability.CDF
import Mathlib.Analysis.Calculus.Monotone

/-!
# Actual one-sided tangent masses and the central good-box count

The monotone CDF is differentiable almost everywhere. Its derivative is
identified with the previously constructed Radon--Nikodym density by the
symmetric-ball limit. This proves local interval-mass ratios, and hence the
central node-count input, with the local scale chosen before finite deletion.
-/

open MeasureTheory Set Filter Topology Metric ProbabilityTheory
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def sourceCDF (μ : ProbabilityMeasure Segment) : ℝ → ℝ :=
  cdf (realSource μ)

theorem sourceCDF_mono (μ : ProbabilityMeasure Segment) : Monotone (sourceCDF μ) :=
  monotone_cdf (realSource μ)

theorem realSource_Ioc (μ : ProbabilityMeasure Segment) (a b : ℝ) (hab : a ≤ b) :
    (realSource μ).real (Ioc a b) = sourceCDF μ b-sourceCDF μ a := by
  have he : realSource μ (Ioc a b) = ENNReal.ofReal (sourceCDF μ b-sourceCDF μ a) := by
    rw [← measure_cdf (realSource μ), StieltjesFunction.measure_Ioc]
    rfl
  change (realSource μ (Ioc a b)).toReal = _
  rw [he, ENNReal.toReal_ofReal (sub_nonneg.mpr (sourceCDF_mono μ hab))]

theorem realSource_Ioo (μ : ProbabilityMeasure Segment) (hfloor : potentialFloor μ ≠ ⊥)
    (a b : ℝ) (hab : a ≤ b) :
    (realSource μ).real (Ioo a b) = sourceCDF μ b-sourceCDF μ a := by
  have he : (Ioo a b : Set ℝ) =ᵐ[realSource μ] Ioc a b := by
    filter_upwards [compl_mem_ae_iff.mpr (realSource_singleton_zero_of_floor_ne_bot μ hfloor b)] with x hx
    have hxb : x ≠ b := hx
    apply propext
    exact ⟨fun h => Ioo_subset_Ioc_self h, fun h => ⟨h.1,lt_of_le_of_ne h.2 hxb⟩⟩
  have hm := measure_congr he
  change (realSource μ (Ioo a b)).toReal = _
  rw [hm]
  exact realSource_Ioc μ a b hab

theorem realSource_Icc (μ : ProbabilityMeasure Segment) (hfloor : potentialFloor μ ≠ ⊥)
    (a b : ℝ) (hab : a ≤ b) :
    (realSource μ).real (Icc a b) = sourceCDF μ b-sourceCDF μ a := by
  have he : (Icc a b : Set ℝ) =ᵐ[realSource μ] Ioc a b := by
    filter_upwards [compl_mem_ae_iff.mpr (realSource_singleton_zero_of_floor_ne_bot μ hfloor a)] with x hx
    have hxa : x ≠ a := hx
    apply propext
    exact ⟨fun h => ⟨lt_of_le_of_ne h.1 (Ne.symm hxa),h.2⟩,fun h => Ioc_subset_Icc_self h⟩
  have hm := measure_congr he
  change (realSource μ (Icc a b)).toReal = _
  rw [hm]
  exact realSource_Ioc μ a b hab

theorem sourceInterval_real_eq_CDF (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (a b : ℝ) (hab : a ≤ b) :
    (μ : Measure Segment).real (sourceInterval a b) = sourceCDF μ b-sourceCDF μ a := by
  have he := realSource_apply μ (Ioo a b) measurableSet_Ioo
  simpa only [sourceInterval, Measure.real, ← he] using realSource_Ioo μ hfloor a b hab

/-- A derivative gives every fixed one-sided tangent slope, with either sign
of v and without silently assuming symmetric differentiation suffices. -/
theorem tangent_CDF_slope (μ : ProbabilityMeasure Segment) (x w v : ℝ)
    (hx : HasDerivAt (sourceCDF μ) w x) :
    Tendsto (fun h : ℝ => (sourceCDF μ (x+h*v)-sourceCDF μ x)/h)
      (𝓝[>] 0) (𝓝 (w*v)) := by
  have ha : HasDerivAt (fun h : ℝ => x+h*v) v 0 := by
    simpa only [id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const v).const_add x
  have hx' : HasDerivAt (sourceCDF μ) w (x+(0 : ℝ)*v) := by simpa using hx
  have hc := hx'.comp 0 ha
  have ht := hc.tendsto_slope_zero.mono_left
    (nhdsWithin_mono (0 : ℝ) (show Ioi (0 : ℝ) ⊆ ({0} : Set ℝ)ᶜ from fun t ht => ne_of_gt ht))
  simpa only [Function.comp_def, zero_add, zero_mul, mul_zero, add_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht

theorem tangent_interval_mass (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w α β : ℝ) (hαβ : α ≤ β)
    (hx : HasDerivAt (sourceCDF μ) w x) :
    Tendsto (fun h : ℝ => (μ : Measure Segment).real
      (sourceInterval (x+h*α) (x+h*β))/h) (𝓝[>] 0) (𝓝 (w*(β-α))) := by
  have ht := (tangent_CDF_slope μ x w β hx).sub (tangent_CDF_slope μ x w α hx)
  have he : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (μ : Measure Segment).real (sourceInterval (x+h*α) (x+h*β))/h =
        (sourceCDF μ (x+h*β)-sourceCDF μ x)/h -
          (sourceCDF μ (x+h*α)-sourceCDF μ x)/h := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    rw [sourceInterval_real_eq_CDF μ hfloor _ _ (by nlinarith [hαβ] : x+h*α ≤ x+h*β)]
    ring
  convert ht.congr' (Filter.EventuallyEq.symm he) using 1
  ring

/-- Identify the actual CDF derivative with the actual source density. -/
theorem CDF_derivative_eq_density (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w : ℝ)
    (hx : HasDerivAt (sourceCDF μ) w x)
    (hd : Tendsto (fun r : ℝ => (realSource μ).real (closedBall x r)/(2*r))
      (𝓝[>] 0) (𝓝 (sourceDensity μ x))) : w = sourceDensity μ x := by
  have ht := (tangent_interval_mass μ hfloor x w (-1) 1 (by norm_num) hx).div_const 2
  have he : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (μ : Measure Segment).real (sourceInterval (x+r*(-1)) (x+r*1))/r/2 =
        (realSource μ).real (closedBall x r)/(2*r) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    change 0 < r at hr
    rw [Real.closedBall_eq_Icc, realSource_Icc μ hfloor _ _ (by linarith),
      sourceInterval_real_eq_CDF μ hfloor _ _ (by nlinarith)]
    simp only [mul_neg_one, mul_one, ← sub_eq_add_neg]
    ring
  have ht' := ht.congr' he
  have hw : w*(1-(-1))/2 = w := by ring
  rw [hw] at ht'
  exact tendsto_nhds_unique ht' hd

/-- The finite positive derivative is supplied at almost every true minimum
point. Neither the derivative nor its positivity is a terminal hypothesis. -/
theorem ae_positive_CDF_derivative_on_minimum (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, x ∉ highPotentialRegion μ →
      HasDerivAt (sourceCDF μ) (sourceDensity μ x) x ∧ 0 < sourceDensity μ x := by
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_positive_density_on_minimum μ,
    ae_restrict_of_ae (sourceCDF_mono μ).ae_differentiableAt,
    ae_restrict_of_ae (ae_sourceDensity_limit μ)] with x hxseg hp hx hd
  intro hnot
  have hfloor : potentialFloor μ ≠ ⊥ := by
    intro hf
    exact hnot (by
      rw [highPotentialRegion_of_floor_bot μ hf]
      exact hxseg)
  have he := CDF_derivative_eq_density μ hfloor x (deriv (sourceCDF μ) x) hx.hasDerivAt hd
  exact ⟨he ▸ hx.hasDerivAt, (hp hnot).2⟩

/-- Every fixed relative interval has the uniform tangent probability mass.
In particular [-1/4,1/4] has limiting fraction 1/4. -/
theorem local_relative_interval_mass (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w α β : ℝ) (hw : 0 < w) (hαβ : α ≤ β)
    (hx : HasDerivAt (sourceCDF μ) w x) :
    Tendsto (fun h : ℝ => (μ : Measure Segment).real (sourceInterval (x+h*α) (x+h*β)) /
      (μ : Measure Segment).real (sourceInterval (x-h) (x+h)))
      (𝓝[>] 0) (𝓝 ((β-α)/2)) := by
  have hnum := tangent_interval_mass μ hfloor x w α β hαβ hx
  have hden := tangent_interval_mass μ hfloor x w (-1) 1 (by norm_num) hx
  have ht := hnum.div hden (by positivity : w*(1-(-1)) ≠ 0)
  have he : ∀ᶠ h : ℝ in 𝓝[>] 0,
      ((μ : Measure Segment).real (sourceInterval (x+h*α) (x+h*β))/h) /
        ((μ : Measure Segment).real (sourceInterval (x+h*(-1)) (x+h*1))/h) =
      (μ : Measure Segment).real (sourceInterval (x+h*α) (x+h*β)) /
        (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    change 0 < h at hh
    simp only [mul_neg_one, mul_one, ← sub_eq_add_neg]
    by_cases hm : (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) = 0
    · simp only [hm, zero_div, div_zero]
    · field_simp [hh.ne']
  convert ht.congr' he using 1
  field_simp <;> ring

/-- Positive local mass and the exact central counting tolerance required by
the good-box argument hold for all sufficiently small h at each good point. -/
theorem eventually_local_mass_and_central_fraction (μ : ProbabilityMeasure Segment)
    (hfloor : potentialFloor μ ≠ ⊥) (x w : ℝ) (hw : 0 < w)
    (hx : HasDerivAt (sourceCDF μ) w x) (ρ : ℕ) (hρ : 0 < ρ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      0 < (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) ∧
      (μ : Measure Segment).real (sourceInterval (x-h/4) (x+h/4)) /
        (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) < 1/4+1/(32*(ρ : ℝ)) := by
  have hpos := (tangent_interval_mass μ hfloor x w (-1) 1 (by norm_num) hx).eventually
    (lt_mem_nhds (by nlinarith : (0 : ℝ) < w*(1-(-1))))
  have hsmall := (local_relative_interval_mass μ hfloor x w (-1/4) (1/4) hw (by norm_num) hx).eventually
    (gt_mem_nhds (by
      have hρ' : (0 : ℝ) < ρ := Nat.cast_pos.mpr hρ
      have hg : 0 < 1 / (32 * (ρ : ℝ)) := by positivity
      norm_num
      linarith : ((1/4 : ℝ)-(-1/4))/2 < 1/4+1/(32*(ρ : ℝ))))
  filter_upwards [self_mem_nhdsWithin,hpos,hsmall] with h hh hp hs
  change 0 < h at hh
  have hmass : 0 < (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) := by
    have h := (div_pos_iff.mp hp)
    simp only [mul_neg_one, mul_one, ← sub_eq_add_neg] at h
    exact h.elim (fun h => h.1) (fun h => (not_lt_of_gt hh h.2).elim)
  refine ⟨hmass, ?_⟩
  simpa only [neg_div, mul_neg, mul_one_div, sub_eq_add_neg] using hs


/-- The central undeleted node fraction converges to the actual limiting
central mass ratio, with no unproved counting input. -/
theorem central_node_fraction_tendsto (X : NodeArray) (rows : ℕ → ℕ)
    (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun k => V3.empiricalProbability X (rows k)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) (x h : ℝ) (hh : 0 < h)
    (hmass : 0 < (μ : Measure Segment).real (sourceInterval (x-h) (x+h)))
    (S : Finset Segment) :
    Tendsto (fun k => ((insideNodes (unassignedNodes X S (rows k)) x (h/4)).card : ℝ) /
      (insideNodes (unassignedNodes X S (rows k)) x h).card) atTop
      (𝓝 ((μ : Measure Segment).real (sourceInterval (x-h/4) (x+h/4)) /
        (μ : Measure Segment).real (sourceInterval (x-h) (x+h)))) := by
  have h1 := insideNodes_fraction_tendsto X rows hrows μ hμ hfloor x (h/4) (by positivity) S
  have h2 := insideNodes_fraction_tendsto X rows hrows μ hμ hfloor x h hh S
  have he (k : ℕ) :
      (((insideNodes (unassignedNodes X S (rows k)) x (h/4)).card : ℝ)/(rows k+1 : ℝ)) /
        (((insideNodes (unassignedNodes X S (rows k)) x h).card : ℝ)/(rows k+1 : ℝ)) =
      ((insideNodes (unassignedNodes X S (rows k)) x (h/4)).card : ℝ) /
        (insideNodes (unassignedNodes X S (rows k)) x h).card := by
    by_cases hzero : ((insideNodes (unassignedNodes X S (rows k)) x h).card : ℝ) = 0
    · simp only [hzero, zero_div, div_zero]
    · field_simp
  exact (h1.div h2 hmass.ne').congr' (Filter.Eventually.of_forall he)

theorem local_excess_fraction_tendsto (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0))
    (rows : ℕ → ℕ) (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun k => V3.empiricalProbability X (rows k)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) (x h : ℝ) (hh : 0 < h)
    (hmass : 0 < (μ : Measure Segment).real (sourceInterval (x-h) (x+h)))
    (S : Finset Segment) :
    Tendsto (fun k => ((r (rows k) : ℝ)+S.card) /
      (insideNodes (unassignedNodes X S (rows k)) x h).card) atTop (𝓝 0) := by
  have hnum := (hr.comp hrows).add (deletion_bound_tendsto_zero rows hrows S 1)
  have hden := insideNodes_fraction_tendsto X rows hrows μ hμ hfloor x h hh S
  have ht := hnum.div hden hmass.ne'
  have he (k : ℕ) :
      ((r (rows k) : ℝ)/(rows k+1 : ℝ)+(S.card : ℝ)*1/(rows k+1 : ℝ)) /
        (((insideNodes (unassignedNodes X S (rows k)) x h).card : ℝ)/(rows k+1 : ℝ)) =
      ((r (rows k) : ℝ)+S.card)/(insideNodes (unassignedNodes X S (rows k)) x h).card := by
    by_cases hzero : ((insideNodes (unassignedNodes X S (rows k)) x h).card : ℝ) = 0
    · simp only [hzero, zero_div, div_zero]
    · field_simp <;> ring
  simpa only [zero_add, zero_div] using ht.congr' (Filter.Eventually.of_forall he)

/-- Actual good-point scale selection. It already contains the quantifier
order needed for the original hm interface: rho and epsilon, then h, then
arbitrary finite S, then a sufficiently late original row. It supplies the
mass/count/degree inputs, but is not yet the missing peak construction. -/
theorem ae_minimum_choose_count_scale (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0))
    (ρ : ℕ) (hρ : 0 < ρ) :
    ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),
      x ∉ canonicalHighRegion X → ∀ ε > (0 : ℝ),
        ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧ -1 < x-h ∧ x+h < 1 ∧
          0 < (canonicalMeasure X : Measure Segment).real (sourceInterval (x-h) (x+h)) ∧
          ∀ S : Finset Segment,
            (∀ᶠ k in atTop,
              0 < (insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card ∧
              ((insideNodes (unassignedNodes X S (canonicalRows X k)) x (h/4)).card : ℝ) ≤
                (1/4+1/(16*(ρ : ℝ))) *
                  (insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card) ∧
            Tendsto (fun k => ((r (canonicalRows X k) : ℝ)+S.card)/
              (insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card)
                atTop (𝓝 0) := by
  let μ := canonicalMeasure X
  have hgood := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self :
    Ioo (-1 : ℝ) 1 ⊆ Icc (-1 : ℝ) 1) (ae_positive_CDF_derivative_on_minimum μ)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,hgood] with x hx hgoodx
  intro hnot ε hε
  have hnot' : x ∉ highPotentialRegion μ := hnot
  obtain ⟨hder,hpos⟩ := hgoodx hnot'
  have hf : potentialFloor μ ≠ ⊥ := by
    intro hbot
    apply hnot'
    rw [highPotentialRegion_of_floor_bot μ hbot]
    exact ⟨hx.1.le,hx.2.le⟩
  have hm := eventually_local_mass_and_central_fraction μ hf x (sourceDensity μ x) hpos hder ρ hρ
  let η := min ε (min (x+1) (1-x))
  have hη : 0 < η := lt_min hε (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < η :=
    mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hη)
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  obtain ⟨h,hh,hmh,hηh⟩ := (Filter.Eventually.and hpositive
    (Filter.Eventually.and hm hsmall)).exists
  obtain ⟨hlocal,hcentral⟩ := hmh
  refine ⟨h,hh, hηh.le.trans (min_le_left _ _), ?_, ?_, hlocal, ?_⟩
  · have hhx := hηh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  · have hhx := hηh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  intro S
  have hmass := insideNodes_fraction_tendsto X (canonicalRows X) (canonicalRows_tendsto X)
    μ (canonicalMeasure_weak X) hf x h hh S
  have hcounts := central_node_fraction_tendsto X (canonicalRows X) (canonicalRows_tendsto X)
    μ (canonicalMeasure_weak X) hf x h hh hlocal S
  have hmargin : (μ : Measure Segment).real (sourceInterval (x-h/4) (x+h/4)) /
      (μ : Measure Segment).real (sourceInterval (x-h) (x+h)) < 1/4+1/(16*(ρ : ℝ)) := by
    have hρ' : (0 : ℝ) < ρ := Nat.cast_pos.mpr hρ
    have hgap : (1 : ℝ)/(32*ρ) < 1/(16*ρ) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    linarith
  refine ⟨?_, local_excess_fraction_tendsto X r hr (canonicalRows X) (canonicalRows_tendsto X)
    μ (canonicalMeasure_weak X) hf x h hh hlocal S⟩
  filter_upwards [hmass.eventually (lt_mem_nhds hlocal),
    hcounts.eventually (gt_mem_nhds hmargin)] with k hk hc
  have hsR : 0 < ((insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card : ℝ) :=
    (div_pos_iff.mp hk).elim (fun h => h.1) (fun h =>
      (not_lt_of_ge (by positivity : (0 : ℝ) ≤ canonicalRows X k+1) h.2).elim)
  refine ⟨Nat.cast_pos.mp hsR, ?_⟩
  exact ((div_lt_iff₀ hsR).mp hc).le

end Erdos1152.V4
