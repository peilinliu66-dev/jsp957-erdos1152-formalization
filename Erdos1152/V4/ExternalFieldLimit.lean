import Erdos1152.V4.DeletedKernel
import Erdos1152.V4.FiniteFieldJet

/-!
# The actual fixed-scale row external field converges in C²

The three kernels below are the field, its first derivative and its second
 derivative. Their clipped continuous extensions agree with the actual kernels
on the exterior of I_h. Weak convergence, restriction and finite deletion are
all proved in preceding files and are instantiated here. The local scale h is
fixed before the arbitrary finite deleted set S; it is never chosen from S.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def rawFieldJet (j : Fin 3) (a h u t : ℝ) : ℝ :=
  if j = 0 then -(Real.log (a+h*u-t)-Real.log (a-t))
  else if j = 1 then -h/(a+h*u-t)
  else h^2/(a+h*u-t)^2

noncomputable def limitFieldJet (μ : ProbabilityMeasure Segment) (j : Fin 3)
    (a h u : ℝ) : ℝ :=
  (∫ t in (sourceInterval (a-h) (a+h))ᶜ, rawFieldJet j a h u (t : ℝ)
    ∂(μ : Measure Segment)) / (μ : Measure Segment).real (sourceInterval (a-h) (a+h))

noncomputable def clippedFieldJet (j : Fin 3) (a h b : ℝ)
    (z : Segment × Segment) : ℝ :=
  let q := a+h*(b*(z.1 : ℝ))-(z.2 : ℝ)
  let d := h*(1-b)
  if j = 0 then -Real.log (max d |q|)+Real.log (max h |a-(z.2 : ℝ)|)
  else if j = 1 then -h*q/(max (d^2) (q^2))
  else h^2/(max (d^2) (q^2))

theorem continuous_clippedFieldJet (j : Fin 3) (a h b : ℝ)
    (hh : 0 < h) (hb : b < 1) : Continuous (clippedFieldJet j a h b) := by
  have hd : 0 < h*(1-b) := mul_pos hh (sub_pos.mpr hb)
  have hlog (z : Segment × Segment) :
      max (h*(1-b)) |a+h*(b*(z.1 : ℝ))-(z.2 : ℝ)| ≠ 0 :=
    (hd.trans_le (le_max_left _ _)).ne'
  have horigin (z : Segment × Segment) : max h |a-(z.2 : ℝ)| ≠ 0 :=
    (hh.trans_le (le_max_left _ _)).ne'
  have hden (z : Segment × Segment) :
      max ((h*(1-b))^2) ((a+h*(b*(z.1 : ℝ))-(z.2 : ℝ))^2) ≠ 0 :=
    ((sq_pos_of_pos hd).trans_le (le_max_left _ _)).ne'
  change Continuous (fun z => clippedFieldJet j a h b z)
  fin_cases j <;> simp only [clippedFieldJet] <;> simp
  all_goals fun_prop (disch := first | apply hlog | apply horigin | apply hden)

theorem exterior_distances (a h b : ℝ) (x t : Segment)
    (hh : 0 < h) (hb0 : 0 ≤ b) (hb : b < 1)
    (ht : t ∉ sourceInterval (a-h) (a+h)) :
    h ≤ |a-(t : ℝ)| ∧ h*(1-b) ≤ |a+h*(b*(x : ℝ))-(t : ℝ)| := by
  have hxu : -b ≤ b*(x : ℝ) ∧ b*(x : ℝ) ≤ b := by
    constructor
    · have hm := mul_le_mul_of_nonneg_left x.property.1 hb0
      nlinarith
    · have hm := mul_le_mul_of_nonneg_left x.property.2 hb0
      nlinarith
  have hside : (t : ℝ) ≤ a-h ∨ a+h ≤ (t : ℝ) := by
    by_cases hl : (t : ℝ) ≤ a-h
    · exact Or.inl hl
    · exact Or.inr (le_of_not_gt (fun hr => ht ⟨lt_of_not_ge hl,hr⟩))
  rcases hside with hl | hr
  · constructor
    · exact (by linarith : h ≤ a-(t : ℝ)).trans (le_abs_self _)
    · have hm := mul_le_mul_of_nonneg_left hxu.1 hh.le
      exact (by nlinarith : h*(1-b) ≤ a+h*(b*(x : ℝ))-(t : ℝ)).trans (le_abs_self _)
  · constructor
    · exact (by linarith : h ≤ -(a-(t : ℝ))).trans (neg_le_abs _)
    · have hm := mul_le_mul_of_nonneg_left hxu.2 hh.le
      exact (by nlinarith : h*(1-b) ≤ -(a+h*(b*(x : ℝ))-(t : ℝ))).trans (neg_le_abs _)

theorem clippedFieldJet_eq_exterior (j : Fin 3) (a h b : ℝ) (x t : Segment)
    (hh : 0 < h) (hb0 : 0 ≤ b) (hb : b < 1)
    (ht : t ∉ sourceInterval (a-h) (a+h)) :
    clippedFieldJet j a h b (x,t) = rawFieldJet j a h (b*(x : ℝ)) (t : ℝ) := by
  obtain ⟨h0,h1⟩ := exterior_distances a h b x t hh hb0 hb ht
  have hd : 0 < h*(1-b) := mul_pos hh (sub_pos.mpr hb)
  have hsq : (h*(1-b))^2 ≤ (a+h*(b*(x : ℝ))-(t : ℝ))^2 := by
    nlinarith [sq_nonneg (|a+h*(b*(x : ℝ))-(t : ℝ)| - h*(1-b)), sq_abs (a+h*(b*(x : ℝ))-(t : ℝ))]
  have hq : a+h*(b*(x : ℝ))-(t : ℝ) ≠ 0 :=
    abs_pos.mp (hd.trans_le h1)
  fin_cases j
  · simp [clippedFieldJet, rawFieldJet, max_eq_right h0, max_eq_right h1,
      Real.log_abs] <;> ring
  · simp [clippedFieldJet, rawFieldJet, max_eq_right hsq]
    field_simp [hq] <;> ring
  · simp [clippedFieldJet, rawFieldJet, max_eq_right hsq]

theorem finiteFieldJet_sum (j : Fin 3) (Y : Finset ℝ) (a h u : ℝ) :
    finiteFieldJet j Y a h u =
      (∑ t ∈ outsideNodes Y a h, rawFieldJet j a h u t)/(insideNodes Y a h).card := by
  fin_cases j <;> simp [finiteFieldJet, rawFieldJet, finiteField, finiteFieldFirst,
    finiteFieldSecond, Finset.sum_neg_distrib, neg_div]

theorem outsideNodes_eq_filter (Y : Finset ℝ) (a h : ℝ) :
    outsideNodes Y a h = Y.filter (fun t => t ∉ Ioo (a-h) (a+h)) := by
  ext t
  simp [outsideNodes, insideNodes]
  tauto

/-- Equality of the empirical denominator to s/N, with both counts actual. -/
theorem erased_interval_fraction_eq_card (X : NodeArray) (S : Finset Segment)
    (n : ℕ) (a h : ℝ) :
    erasedAverage X S n ((sourceInterval (a-h) (a+h)).indicator (fun _ => (1 : ℝ))) =
      ((insideNodes (unassignedNodes X S n) a h).card : ℝ)/(n+1 : ℝ) := by
  have he : (sourceInterval (a-h) (a+h)).indicator (fun _ => (1 : ℝ)) =
      fun t : Segment => if (t : ℝ) ∈ Ioo (a-h) (a+h) then 1 else 0 := by
    ext t
    simp only [sourceInterval, Set.indicator, Set.mem_preimage]
  rw [he, erasedAverage_sum_real_nodes X S n
    (fun t : ℝ => if t ∈ Ioo (a-h) (a+h) then 1 else 0)]
  congr 1
  simp [insideNodes, ← Finset.sum_filter]

/-- Exact identification of the normalized clipped sum with the actual field
or actual derivative, not with a newly introduced approximation. -/
theorem normalized_erased_clipped_eq_fieldJet (X : NodeArray) (S : Finset Segment)
    (n : ℕ) (j : Fin 3) (a h b : ℝ) (x : Segment)
    (hh : 0 < h) (hb0 : 0 ≤ b) (hb : b < 1) :
    erasedAverage X S n ((sourceInterval (a-h) (a+h))ᶜ.indicator
        (fun t => clippedFieldJet j a h b (x,t))) /
      erasedAverage X S n ((sourceInterval (a-h) (a+h)).indicator (fun _ => (1 : ℝ))) =
        finiteFieldJet j (unassignedNodes X S n) a h (b*(x : ℝ)) := by
  have he : (sourceInterval (a-h) (a+h))ᶜ.indicator
        (fun t => clippedFieldJet j a h b (x,t)) =
      fun t : Segment => if (t : ℝ) ∈ Ioo (a-h) (a+h) then 0
        else rawFieldJet j a h (b*(x : ℝ)) (t : ℝ) := by
    ext t
    by_cases ht : t ∈ sourceInterval (a-h) (a+h)
    · have ht' : (t : ℝ) ∈ Ioo (a-h) (a+h) := ht
      simp only [Set.indicator_of_notMem
        (show t ∉ (sourceInterval (a-h) (a+h))ᶜ from fun htc => htc ht),
        if_pos ht']
    · have ht' : (t : ℝ) ∉ Ioo (a-h) (a+h) := ht
      simp only [Set.indicator_of_mem (show t ∈ (sourceInterval (a-h) (a+h))ᶜ from ht),
        if_neg ht']
      exact clippedFieldJet_eq_exterior j a h b x t hh hb0 hb ht
  rw [he, erasedAverage_sum_real_nodes X S n
      (fun t : ℝ => if t ∈ Ioo (a-h) (a+h) then 0 else rawFieldJet j a h (b*(x : ℝ)) t),
    erased_interval_fraction_eq_card,
    finiteFieldJet_sum, outsideNodes_eq_filter, Finset.sum_filter]
  have hsum : (∑ t ∈ unassignedNodes X S n,
      if t ∈ Ioo (a-h) (a+h) then (0 : ℝ) else rawFieldJet j a h (b*(x : ℝ)) t) =
      ∑ t ∈ unassignedNodes X S n,
        if t ∉ Ioo (a-h) (a+h) then rawFieldJet j a h (b*(x : ℝ)) t else 0 := by
    apply Finset.sum_congr rfl
    intro t ht
    by_cases hi : t ∈ Ioo (a-h) (a+h) <;> simp [hi]
  rw [hsum]
  by_cases hs : ((insideNodes (unassignedNodes X S n) a h).card : ℝ) = 0
  · simp only [hs, zero_div, div_zero]
  · field_simp

/-- The matching limiting integral uses the real exterior field kernel. -/
theorem clipped_limit_eq_fieldJet (μ : ProbabilityMeasure Segment) (j : Fin 3)
    (a h b : ℝ) (x : Segment) (hh : 0 < h) (hb0 : 0 ≤ b) (hb : b < 1) :
    (∫ t in (sourceInterval (a-h) (a+h))ᶜ, clippedFieldJet j a h b (x,t)
      ∂(μ : Measure Segment)) / (μ : Measure Segment).real (sourceInterval (a-h) (a+h)) =
      limitFieldJet μ j a h (b*(x : ℝ)) := by
  unfold limitFieldJet
  congr 1
  exact setIntegral_congr_fun (measurableSet_sourceInterval (a-h) (a+h)).compl
    (fun t ht => clippedFieldJet_eq_exterior j a h b x t hh hb0 hb ht)

/-- The full fixed-h C² jet convergence along original rows after each finite
S. Only the genuine weak limit, finite-floor branch and positive local mass
are hypotheses; all restriction/deletion/normalization limits are proved. -/
theorem finiteFieldJet_tendsto_uniform (X : NodeArray) (rows : ℕ → ℕ)
    (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun k => V3.empiricalProbability X (rows k)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) (a h b : ℝ) (hh : 0 < h)
    (hb0 : 0 < b) (hb : b < 1)
    (hmass : 0 < (μ : Measure Segment).real (sourceInterval (a-h) (a+h))) :
    ∀ S : Finset Segment, ∀ ε > (0 : ℝ), ∀ᶠ k in atTop,
      ∀ j : Fin 3, ∀ u ∈ Icc (-b) b,
        |finiteFieldJet j (unassignedNodes X S (rows k)) a h u -
          limitFieldJet μ j a h u| < ε := by
  intro S ε hε
  have hj (j : Fin 3) : ∀ᶠ k in atTop, ∀ x : Segment,
      |finiteFieldJet j (unassignedNodes X S (rows k)) a h (b*(x : ℝ)) -
        limitFieldJet μ j a h (b*(x : ℝ))| < ε := by
    have he := erased_normalized_exterior_uniform X rows hrows μ hμ hfloor
      (clippedFieldJet j a h b) (continuous_clippedFieldJet j a h b hh hb)
      (by linarith : a-h < a+h) hmass S ε hε
    filter_upwards [he] with k hk
    intro x
    simpa only [normalized_erased_clipped_eq_fieldJet X S (rows k) j a h b x hh hb0.le hb,
      clipped_limit_eq_fieldJet μ j a h b x hh hb0.le hb] using hk x
  have hall := (eventually_all_finset (Finset.univ : Finset (Fin 3))).mpr (fun j _ => hj j)
  filter_upwards [hall] with k hk
  intro j u hu
  have hx : u/b ∈ Segment := by
    constructor
    · exact (le_div_iff₀ hb0).mpr (by nlinarith [hu.1])
    · exact (div_le_one hb0).mpr hu.2
  let x : Segment := ⟨u/b,hx⟩
  have hid : b*(x : ℝ)=u := by dsimp [x]; field_simp
  simpa only [hid] using hk j (Finset.mem_univ _) x

/-- For each fixed interval and each finite S, the inside count really grows
linearly in the original node number. -/
theorem insideNodes_fraction_tendsto (X : NodeArray) (rows : ℕ → ℕ)
    (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun k => V3.empiricalProbability X (rows k)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) (a h : ℝ) (hh : 0 < h) (S : Finset Segment) :
    Tendsto (fun k => ((insideNodes (unassignedNodes X S (rows k)) a h).card : ℝ) /
      (rows k+1 : ℝ)) atTop (𝓝 ((μ : Measure Segment).real (sourceInterval (a-h) (a+h)))) := by
  simpa only [erased_interval_fraction_eq_card] using
    erased_interval_fraction_tendsto X rows hrows μ hμ hfloor (by linarith : a-h<a+h) S

end Erdos1152.V4
