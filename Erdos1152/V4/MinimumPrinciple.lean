import Erdos1152.V4.PotentialLevel
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Minimum principle for the actual logarithmic potential

We prove the lower bound on the entire real axis, not merely on the support.
The proof avoids assuming endpoint integrability: values just inside a support
gap are compared with *truncated* endpoint values. The clipping threshold can
be smaller than the distance moved into the gap. Jensen's inequality for log
then propagates the lower bound to the gap, and the displacement tends to zero.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def supportReal (μ : ProbabilityMeasure Segment) : Set ℝ :=
  Subtype.val '' (μ : Measure Segment).support

theorem supportReal_compact (μ : ProbabilityMeasure Segment) : IsCompact (supportReal μ) :=
  (Measure.isClosed_support.isCompact).image continuous_subtype_val

theorem supportReal_nonempty (μ : ProbabilityMeasure Segment) : (supportReal μ).Nonempty := by
  have hp : 0 < (μ : Measure Segment) Set.univ := by simp
  obtain ⟨t, _, ht⟩ := Measure.nonempty_inter_support_of_pos hp
  exact ⟨(t : ℝ), ⟨t, ht, rfl⟩⟩

theorem ae_mem_supportReal (μ : ProbabilityMeasure Segment) :
    ∀ᵐ t : Segment ∂(μ : Measure Segment), (t : ℝ) ∈ supportReal μ := by
  filter_upwards [Measure.support_mem_ae (μ := (μ : Measure Segment))] with t ht
  exact ⟨t, ht, rfl⟩

theorem potentialFloor_le_trunc_supportReal (μ : ProbabilityMeasure Segment)
    (x : ℝ) (hx : x ∈ supportReal μ) (k : ℕ) :
    potentialFloor μ ≤ (truncPotential μ k x : EReal) := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact potentialFloor_le_trunc_at_support μ t ht k

/-- Integrability away from the actual source support follows from a continuous
clipped kernel. No absolute-continuity assumption on the measure occurs. -/
theorem log_section_integrable_away (μ : ProbabilityMeasure Segment) (x d : ℝ)
    (hd : 0 < d) (haway : ∀ᵐ t : Segment ∂(μ : Measure Segment), d ≤ |x - t|) :
    Integrable (fun t : Segment => logProfile (x - t)) (μ : Measure Segment) := by
  obtain ⟨k, hk⟩ := (cutoff_tendsto_zero.eventually (gt_mem_nhds hd)).exists
  apply (integrable_trunc_section μ k x).congr
  filter_upwards [haway] with t ht
  simp only [truncProfile, logProfile, max_eq_right (hk.le.trans ht)]

theorem extendedPotential_eq_potential_away (μ : ProbabilityMeasure Segment) (x d : ℝ)
    (hd : 0 < d) (haway : ∀ᵐ t : Segment ∂(μ : Measure Segment), d ≤ |x - t|) :
    extendedPotential μ x = (potential μ x : EReal) := by
  have he : ∀ᶠ k in atTop, truncPotential μ k x = potential μ x := by
    filter_upwards [cutoff_tendsto_zero.eventually (gt_mem_nhds hd)] with k hk
    apply integral_congr_ae
    filter_upwards [haway] with t ht
    simp only [truncProfile, logProfile, max_eq_right (hk.le.trans ht)]
  have hlim : Tendsto (fun k => (truncPotential μ k x : EReal)) atTop
      (𝓝 (potential μ x : EReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with k hk
    rw [hk]
  exact tendsto_nhds_unique (extendedPotential_limit μ x) hlim

theorem gap_distance (a b x t : ℝ) (hx : x ∈ Ioo a b)
    (ht : t ≤ a ∨ b ≤ t) : min (x - a) (b - x) ≤ |x - t| := by
  rcases ht with ht | ht
  · rw [abs_of_nonneg (by linarith [hx.1] : 0 ≤ x - t)]
    exact (min_le_left _ _).trans (by linarith)
  · rw [abs_of_nonpos (by linarith [hx.2] : x - t ≤ 0)]
    exact (min_le_right _ _).trans (by linarith)

/-- Scalar concavity on a gap that contains no source. -/
theorem logProfile_gap_jensen (a b y z t «λ» θ : ℝ)
    (hy : y ∈ Ioo a b) (hz : z ∈ Ioo a b) (ht : t ≤ a ∨ b ≤ t)
    («hλ» : 0 ≤ «λ») (hθ : 0 ≤ θ) (hsum : «λ» + θ = 1) :
    «λ» * logProfile (y - t) + θ * logProfile (z - t) ≤
      logProfile («λ» * y + θ * z - t) := by
  rcases ht with ht | ht
  · have hy' : 0 < y - t := by linarith [hy.1]
    have hz' : 0 < z - t := by linarith [hz.1]
    have hc := strictConcaveOn_log_Ioi.concaveOn.2 hy' hz' «hλ» hθ hsum
    have hp : 0 < «λ» * (y - t) + θ * (z - t) := by
      by_cases hzero : «λ» = 0
      · have hθone : θ = 1 := by linarith
        simpa only [hzero, hθone, zero_mul, one_mul, zero_add] using hz'
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (lt_of_le_of_ne «hλ» (Ne.symm hzero)) hy') (mul_nonneg hθ hz'.le)
    have he : «λ» * (y - t) + θ * (z - t) = «λ» * y + θ * z - t := by
      calc
        _ = «λ» * y + θ * z - («λ» + θ) * t := by ring
        _ = _ := by rw [hsum]; ring
    simp only [smul_eq_mul] at hc
    simp only [logProfile, abs_of_pos hy', abs_of_pos hz']
    rw [← he, abs_of_pos hp]
    exact hc
  · have hy' : 0 < t - y := by linarith [hy.2]
    have hz' : 0 < t - z := by linarith [hz.2]
    have hc := strictConcaveOn_log_Ioi.concaveOn.2 hy' hz' «hλ» hθ hsum
    have hp : 0 < «λ» * (t - y) + θ * (t - z) := by
      by_cases hzero : «λ» = 0
      · have hθone : θ = 1 := by linarith
        simpa only [hzero, hθone, zero_mul, one_mul, zero_add] using hz'
      · exact add_pos_of_pos_of_nonneg
          (mul_pos (lt_of_le_of_ne «hλ» (Ne.symm hzero)) hy') (mul_nonneg hθ hz'.le)
    have he : «λ» * (t - y) + θ * (t - z) = -(«λ» * y + θ * z - t) := by
      calc
        _ = («λ» + θ) * t - («λ» * y + θ * z) := by ring
        _ = _ := by rw [hsum]; ring
    simp only [smul_eq_mul] at hc
    simp only [logProfile, abs_of_neg (by linarith : y - t < 0),
      abs_of_neg (by linarith : z - t < 0)]
    have habs : |«λ» * y + θ * z - t| = «λ» * (t - y) + θ * (t - z) := by
      rw [he, abs_of_neg (by linarith : «λ» * y + θ * z - t < 0)]
    rw [habs]
    simpa only [neg_sub] using hc

theorem potential_concave_gap (μ : ProbabilityMeasure Segment) (a b : ℝ)
    (hgap : ∀ᵐ t : Segment ∂(μ : Measure Segment), (t : ℝ) ≤ a ∨ b ≤ t) :
    ConcaveOn ℝ (Ioo a b) (potential μ) := by
  refine ⟨convex_Ioo a b, ?_⟩
  intro y hy z hz «λ» θ «hλ» hθ hsum
  have hw : «λ» * y + θ * z ∈ Ioo a b := by
    simpa only [smul_eq_mul] using (convex_Ioo a b) hy hz «hλ» hθ hsum
  have hi (x : ℝ) (hx : x ∈ Ioo a b) :
      Integrable (fun t : Segment => logProfile (x - t)) (μ : Measure Segment) := by
    apply log_section_integrable_away μ x (min (x - a) (b - x))
      (lt_min (sub_pos.mpr hx.1) (sub_pos.mpr hx.2))
    filter_upwards [hgap] with t ht
    exact gap_distance a b x t hx ht
  simp only [smul_eq_mul]
  rw [potential, potential, potential, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((hi y hy).const_mul «λ») ((hi z hz).const_mul θ)]
  apply integral_mono_ae (((hi y hy).const_mul «λ»).add ((hi z hz).const_mul θ)) (hi _ hw)
  filter_upwards [hgap] with t ht
  exact logProfile_gap_jensen a b y z t «λ» θ hy hz ht «hλ» hθ hsum

/-- Move a small distance into a gap. The clipped endpoint value gives a lower
bound, up to log(1-δ/(b-a)). This handles singular endpoint source distributions. -/
theorem left_endpoint_log_bound (a b t δ : ℝ) (k : ℕ)
    (hab : a < b) (hδ : 0 < δ) (hδsmall : δ ≤ (b - a) / 4)
    (hk : cutoff k ≤ δ) (ht : t ≤ a ∨ b ≤ t) :
    truncProfile k (a - t) + Real.log (1 - δ / (b - a)) ≤ logProfile (a + δ - t) := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hc : 0 < 1 - δ / (b - a) := by rw [sub_pos, div_lt_one hd]; linarith
  have hc1 : 1 - δ / (b - a) ≤ 1 := by
    have := div_nonneg hδ.le hd.le
    linarith
  have hlogc := Real.log_nonpos hc.le hc1
  rcases ht with ht | ht
  · have hraw : 0 < a + δ - t := by linarith
    have hmax : max (cutoff k) |a - t| ≤ |a + δ - t| := by
      rw [abs_of_nonneg (by linarith : 0 ≤ a - t), abs_of_pos hraw]
      exact max_le (by linarith) (by linarith)
    have hlog := Real.log_le_log (lt_of_lt_of_le (cutoff_pos k) (le_max_left _ _)) hmax
    dsimp only [truncProfile, logProfile]
    linarith
  · have hta : 0 < t - a := by linarith
    have hbase : max (cutoff k) |a - t| = t - a := by
      rw [abs_of_nonpos (by linarith : a - t ≤ 0), neg_sub]
      apply max_eq_right
      linarith
    have hraw : 0 < t - a - δ := by linarith
    have hprod : (1 - δ / (b - a)) * (t - a) ≤ t - a - δ := by
      have hquot : δ ≤ (δ / (b - a)) * (t - a) := by
        have hm := mul_le_mul_of_nonneg_left (show b - a ≤ t - a by linarith)
          (div_nonneg hδ.le hd.le)
        have he : (δ / (b - a)) * (b - a) = δ := div_mul_cancel₀ δ hd.ne'
        linarith
      nlinarith
    have hlog := Real.log_le_log (mul_pos hc hta) hprod
    rw [Real.log_mul hc.ne' hta.ne'] at hlog
    dsimp only [truncProfile, logProfile]
    rw [hbase, abs_of_neg (by linarith : a + δ - t < 0)]
    rw [show -(a + δ - t) = t - a - δ by ring]
    linarith

theorem right_endpoint_log_bound (a b t δ : ℝ) (k : ℕ)
    (hab : a < b) (hδ : 0 < δ) (hδsmall : δ ≤ (b - a) / 4)
    (hk : cutoff k ≤ δ) (ht : t ≤ a ∨ b ≤ t) :
    truncProfile k (b - t) + Real.log (1 - δ / (b - a)) ≤ logProfile (b - δ - t) := by
  have h := left_endpoint_log_bound (-b) (-a) (-t) δ k (by linarith) hδ
    (by linarith) hk (ht.elim (fun h => Or.inr (by linarith)) (fun h => Or.inl (by linarith)))
  have hleft : truncProfile k (-b - -t) = truncProfile k (b - t) := by
    unfold truncProfile
    rw [show -b - -t = -(b - t) by ring, abs_neg]
  have hright : logProfile (-b + δ - -t) = logProfile (b - δ - t) := by
    unfold logProfile
    rw [show -b + δ - -t = -(b - δ - t) by ring, abs_neg]
  simpa only [hleft, hright, show -a - -b = b - a by ring] using h

/-- Real lower bounds on all clipped support values extend across a bounded gap. -/
theorem potential_ge_of_gap_endpoint_bounds (μ : ProbabilityMeasure Segment)
    (a b x A : ℝ) (hax : a < x) (hxb : x < b)
    (hgap : ∀ᵐ t : Segment ∂(μ : Measure Segment), (t : ℝ) ≤ a ∨ b ≤ t)
    (ha : ∀ k, A ≤ truncPotential μ k a) (hb : ∀ k, A ≤ truncPotential μ k b) :
    A ≤ potential μ x := by
  let δ : ℕ → ℝ := fun n => (b - a) / (n + 4 : ℝ)
  have hd : 0 < b - a := by linarith
  have hδpos (n : ℕ) : 0 < δ n := div_pos hd (by positivity)
  have hδsmall (n : ℕ) : δ n ≤ (b - a) / 4 := by
    apply div_le_div_of_nonneg_left hd.le (by norm_num)
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    have hN : Tendsto (fun n : ℕ => (n + 4 : ℝ)) atTop atTop :=
      tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
    simpa only [δ, Function.comp_def, div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp hN).const_mul (b - a)
  have he : ∀ᶠ n : ℕ in atTop, δ n < min (x - a) (b - x) :=
    hδlim.eventually (gt_mem_nhds (lt_min (sub_pos.mpr hax) (sub_pos.mpr hxb)))
  have hloglim : Tendsto (fun n => A + Real.log (1 - δ n / (b - a))) atTop (𝓝 A) := by
    have ht0 : Tendsto (fun n => 1 - δ n / (b - a)) atTop (𝓝 (1 : ℝ)) := by
      simpa only [zero_div, sub_zero] using (hδlim.div_const (b - a)).const_sub 1
    have ht := ht0.log (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [Real.log_one, add_zero] using ht.const_add A
  apply le_of_tendsto hloglim
  filter_upwards [he] with n hn
  let y := a + δ n
  let z := b - δ n
  have hy : y ∈ Ioo a b := ⟨by dsimp [y]; linarith [hδpos n], by dsimp [y]; linarith [hδsmall n]⟩
  have hz : z ∈ Ioo a b := ⟨by dsimp [z]; linarith [hδsmall n], by dsimp [z]; linarith [hδpos n]⟩
  have hyx : y < x := by dsimp [y]; have := hn.trans_le (min_le_left _ _); linarith
  have hxz : x < z := by dsimp [z]; have := hn.trans_le (min_le_right _ _); linarith
  obtain ⟨k, hk⟩ := (cutoff_tendsto_zero.eventually (gt_mem_nhds (hδpos n))).exists
  have hi (w : ℝ) (hw : w ∈ Ioo a b) :=
    log_section_integrable_away μ w (min (w - a) (b - w))
      (lt_min (sub_pos.mpr hw.1) (sub_pos.mpr hw.2))
      (hgap.mono (fun t ht => gap_distance a b w t hw ht))
  have hylow : A + Real.log (1 - δ n / (b - a)) ≤ potential μ y := by
    calc
      _ ≤ truncPotential μ k a + Real.log (1 - δ n / (b - a)) := by linarith [ha k]
      _ = ∫ t : Segment, truncProfile k (a - t) + Real.log (1 - δ n / (b - a))
          ∂(μ : Measure Segment) := by rw [integral_add (integrable_trunc_section μ k a) (integrable_const _)]; simp [truncPotential]
      _ ≤ potential μ y := by
        apply integral_mono_ae ((integrable_trunc_section μ k a).add (integrable_const _)) (hi y hy)
        filter_upwards [hgap] with t ht
        exact left_endpoint_log_bound a b t (δ n) k (by linarith) (hδpos n) (hδsmall n) hk.le ht
  have hzlow : A + Real.log (1 - δ n / (b - a)) ≤ potential μ z := by
    calc
      _ ≤ truncPotential μ k b + Real.log (1 - δ n / (b - a)) := by linarith [hb k]
      _ = ∫ t : Segment, truncProfile k (b - t) + Real.log (1 - δ n / (b - a))
          ∂(μ : Measure Segment) := by rw [integral_add (integrable_trunc_section μ k b) (integrable_const _)]; simp [truncPotential]
      _ ≤ potential μ z := by
        apply integral_mono_ae ((integrable_trunc_section μ k b).add (integrable_const _)) (hi z hz)
        filter_upwards [hgap] with t ht
        exact right_endpoint_log_bound a b t (δ n) k (by linarith) (hδpos n) (hδsmall n) hk.le ht
  let «λ» : ℝ := (z - x) / (z - y)
  let θ : ℝ := (x - y) / (z - y)
  have hzy : 0 < z - y := by linarith
  have «hλ» : 0 ≤ «λ» := (div_pos (sub_pos.mpr hxz) hzy).le
  have hθ : 0 ≤ θ := (div_pos (sub_pos.mpr hyx) hzy).le
  have hsum : «λ» + θ = 1 := by dsimp [«λ», θ]; field_simp [hzy.ne']; ring
  have hw : «λ» * y + θ * z = x := by dsimp [«λ», θ]; field_simp [hzy.ne']; ring
  have hj := (potential_concave_gap μ a b hgap).2 hy hz «hλ» hθ hsum
  simp only [smul_eq_mul, hw] at hj
  have hl := mul_le_mul_of_nonneg_left hylow «hλ»
  have hr := mul_le_mul_of_nonneg_left hzlow hθ
  have heq : «λ» * (A + Real.log (1 - δ n / (b - a))) +
      θ * (A + Real.log (1 - δ n / (b - a))) =
      A + Real.log (1 - δ n / (b - a)) := by
    rw [← add_mul, hsum, one_mul]
  linarith

/-- A compact real support has either a two-sided source-free gap containing x,
or all sources lie on one side of x. The selected endpoint belongs to the support. -/
theorem compact_support_gap (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (x : ℝ) (hx : x ∉ K) :
    (∃ a ∈ K, a < x ∧ ∀ t ∈ K, t ≤ a) ∨
    (∃ b ∈ K, x < b ∧ ∀ t ∈ K, b ≤ t) ∨
    (∃ a ∈ K, ∃ b ∈ K, a < x ∧ x < b ∧ ∀ t ∈ K, t ≤ a ∨ b ≤ t) := by
  by_cases hleft : (K ∩ Iic x).Nonempty
  · obtain ⟨a, ha, hmax⟩ := (hK.inter_right isClosed_Iic).exists_isMaxOn hleft continuousOn_id
    have hax : a < x := lt_of_le_of_ne ha.2 (fun he => hx (he ▸ ha.1))
    by_cases hright : (K ∩ Ici x).Nonempty
    · obtain ⟨b, hb, hmin⟩ := (hK.inter_right isClosed_Ici).exists_isMinOn hright continuousOn_id
      have hxb : x < b := lt_of_le_of_ne hb.2 (fun he => hx (he.symm ▸ hb.1))
      refine Or.inr (Or.inr ⟨a, ha.1, b, hb.1, hax, hxb, ?_⟩)
      intro t ht
      rcases le_total t x with htx | hxt
      · exact Or.inl (hmax ⟨ht, htx⟩)
      · exact Or.inr (hmin ⟨ht, hxt⟩)
    · refine Or.inl ⟨a, ha.1, hax, ?_⟩
      intro t ht
      have htx : t ≤ x := by
        by_contra! h
        exact hright ⟨t, ht, h.le⟩
      exact hmax ⟨ht, htx⟩
  · obtain ⟨b, hb, hmin⟩ := hK.exists_isMinOn hne continuousOn_id
    have hxb : x < b := by
      by_contra! h
      exact hleft ⟨b, hb, h⟩
    exact Or.inr (Or.inl ⟨b, hb, hxb, fun t ht => hmin ht⟩)

/-- One-sided source bounds require no limiting endpoint argument. -/
theorem potential_ge_left_of_support (μ : ProbabilityMeasure Segment) (x b A : ℝ)
    (hxb : x < b) (hs : ∀ᵐ t : Segment ∂(μ : Measure Segment), b ≤ (t : ℝ))
    (hb : ∀ k, A ≤ truncPotential μ k b) : A ≤ potential μ x := by
  obtain ⟨k, hk⟩ := (cutoff_tendsto_zero.eventually (gt_mem_nhds (sub_pos.mpr hxb))).exists
  have haway : ∀ᵐ t : Segment ∂(μ : Measure Segment), b - x ≤ |x - t| := by
    filter_upwards [hs] with t ht
    rw [abs_of_neg (by linarith : x - t < 0)]
    linarith
  apply (hb k).trans
  apply integral_mono_ae (integrable_trunc_section μ k b)
    (log_section_integrable_away μ x (b - x) (sub_pos.mpr hxb) haway)
  filter_upwards [hs] with t ht
  apply Real.log_le_log (lt_of_lt_of_le (cutoff_pos k) (le_max_left _ _))
  rw [abs_of_nonpos (by linarith : b - t ≤ 0), abs_of_neg (by linarith : x - t < 0)]
  exact max_le (by linarith) (by linarith)

theorem potential_ge_right_of_support (μ : ProbabilityMeasure Segment) (a x A : ℝ)
    (hax : a < x) (hs : ∀ᵐ t : Segment ∂(μ : Measure Segment), (t : ℝ) ≤ a)
    (ha : ∀ k, A ≤ truncPotential μ k a) : A ≤ potential μ x := by
  obtain ⟨k, hk⟩ := (cutoff_tendsto_zero.eventually (gt_mem_nhds (sub_pos.mpr hax))).exists
  have haway : ∀ᵐ t : Segment ∂(μ : Measure Segment), x - a ≤ |x - t| := by
    filter_upwards [hs] with t ht
    rw [abs_of_pos (by linarith : 0 < x - t)]
    linarith
  apply (ha k).trans
  apply integral_mono_ae (integrable_trunc_section μ k a)
    (log_section_integrable_away μ x (x - a) (sub_pos.mpr hax) haway)
  filter_upwards [hs] with t ht
  apply Real.log_le_log (lt_of_lt_of_le (cutoff_pos k) (le_max_left _ _))
  rw [abs_of_nonneg (by linarith : 0 ≤ a - t), abs_of_pos (by linarith : 0 < x - t)]
  exact max_le (by linarith) (by linarith)

/-- The key global lower bound needed by the Poisson argument, valid with
extended values and arbitrary atomic or singular measures. -/
theorem potentialFloor_le_extended (μ : ProbabilityMeasure Segment) (x : ℝ) :
    potentialFloor μ ≤ extendedPotential μ x := by
  by_cases hx : x ∈ supportReal μ
  · obtain ⟨t, ht, rfl⟩ := hx
    exact potentialFloor_le_extended_at_support μ t ht
  · have hclosed := (supportReal_compact μ).isClosed
    have hdist : ∃ d > (0 : ℝ), ∀ t ∈ supportReal μ, d ≤ |x - t| := by
      obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl x hx
      refine ⟨d, hd, ?_⟩
      intro t ht
      by_contra! h
      have htball : t ∈ Metric.ball x d := by
        simpa only [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using h
      exact hball htball ht
    obtain ⟨d, hd, hdist⟩ := hdist
    have haway := (ae_mem_supportReal μ).mono (fun t ht => hdist t ht)
    rw [extendedPotential_eq_potential_away μ x d hd haway]
    by_contra! hlt
    obtain ⟨A, hPA, hAF⟩ := EReal.exists_between_coe_real hlt
    have hbound (t : ℝ) (ht : t ∈ supportReal μ) (k : ℕ) : A ≤ truncPotential μ k t := by
      exact EReal.coe_le_coe_iff.mp (hAF.le.trans (potentialFloor_le_trunc_supportReal μ t ht k))
    have hreal : potential μ x < A := EReal.coe_lt_coe_iff.mp hPA
    rcases compact_support_gap (supportReal μ) (supportReal_compact μ)
      (supportReal_nonempty μ) x hx with hL | hR | hG
    · obtain ⟨a, ha, hax, hs⟩ := hL
      have hlow := potential_ge_right_of_support μ a x A hax
        ((ae_mem_supportReal μ).mono (fun t ht => hs t ht)) (hbound a ha)
      linarith
    · obtain ⟨b, hb, hxb, hs⟩ := hR
      have hlow := potential_ge_left_of_support μ x b A hxb
        ((ae_mem_supportReal μ).mono (fun t ht => hs t ht)) (hbound b hb)
      linarith
    · obtain ⟨a, ha, b, hb, hax, hxb, hs⟩ := hG
      have hlow := potential_ge_of_gap_endpoint_bounds μ a b x A hax hxb
        ((ae_mem_supportReal μ).mono (fun t ht => hs t ht)) (hbound a ha) (hbound b hb)
      linarith

/-- Thus the complement of the actual high cover is the minimum level a.e.,
not an arbitrary leftover measurable region. -/
theorem ae_compl_high_is_minimum (μ : ProbabilityMeasure Segment) :
    ∀ᵐ x ∂baseMeasure, x ∉ highPotentialRegion μ →
      extendedPotential μ x = potentialFloor μ := by
  filter_upwards [ae_highPotentialRegion_iff_extended μ] with x hx hnot
  have hle : extendedPotential μ x ≤ potentialFloor μ :=
    le_of_not_gt (fun h => hnot (hx.mpr h))
  exact hle.antisymm (potentialFloor_le_extended μ x)

end Erdos1152.V4
