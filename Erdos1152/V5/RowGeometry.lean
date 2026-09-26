import Erdos1152.V5.SmallScaleField

/-!
# One genuine scale, followed by all finite deletions and late original rows

The model field, node-count budget, unbounded local node count and sublinear
excess ratio are obtained together. The quantifiers do not allow the chosen
scale to change with the finite assigned set.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace Erdos1152.V5
open V4

/-- Positive local limiting mass forces the actual local node count to infinity. -/
theorem inside_card_tendsto_atTop (X : NodeArray) (rows : ℕ → ℕ)
    (hrows : Tendsto rows atTop atTop) (μ : ProbabilityMeasure Segment)
    (hμ : Tendsto (fun k => V3.empiricalProbability X (rows k)) atTop (𝓝 μ))
    (hfloor : potentialFloor μ ≠ ⊥) (x h : ℝ) (hh : 0 < h)
    (hm : 0 < localMass μ x h) (S : Finset Segment) :
    Tendsto (fun k => (insideNodes (unassignedNodes X S (rows k)) x h).card) atTop atTop := by
  have hf := insideNodes_fraction_tendsto X rows hrows μ hμ hfloor x h hh S
  apply Filter.tendsto_atTop.mpr
  intro L
  obtain ⟨N,hN⟩ := exists_nat_gt ((L : ℝ)/(localMass μ x h/2))
  have hhalf : 0 < localMass μ x h/2 := half_pos hm
  have hL : (L : ℝ)<(localMass μ x h/2)*N := by
    have := (div_lt_iff₀ hhalf).mp hN
    nlinarith
  have he := hf.eventually (lt_mem_nhds (half_lt_self hm))
  filter_upwards [he,hrows.eventually (eventually_ge_atTop N)] with k hk hNk
  have hn : (N : ℝ) ≤ (rows k : ℝ) := by exact_mod_cast hNk
  have hr := (lt_div_iff₀ (by positivity : 0 < (rows k+1 : ℝ))).mp hk
  have hcard : (L : ℝ)<(insideNodes (unassignedNodes X S (rows k)) x h).card := by
    change (localMass μ x h/2)*(rows k+1 : ℝ)<_ at hr
    nlinarith
  exact le_of_lt (by exact_mod_cast hcard)

/-- All geometric/analytic inputs for the finite weighted construction, on
one scale selected before the arbitrary finite assigned set. These are the
actual `finiteFieldJet` values, not an assumed external-field predicate. -/
theorem ae_minimum_choose_field_scale (X : NodeArray) (r : ℕ → ℕ)
    (hr : Tendsto (fun n => (r n : ℝ)/(n+1 : ℝ)) atTop (𝓝 0))
    (ρ : ℕ) (hρ : 0 < ρ) (b δ : ℝ) (hb0 : 0 < b) (hb1 : b < 1) (hδ : 0 < δ) :
    ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1),x ∉ canonicalHighRegion X →
      ∀ ε > (0 : ℝ),∃ h : ℝ,0 < h ∧ h ≤ ε ∧ -1 < x-h ∧ x+h < 1 ∧
        0 < localMass (canonicalMeasure X) x h ∧
        ∀ S : Finset Segment,
          (∀ᶠ k in atTop,
            0 < (insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card ∧
            ((insideNodes (unassignedNodes X S (canonicalRows X k)) x (h/4)).card : ℝ) ≤
              (1/4+1/(16*(ρ : ℝ)))*(insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card ∧
            ∀ j : Fin 3,∀ u ∈ Icc (-b) b,
              |finiteFieldJet j (unassignedNodes X S (canonicalRows X k)) x h u-modelJet j u| < δ) ∧
          Tendsto (fun k => (insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card)
            atTop atTop ∧
          Tendsto (fun k => ((r (canonicalRows X k) : ℝ)+S.card)/
            (insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card) atTop (𝓝 0) := by
  let μ := canonicalMeasure X
  have hfield := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self :
    Ioo (-1 : ℝ) 1 ⊆ Segment) (ae_minimum_small_scale_field μ)
  have hder := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Icc_self :
    Ioo (-1 : ℝ) 1 ⊆ Segment) (ae_positive_CDF_derivative_on_minimum μ)
  filter_upwards [ae_restrict_mem measurableSet_Ioo,hfield,hder] with x hx hfx hdx
  intro hnot ε hε
  have hnot' : x ∉ highPotentialRegion μ := hnot
  have hf : potentialFloor μ ≠ ⊥ := by
    intro hbot
    exact hnot' (by rw [highPotentialRegion_of_floor_bot μ hbot]; exact ⟨hx.1.le,hx.2.le⟩)
  obtain ⟨hd,hw⟩ := hdx hnot'
  have hcm := eventually_local_mass_and_central_fraction μ hf x (sourceDensity μ x) hw hd ρ hρ
  have hmod := hfx hnot' b hb0 hb1 (δ/2) (half_pos hδ)
  let η := min ε (min (x+1) (1-x))
  have hη : 0 < η := lt_min hε (lt_min (by linarith [hx.1]) (by linarith [hx.2]))
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0,h < η := mem_nhdsWithin_of_mem_nhds (gt_mem_nhds hη)
  have hpositive : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
  obtain ⟨h,hh,hsmallh,hcmh,hmodh⟩ :=
    (hpositive.and (hsmall.and (hcm.and hmod))).exists
  have hm : 0 < localMass μ x h := hmodh.1
  refine ⟨h,hh,hsmallh.le.trans (min_le_left _ _),?_,?_,hm,?_⟩
  · have ht := hsmallh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  · have ht := hsmallh.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  intro S
  have hgrowth := inside_card_tendsto_atTop X (canonicalRows X) (canonicalRows_tendsto X)
    μ (canonicalMeasure_weak X) hf x h hh hm S
  have hcount := central_node_fraction_tendsto X (canonicalRows X) (canonicalRows_tendsto X)
    μ (canonicalMeasure_weak X) hf x h hh hm S
  have hjet := finiteFieldJet_tendsto_uniform X (canonicalRows X) (canonicalRows_tendsto X)
    μ (canonicalMeasure_weak X) hf x h b hh hb0 hb1 hm S (δ/2) (half_pos hδ)
  have hmargin : (μ : Measure Segment).real (sourceInterval (x-h/4) (x+h/4))/
      localMass μ x h < 1/4+1/(16*(ρ : ℝ)) := by
    have hρ' : (0 : ℝ)<ρ := Nat.cast_pos.mpr hρ
    have hgap : (1 : ℝ)/(32*ρ)<1/(16*ρ) := by
      apply one_div_lt_one_div_of_lt (by positivity)
      nlinarith
    dsimp only [localMass]
    linarith [hcmh.2]
  refine ⟨?_,hgrowth,local_excess_fraction_tendsto X r hr (canonicalRows X)
    (canonicalRows_tendsto X) μ (canonicalMeasure_weak X) hf x h hh hm S⟩
  filter_upwards [hgrowth.eventually (eventually_ge_atTop 1),
    hcount.eventually (gt_mem_nhds hmargin),hjet] with k hsk hck hjk
  have hs : 0 < (insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card := by omega
  have hsR : (0 : ℝ)<(insideNodes (unassignedNodes X S (canonicalRows X k)) x h).card :=
    Nat.cast_pos.mpr hs
  refine ⟨hs,((div_lt_iff₀ hsR).mp hck).le,?_⟩
  intro j u hu
  have he := hmodh.2 j u (abs_le.mpr hu)
  have hj := hjk j u hu
  exact (abs_sub_le
    (finiteFieldJet j (unassignedNodes X S (canonicalRows X k)) x h u)
    (limitFieldJet μ j x h u) (modelJet j u)).trans_lt (by linarith)

end Erdos1152.V5
