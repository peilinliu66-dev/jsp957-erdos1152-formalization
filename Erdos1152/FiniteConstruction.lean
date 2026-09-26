import Erdos1152.Batches

/-! Iterating the uniform contraction and extending the resulting finite data. -/

open Polynomial MeasureTheory Set
open scoped ENNReal

namespace Erdos1152

theorem exists_small_low_stage (X : NodeArray) (r : ℕ → ℕ) (H c δ : ℝ) (N : ℕ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ)
    (hamp : IntervalAmplification X r H c N) :
    ∃ S : Stage X, S.Above N ∧ ∀ p : ℕ → ℝ[X], S.Fits r p →
      volume.real (commonLowSet S.rows p H) < δ := by
  let q := 1 - 3 * c / 4
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hstage (k : ℕ) : ∃ S : Stage X, S.Above N ∧ ∀ p : ℕ → ℝ[X], S.Fits r p →
      volume.real (commonLowSet S.rows p H) < δ ∨
      volume.real (commonLowSet S.rows p H) ≤ 2 * q ^ k := by
    induction k with
    | zero =>
      refine ⟨Stage.empty X, by simp [Stage.Above, Stage.empty], fun p _ => Or.inr ?_⟩
      norm_num [Stage.empty, commonLowSet, Segment, Real.volume_real_Icc]
    | succ k ih =>
      obtain ⟨S, hS, hpS⟩ := ih
      obtain ⟨T, hST, hT, hpT⟩ := one_batch X r H c δ N hc.le hδ hamp S hS
      refine ⟨T, hT, fun p hp => ?_⟩
      have hmono := measureReal_mono (hST.lowSet_subset p H) (commonLowSet_measure_ne_top _ _ _)
      by_cases hsmall : volume.real (commonLowSet S.rows p H) < δ
      · exact Or.inl (hmono.trans_lt hsmall)
      · right
        have hbound := (hpS p (hp.restrict hST)).resolve_left hsmall
        have hstep := hpT p hp (le_of_not_gt hsmall)
        change volume.real (commonLowSet T.rows p H) ≤ 2 * q ^ (k + 1)
        calc
          _ ≤ q * volume.real (commonLowSet S.rows p H) := hstep
          _ ≤ q * (2 * q ^ k) := mul_le_mul_of_nonneg_left hbound hq0
          _ = _ := by rw [pow_succ]; ring
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (show 0 < δ / 2 by positivity) hq1
  obtain ⟨S, hS, hpS⟩ := hstage k
  refine ⟨S, hS, fun p hp => ?_⟩
  rcases hpS p hp with h | h
  · exact h
  · linarith

/-- Proposition 11 from the interval amplification statement, with compatible data on all rows. -/
theorem finiteObstruction_of_intervalAmplification (X : NodeArray) (r : ℕ → ℕ)
    (H c : ℝ) (N : ℕ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hamp : IntervalAmplification X r H c N) (δ : ℝ≥0∞) (hδ : 0 < δ) :
    ∃ g : ContinuousFunction, ‖g‖ ≤ 1 ∧ FiniteObstruction X r H δ N g := by
  obtain ⟨ε, _, hε, hεδ⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ
  have hε0 : 0 < ε := ENNReal.ofReal_pos.mp hε
  obtain ⟨S, hS, hpS⟩ := exists_small_low_stage X r H c ε N hc hc1 hε0 hamp
  obtain ⟨g, hg, hfits⟩ := S.continuous_extension_fits r
  refine ⟨g, hg, S.rows, hS, fun p hp => ?_⟩
  have hsmall := hpS p (hfits p hp)
  apply lt_trans _ hεδ
  apply (ENNReal.toReal_lt_toReal (commonLowSet_measure_ne_top _ _ _) ENNReal.ofReal_ne_top).mp
  simpa only [ENNReal.toReal_ofReal hε0.le, measureReal_def] using hsmall

theorem finiteAmplification_of_intervalAmplification (X : NodeArray) (r : ℕ → ℕ)
    (hamp : ∀ H : ℝ, 1 < H → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ N : ℕ, IntervalAmplification X r H c N) : FiniteAmplification X r := by
  intro H hH δ hδ N
  obtain ⟨c, hc, hc1, hlocal⟩ := hamp H hH
  exact finiteObstruction_of_intervalAmplification X r H c N hc hc1 (hlocal N) δ hδ

end Erdos1152
