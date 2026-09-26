import Erdos1152.FiniteObstruction
import Mathlib.Topology.ContinuousMap.Weierstrass

/-! Density of the finite obstructions in the space of continuous functions. -/

open Polynomial MeasureTheory Set
open scoped ENNReal

namespace Erdos1152

theorem finiteObstruction_translate (X : NodeArray) (r : ℕ → ℕ)
    {H M ε : ℝ} {δ : ℝ≥0∞} {N : ℕ} {g : ContinuousFunction} (h : ℝ[X])
    (hg : FiniteObstruction X r H δ (max N h.natDegree) g)
    (hε : 0 < ε) (hH : M + ‖h.toContinuousMapOn Segment‖ ≤ ε * H) :
    FiniteObstruction X r M δ N (h.toContinuousMapOn Segment + ε • g) := by
  obtain ⟨s, hs, hg⟩ := hg
  refine ⟨s, fun n hn => (le_max_left _ _).trans (hs n hn), ?_⟩
  intro p hp
  let q := fun n => ε⁻¹ • (p n - h)
  have hq : ∀ n ∈ s, X.Interpolates r g n (q n) := by
    intro n hn
    have hdegree : h.natDegree ≤ n + 1 + r n := by
      have := (le_max_right N h.natDegree).trans (hs n hn)
      omega
    refine ⟨?_, ?_⟩
    · apply (natDegree_smul_le _ _).trans
      simpa only [max_self] using natDegree_sub_le_of_le (hp n hn).1 hdegree
    · intro i
      have he := (hp n hn).2 i
      simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,
        toContinuousMapOn_apply, toContinuousMap_apply, smul_eq_mul] at he
      simp only [q, eval_smul, eval_sub, smul_eq_mul, he]
      field_simp
      ring
  apply lt_of_le_of_lt (measure_mono ?_) (hg q hq)
  rintro x ⟨hx, hpx⟩
  refine ⟨hx, fun n hn => ?_⟩
  have hh : |h.eval x| ≤ ‖h.toContinuousMapOn Segment‖ :=
    ContinuousMap.norm_coe_le_norm (h.toContinuousMapOn Segment) ⟨x, hx⟩
  have hb : |(p n).eval x - h.eval x| ≤ ε * H :=
    (abs_sub _ _).trans ((add_le_add (hpx n hn) hh).trans hH)
  change |(ε⁻¹ • (p n - h)).eval x| ≤ H
  simp only [eval_smul, eval_sub, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hε]
  exact (inv_mul_le_iff₀ hε).2 hb

theorem dense_finiteObstruction_interior (X : NodeArray) (r : ℕ → ℕ)
    (hamp : FiniteAmplification X r) (M : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) (N : ℕ) :
    Dense (interior {f | FiniteObstruction X r M δ N f}) := by
  intro f
  apply Metric.mem_closure_iff.mpr
  intro η hη
  obtain ⟨h, hh⟩ := exists_polynomial_near_continuousMap (-1) 1 f (η / 2) (by linarith)
  let ε := η / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  obtain ⟨H, hH⟩ := exists_gt (max 1 ((M + 1 + ‖h.toContinuousMapOn Segment‖) / ε))
  have hH1 : 1 < H := (le_max_left _ _).trans_lt hH
  have hHM : M + 1 + ‖h.toContinuousMapOn Segment‖ ≤ ε * H := by
    have hb := (le_max_right _ _).trans_lt hH
    exact (div_lt_iff₀ hε).mp hb |>.le.trans_eq (mul_comm _ _)
  obtain ⟨g, hg, hgood⟩ := hamp H hH1 δ hδ (max N h.natDegree)
  let f' := h.toContinuousMapOn Segment + ε • g
  have hgood' : FiniteObstruction X r (M + 1) δ N f' :=
    finiteObstruction_translate X r h hgood hε hHM
  refine ⟨f', finiteObstruction_interior X r hgood' (by linarith), ?_⟩
  have hnorm : ‖ε • g‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  have htriangle : ‖f' - f‖ ≤ ‖h.toContinuousMapOn Segment - f‖ + ‖ε • g‖ := by
    calc
      _ = ‖(h.toContinuousMapOn Segment - f) + ε • g‖ := by congr 1; dsimp [f']; abel
      _ ≤ _ := norm_add_le _ _
  rw [dist_comm, dist_eq_norm]
  dsimp [ε] at hnorm
  linarith

end Erdos1152
