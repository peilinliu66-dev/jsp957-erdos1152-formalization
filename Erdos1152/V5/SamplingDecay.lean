import Erdos1152.V5.SineContour
import Mathlib.Analysis.PSeries

noncomputable section
open scoped Topology Real
open Complex Set Filter
namespace Erdos1152.V5

def symmetricIndices (N : ℕ) : Finset ℤ := Finset.Icc (-(N:ℤ)) N
def latticeWeight (j : ℤ) : ℝ := 1/(1+|(j:ℝ)|)^4

theorem symmetricIndices_tendsto : Tendsto symmetricIndices atTop atTop := by
  apply tendsto_atTop.mpr
  intro s
  apply (Filter.eventually_all_finset s).mpr
  intro j hj
  filter_upwards [eventually_ge_atTop j.natAbs] with N hN
  have hp : j ≤ (j.natAbs : ℤ) := Int.le_natAbs
  have hm : -j ≤ (j.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -j))
  simpa [symmetricIndices,Finset.mem_Icc] using
    (show -(N:ℤ)≤j ∧ j≤N by omega)

theorem latticeWeight_nonneg (j : ℤ) : 0≤latticeWeight j := by
  unfold latticeWeight; positivity

theorem latticeWeight_summable : Summable latticeWeight := by
  apply (Real.summable_one_div_int_pow.mpr (by norm_num : 1<(4:ℕ))).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0:ℤ)] with j hj
  have hn : 0 < |(j:ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  rw [Real.norm_eq_abs,abs_of_nonneg (latticeWeight_nonneg j),latticeWeight]
  rw [←(show Even (4:ℕ) from ⟨2,rfl⟩).pow_abs (j:ℝ)]
  exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
    (pow_le_pow_left₀ hn.le (by linarith) 4)

/-- The grid phase is controlled uniformly; no separation assumption is made on
 the interpolation nodes that were used to construct the Bernstein function. -/
theorem lattice_distance_comparison (t θ : ℝ) (ht : 0<t) (ht1 : t≤1)
    (hθ : |θ|≤1/2) (j : ℤ) :
    1+|(j:ℝ)|≤2*(1+|samplePoint t θ j|) := by
  have hsum : (j:ℝ)+θ=t*samplePoint t θ j := by
    dsimp [samplePoint]; field_simp
  have htriangle := abs_sub ((j:ℝ)+θ) θ
  rw [add_sub_cancel_right,hsum,abs_mul,abs_of_pos ht] at htriangle
  have hmul := mul_le_mul_of_nonneg_right ht1 (abs_nonneg (samplePoint t θ j))
  nlinarith [abs_nonneg (samplePoint t θ j)]

theorem sample_moment_bound (g : ℂ→ℂ) (C σ t θ : ℝ)
    (hC : 0≤C) (ht : 0<t) (ht1 : t≤1) (hθ : |θ|≤1/2)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (d : ℕ) (hd : d≤2) (j : ℤ) :
    ‖((samplePoint t θ j:ℂ)^d)*g (samplePoint t θ j)‖≤16*C*latticeWeight j := by
  let v := samplePoint t θ j
  have hv : ‖(v:ℂ)‖=|v| := by simp
  have hb : ‖g v‖≤C/(1+|v|)^6 := by
    simpa using hg (v:ℂ)
  have hpow : |v|^d≤(1+|v|)^2 := by
    interval_cases d
    · simp only [pow_zero]
      nlinarith [abs_nonneg v, sq_nonneg (|v|)]
    · simp only [pow_one]
      nlinarith [abs_nonneg v, sq_nonneg (|v|)]
    · exact pow_le_pow_left₀ (abs_nonneg v) (by linarith) 2
  have hdist := lattice_distance_comparison t θ ht ht1 hθ j
  have hdist4 := pow_le_pow_left₀ (by positivity) hdist 4
  rw [mul_pow] at hdist4
  norm_num at hdist4
  rw [norm_mul,norm_pow,hv]
  calc
    |v|^d*‖g v‖≤(1+|v|)^2*(C/(1+|v|)^6) :=
      mul_le_mul hpow hb (norm_nonneg _) (by positivity)
    _=C/(1+|v|)^4 := by field_simp
    _≤16*C*latticeWeight j := by
      unfold latticeWeight
      rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hdist4 hC]

theorem sample_moment_summable (g : ℂ→ℂ) (C σ t θ : ℝ)
    (hC : 0≤C) (ht : 0<t) (ht1 : t≤1) (hθ : |θ|≤1/2)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (d : ℕ) (hd : d≤2) :
    Summable (fun j:ℤ => (samplePoint t θ j:ℂ)^d*g (samplePoint t θ j)) :=
  (latticeWeight_summable.mul_left (16*C)).of_norm_bounded
    (sample_moment_bound g C σ t θ hC ht ht1 hθ hg d hd)

theorem sign_norm (j : ℤ) : ‖(-1:ℂ)^j‖=1 := by simp

theorem sign_mul_self (j : ℤ) : (-1:ℂ)^j*(-1:ℂ)^j=1 := by
  rw [← mul_zpow]
  norm_num

theorem inverse_sign (j : ℤ) : ((-1:ℂ)^j)⁻¹=(-1:ℂ)^j :=
  inv_eq_of_mul_eq_one_left (sign_mul_self j)

theorem signed_moment_summable (g : ℂ→ℂ) (C σ t θ : ℝ)
    (hC : 0≤C) (ht : 0<t) (ht1 : t≤1) (hθ : |θ|≤1/2)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (d : ℕ) (hd : d≤2) :
    Summable (fun j:ℤ => (-1:ℂ)^j*(samplePoint t θ j:ℂ)^d*g (samplePoint t θ j)) := by
  apply (latticeWeight_summable.mul_left (16*C)).of_norm_bounded
  intro j
  simpa [mul_assoc,norm_mul,sign_norm] using
    sample_moment_bound g C σ t θ hC ht ht1 hθ hg d hd j

/-- A single summable majorant gives phase-uniform finite truncation. -/
def samplingTail (N : ℕ) : ℝ :=
  (∑'j:ℤ,latticeWeight j)-∑j∈symmetricIndices N,latticeWeight j

theorem samplingTail_nonneg (N : ℕ) : 0≤samplingTail N := by
  exact sub_nonneg.mpr (Summable.sum_le_tsum (symmetricIndices N)
    (fun j hj => latticeWeight_nonneg j) latticeWeight_summable)

theorem samplingTail_tendsto : Tendsto samplingTail atTop (𝓝 0) := by
  have h := latticeWeight_summable.hasSum.comp symmetricIndices_tendsto
  have hc : Tendsto (fun _ : ℕ => ∑'j:ℤ,latticeWeight j) atTop
      (𝓝 (∑'j:ℤ,latticeWeight j)) := tendsto_const_nhds
  change Tendsto (fun N => (∑'j:ℤ,latticeWeight j) -
    ∑j∈symmetricIndices N,latticeWeight j) atTop (𝓝 0)
  simpa using hc.sub h

theorem norm_tsum_sub_symmetric_le {f : ℤ→ℂ} {D : ℝ} (hD : 0≤D)
    (hf : ∀j,‖f j‖≤D*latticeWeight j) (N : ℕ) :
    ‖(∑'j,f j)-∑j∈symmetricIndices N,f j‖≤D*samplingTail N := by
  have hs : Summable f := (latticeWeight_summable.mul_left D).of_norm_bounded hf
  have hw := (latticeWeight_summable.mul_left D)
  have hn : Summable (fun j : ℤ => ‖f j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hf hw
  rw [←hs.sum_add_tsum_compl (s := symmetricIndices N),add_sub_cancel_left]
  apply (norm_tsum_le_tsum_norm (hn.subtype _)).trans
  calc
    (∑'j:{j:ℤ // j∉symmetricIndices N},‖f j‖)
        ≤∑'j:{j:ℤ // j∉symmetricIndices N},D*latticeWeight j :=
      Summable.tsum_le_tsum (fun j => hf j) (hn.subtype _) (hw.subtype _)
    _=D*samplingTail N := by
      rw [tsum_mul_left]
      unfold samplingTail
      have he := latticeWeight_summable.sum_add_tsum_compl (s := symmetricIndices N)
      congr 1
      change (∑'j : ↥((↑(symmetricIndices N) : Set ℤ)ᶜ), latticeWeight j) = _
      linarith

end Erdos1152.V5
