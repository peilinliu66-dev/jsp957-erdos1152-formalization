import Erdos1152.V5.SamplingContours
import Erdos1152.V5.FinitePoles
import Erdos1152.V5.EntireSinc

noncomputable section
open scoped Topology Real
open Complex MeasureTheory Set Filter
namespace Erdos1152.V5

private theorem grid_residue_sum (f : ℂ→ℂ) (t θ : ℝ) (ht : 0<t) (N : ℕ) :
    ∑a∈sampleNodes t θ N,f a/deriv (samplingSine t θ) a =
      (Real.pi*t:ℝ)⁻¹*∑j∈symmetricIndices N,(-1:ℂ)^j*f (samplePoint t θ j) := by
  rw [sampleNodes,Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [samplingSine_derivative t θ ht.ne' j,div_eq_mul_inv,mul_inv_rev,inverse_sign]
    push_cast
    ring
  · intro j hj k hk h
    exact samplePoint_injective t θ ht.ne' h

private theorem moment_residue_formula
    (g : ℂ→ℂ) (hd : Differentiable ℂ g) (t θ : ℝ) (ht : 0<t)
    (d N : ℕ) :
    (∮z in C(((θ/t:ℝ):ℂ),contourRadius t N),z^d*g z/samplingSine t θ z) =
      ((2*Real.pi*Complex.I)*(Real.pi*t:ℝ)⁻¹)*
        ∑j∈symmetricIndices N,(-1:ℂ)^j*(samplePoint t θ j:ℂ)^d*g (samplePoint t θ j) := by
  rw [circleIntegral_finite_simple_poles (fun z => z^d*g z) (samplingSine t θ)
    ((differentiable_id.pow d).mul hd) (by fun_prop [samplingSine])
    (sampleNodes t θ N) ((θ/t:ℝ):ℂ) (contourRadius t N)
    (by dsimp [contourRadius]; positivity) (sampleNodes_inside t θ ht N)
    (by intro a ha; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
        exact samplingSine_at_grid t θ ht.ne' j)
    (sampleNodes_simple t θ ht N) (samplingSine_all_zeros_in_disk t θ ht N),
    grid_residue_sum (fun z => z^d*g z) t θ ht N,mul_assoc]
  simp only [mul_assoc]

/-- The two alternating moments follow from actual vanishing contour integrals.
 They are not supplied as assumptions of the finite correction. -/
theorem hasSum_alternating_moment
    (g : ℂ→ℂ) (hgd : Differentiable ℂ g) (C σ t θ : ℝ)
    (hC : 0≤C) (ht : 0<t) (ht1 : t≤1) (hθ : |θ|≤1/2)
    (hσ : σ<Real.pi*t)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6)
    (d : ℕ) (hd : d≤1) :
    HasSum (fun j:ℤ => (-1:ℂ)^j*(samplePoint t θ j:ℂ)^d*g (samplePoint t θ j)) 0 := by
  let c : ℂ := (2*Real.pi*Complex.I)*(Real.pi*t:ℝ)⁻¹
  have hc : c≠0 := by
    dsimp [c]
    apply mul_ne_zero
    · exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) I_ne_zero
    · exact_mod_cast inv_ne_zero (mul_ne_zero Real.pi_ne_zero ht.ne')
  have hlim := (moment_contour_tendsto_zero g C σ t θ hC ht ht1 hθ hσ.le hg d hd).div_const c
  have hpartial : Tendsto (fun N => ∑j∈symmetricIndices N,
      (-1:ℂ)^j*(samplePoint t θ j:ℂ)^d*g (samplePoint t θ j)) atTop (𝓝 0) := by
    convert hlim using 1
    · ext N
      rw [moment_residue_formula g hgd t θ ht d N]
      change _ = c * _ / c
      rw [mul_div_cancel_left₀ _ hc]
    · simp
  have hs := signed_moment_summable g C σ t θ hC ht ht1 hθ hg d (hd.trans (by norm_num))
  have heq := tendsto_nhds_unique (hs.hasSum.comp symmetricIndices_tendsto) hpartial
  simpa [heq] using hs.hasSum

private theorem sinc_ratio_at_grid (t θ ξ : ℝ) (ht : 0<t) (j : ℤ)
    (hξ : ξ≠samplePoint t θ j) :
    samplingSine t θ ξ /
      (deriv (samplingSine t θ) (samplePoint t θ j)*(ξ-samplePoint t θ j)) =
      (cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ) := by
  have hv : t*samplePoint t θ j=(j:ℝ)+θ := by dsimp [samplePoint]; field_simp
  have hu : Real.pi*(t*(ξ-samplePoint t θ j))≠0 :=
    mul_ne_zero Real.pi_ne_zero (mul_ne_zero ht.ne' (sub_ne_zero.mpr hξ))
  have he : (Real.pi:ℂ)*((t:ℂ)*(ξ:ℂ)-θ)=
      Real.pi*(t*(ξ-samplePoint t θ j):ℝ)+(j:ℂ)*Real.pi := by
    push_cast
    have hv' : (t:ℂ)*(samplePoint t θ j:ℂ)=(j:ℂ)+θ := by exact_mod_cast hv
    linear_combination Real.pi*hv'
  rw [samplingSine,he,Complex.sin_add,samplingSine_derivative t θ ht.ne' j]
  simp only [Complex.sin_int_mul_pi,zero_mul,add_zero]
  rw [complex_cos_int_mul_pi]
  rw [cardinalSinc,Real.sinc_of_ne_zero hu]
  push_cast
  have ht' : (Real.pi*t:ℂ)≠0 := by exact_mod_cast mul_ne_zero Real.pi_ne_zero ht.ne'
  have hv' : (ξ:ℂ)-(samplePoint t θ j:ℂ)≠0 := by
    exact_mod_cast sub_ne_zero.mpr hξ
  field_simp [ht',hv',zpow_ne_zero j (by norm_num : (-1:ℂ)≠0)]
  ring

private theorem sinc_at_lattice (t θ : ℝ) (ht : 0<t) (k j : ℤ) :
    cardinalSinc (t*(samplePoint t θ k-samplePoint t θ j))=if j=k then 1 else 0 := by
  have he : t*(samplePoint t θ k-samplePoint t θ j)=((k-j:ℤ):ℝ) := by
    dsimp [samplePoint]; push_cast; field_simp; ring
  rw [he]
  by_cases hj : j=k
  · simp [hj,cardinalSinc]
  · have hn : (k-j:ℤ)≠0 := sub_ne_zero.mpr (Ne.symm hj)
    have hp : Real.pi*((k-j:ℤ):ℝ)≠0 :=
      mul_ne_zero Real.pi_ne_zero (by exact_mod_cast hn)
    rw [if_neg hj, cardinalSinc, Real.sinc_of_ne_zero hp]
    rw [mul_comm Real.pi, Real.sin_int_mul_pi, zero_div]

private theorem shannon_partial_error
    (g : ℂ→ℂ) (hgd : Differentiable ℂ g) (t θ ξ : ℝ) (ht : 0<t)
    (hξ : samplingSine t θ ξ≠0) (N : ℕ)
    (hξN : (ξ:ℂ)∈Metric.ball ((θ/t:ℝ):ℂ) (contourRadius t N)) :
    g ξ-∑j∈symmetricIndices N,
      g (samplePoint t θ j)*(cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ) =
      samplingSine t θ ξ*(2*Real.pi*Complex.I)⁻¹*
        (∮z in C(((θ/t:ℝ):ℂ),contourRadius t N),(g z/samplingSine t θ z)/(z-ξ)) := by
  have heq := cauchy_finite_simple_poles g (samplingSine t θ) hgd
    (by fun_prop [samplingSine]) (sampleNodes t θ N) ((θ/t:ℝ):ℂ) ξ
    (contourRadius t N) (by dsimp [contourRadius]; positivity) hξN hξ
    (sampleNodes_inside t θ ht N)
    (by intro a ha; obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ha
        exact samplingSine_at_grid t θ ht.ne' j)
    (sampleNodes_simple t θ ht N) (samplingSine_all_zeros_in_disk t θ ht N)
  have hterm : ∀j∈symmetricIndices N,
      samplingSine t θ ξ*((g (samplePoint t θ j)/
        deriv (samplingSine t θ) (samplePoint t θ j))/(ξ-samplePoint t θ j)) =
      g (samplePoint t θ j)*(cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ) := by
    intro j hj
    have hξj : ξ≠samplePoint t θ j := fun he =>
      hξ (he.symm ▸ samplingSine_at_grid t θ ht.ne' j)
    rw [←sinc_ratio_at_grid t θ ξ ht j hξj]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have heq' := congrArg (fun z:ℂ => samplingSine t θ ξ*z) heq
  rw [mul_sub,mul_div_cancel₀ _ hξ,Finset.mul_sum] at heq'
  rw [sampleNodes,Finset.sum_image] at heq'
  · rw [Finset.sum_congr rfl hterm] at heq'
    simpa [mul_assoc] using heq'.symm
  · intro j hj k hk he
    exact samplePoint_injective t θ ht.ne' he

/-- Shannon cardinal reconstruction for the actual entire functions used here.
 The contour proof also supplies the two moments needed for cubic finite tails. -/
theorem hasSum_shannon
    (g : ℂ→ℂ) (hgd : Differentiable ℂ g) (C σ t θ : ℝ)
    (hC : 0≤C) (ht : 0<t) (ht1 : t≤1) (hθ : |θ|≤1/2)
    (hσ : σ<Real.pi*t)
    (hg : ∀z,‖g z‖≤C*Real.exp (σ*|z.im|)/(1+‖z‖)^6) (ξ : ℝ) :
    HasSum (fun j:ℤ => g (samplePoint t θ j)*
      (cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ)) (g ξ) := by
  classical
  by_cases hξ : samplingSine t θ ξ=0
  · obtain ⟨k,hk⟩ := (samplingSine_zero_iff t θ ht.ne' ξ).mp hξ
    have hk' : ξ=samplePoint t θ k := Complex.ofReal_injective hk
    subst ξ
    convert (hasSum_ite_eq k (g (samplePoint t θ k))) using 1
    ext j
    rw [sinc_at_lattice t θ ht]
    by_cases hj : j = k <;> simp [hj]
  · have hs : Summable (fun j:ℤ => g (samplePoint t θ j)*
        (cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ)) := by
      apply (latticeWeight_summable.mul_left (16*C)).of_norm_bounded
      intro j
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      apply (mul_le_of_le_one_right (norm_nonneg _)
        (Real.abs_sinc_le_one _)).trans
      simpa using sample_moment_bound g C σ t θ hC ht ht1 hθ hg 0 (by norm_num) j
    have hc := (cauchy_contour_tendsto_zero g C σ t θ hC ht ht1 hθ hσ.le hg ξ).const_mul
      (samplingSine t θ ξ*(2*Real.pi*Complex.I)⁻¹)
    have hinside : ∀ᶠN in atTop,
        (ξ:ℂ)∈Metric.ball ((θ/t:ℝ):ℂ) (contourRadius t N) := by
      have hr : Tendsto (contourRadius t) atTop atTop :=
        (tendsto_atTop_add_const_right atTop (1/2 : ℝ)
          tendsto_natCast_atTop_atTop).atTop_div_const ht
      filter_upwards [hr.eventually_gt_atTop (dist (ξ:ℂ) ((θ/t:ℝ):ℂ))] with N hN
      exact Metric.mem_ball.mpr hN
    simp only [mul_zero] at hc
    have herr : Tendsto (fun N => g ξ-∑j∈symmetricIndices N,g (samplePoint t θ j)*
        (cardinalSinc (t*(ξ-samplePoint t θ j)):ℂ)) atTop (𝓝 0) := by
      apply hc.congr'
      filter_upwards [hinside] with N hN
      simpa using (shannon_partial_error g hgd t θ ξ ht hξ N hN).symm
    have hconst : Tendsto (fun _ : ℕ => g ξ) atTop (𝓝 (g ξ)) := tendsto_const_nhds
    have hsumlim := hconst.sub herr
    simp only [sub_sub_cancel,mul_zero,sub_zero] at hsumlim
    have he := tendsto_nhds_unique (hs.hasSum.comp symmetricIndices_tendsto) hsumlim
    simpa [he] using hs.hasSum

end Erdos1152.V5
