import Erdos1152.V5.FejerGrid

/-! The de la Vallée Poussin filter, with its uniform operator bound proved
from the positive Fejér kernels.  This is the low/high-frequency separator in
Privalov's finite-dimensional sampling proof. -/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

private abbrev differencePairs (L : ℕ) (n : ℤ) :=
  {p : Fin L × Fin L // (p.1 : ℤ)-(p.2 : ℤ)=n}

private noncomputable def nonnegDifferenceEquiv (L q : ℕ) :
    Fin (L-q) ≃ differencePairs L (q : ℤ) where
  toFun i := ⟨(⟨q+i, by omega⟩, ⟨i, by omega⟩), by dsimp; omega⟩
  invFun p := ⟨p.1.2, by have := p.2; have := p.1.1.isLt; omega⟩
  left_inv i := by ext; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext; have := p.2; dsimp at *; omega
    · rfl

private def differenceNegEquiv (L : ℕ) (n : ℤ) :
    differencePairs L n ≃ differencePairs L (-n) where
  toFun p := ⟨p.1.swap, by have := p.2; dsimp at *; omega⟩
  invFun p := ⟨p.1.swap, by have := p.2; dsimp at *; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_differencePairs (L : ℕ) (n : ℤ) :
    Fintype.card (differencePairs L n) = L-n.natAbs := by
  obtain ⟨q, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simpa using (Fintype.card_congr (nonnegDifferenceEquiv L q)).symm
  · rw [← Fintype.card_congr (differenceNegEquiv L (q : ℤ))]
    simpa using (Fintype.card_congr (nonnegDifferenceEquiv L q)).symm

noncomputable def fejerKernel (L : ℕ) : CircleFunction where
  toFun x := ((‖oneSidedDirichlet L x‖^2 / (L : ℝ) : ℝ) : ℂ)
  continuous_toFun := by fun_prop

private theorem fejerKernel_expansion (L : ℕ) (x : FourierCircle) :
    fejerKernel L x = (L : ℂ)⁻¹ *
      ∑ i : Fin L, ∑ j : Fin L, character ((i:ℤ)-(j:ℤ)) x := by
  change ((‖oneSidedDirichlet L x‖^2 / (L : ℝ) : ℝ) : ℂ) = _
  rw [Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow, normSq_dirichlet_expansion, div_eq_mul_inv]
  ring

/-- The exact triangular Fourier coefficients, including the cutoff endpoints. -/
theorem coefficient_fejerKernel (L : ℕ) (n : ℤ) :
    coefficient (fejerKernel L) n = ((L-n.natAbs : ℕ) : ℂ) / L := by
  classical
  unfold coefficient
  simp_rw [fejerKernel_expansion, mul_left_comm (character (-n) _),
    integral_const_mul, mul_sum, ← character_add]
  rw [integral_finsetSum]
  · have hInt (i j : Fin L) : Integrable
        (fun x : FourierCircle => character (-n+((i:ℤ)-(j:ℤ))) x) circleMeasure :=
      (character _).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hInner (i : Fin L) := integral_finsetSum Finset.univ (fun j _ => hInt i j)
    simp_rw [hInner, character_integral]
    have he : (∑ i : Fin L, ∑ j : Fin L,
        if -n+((i:ℤ)-(j:ℤ))=0 then (1 : ℂ) else 0) =
        (Fintype.card (differencePairs L n) : ℂ) := by
      rw [← Fintype.sum_prod_type']
      have hp (p : Fin L × Fin L) :
          -n+((p.1:ℤ)-(p.2:ℤ))=0 ↔ (p.1:ℤ)-(p.2:ℤ)=n := by omega
      simp_rw [hp]
      simp only [Finset.sum_boole, differencePairs]
      rw [Fintype.card_subtype]
    rw [he, card_differencePairs, div_eq_mul_inv]
    ring
  · intro i hi
    exact (by fun_prop : Continuous fun x : FourierCircle =>
      ∑ j : Fin L, character (-n+((i:ℤ)-(j:ℤ))) x).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem integral_norm_fejerKernel (L : ℕ) [NeZero L] :
    ∫ x, ‖fejerKernel L x‖ ∂circleMeasure = 1 := by
  have hnonneg (x : FourierCircle) :
      0 ≤ ‖oneSidedDirichlet L x‖^2/(L : ℝ) := by positivity
  have he (x : FourierCircle) :
      (‖fejerKernel L x‖ : ℂ) = fejerKernel L x := by
    change (‖((‖oneSidedDirichlet L x‖^2 / (L : ℝ) : ℝ) : ℂ)‖ : ℂ) = _
    simp only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hnonneg x)]
    rfl
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simp_rw [he]
  have hc := coefficient_fejerKernel L 0
  simpa [coefficient, NeZero.ne L] using hc

noncomputable def valleeKernel (L : ℕ) : CircleFunction :=
  (2 : ℂ) • fejerKernel (2*L) - fejerKernel L

theorem integral_norm_valleeKernel_le (L : ℕ) [NeZero L] :
    ∫ x, ‖valleeKernel L x‖ ∂circleMeasure ≤ 3 := by
  have : NeZero (2*L) := ⟨mul_ne_zero (by decide) (NeZero.ne L)⟩
  calc
    _ ≤ ∫ x, 2*‖fejerKernel (2*L) x‖+‖fejerKernel L x‖ ∂circleMeasure := by
      apply integral_mono
      · exact (valleeKernel L).continuous.norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (by fun_prop : Continuous fun x : FourierCircle =>
          2*‖fejerKernel (2*L) x‖+‖fejerKernel L x‖).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · intro x
        simpa [valleeKernel, norm_mul] using
          norm_sub_le ((2 : ℂ)*fejerKernel (2*L) x) (fejerKernel L x)
    _ = 3 := by
      rw [integral_add, integral_const_mul, integral_norm_fejerKernel,
        integral_norm_fejerKernel]
      · norm_num
      · exact ((fejerKernel (2*L)).continuous.norm.const_mul 2).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact (fejerKernel L).continuous.norm.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)

theorem coefficient_valleeKernel (L : ℕ) (n : ℤ) :
    coefficient (valleeKernel L) n =
      2*(((2*L-n.natAbs : ℕ) : ℂ)/(2*L))-
        (((L-n.natAbs : ℕ) : ℂ)/L) := by
  unfold coefficient valleeKernel
  simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul,
    mul_sub, mul_left_comm (character (-n) _)]
  rw [integral_sub, integral_const_mul]
  · change 2*coefficient (fejerKernel (2*L)) n-coefficient (fejerKernel L) n = _
    simp [coefficient_fejerKernel]
  · exact (by fun_prop : Continuous fun x : FourierCircle =>
      2*(character (-n) x*fejerKernel (2*L) x)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (by fun_prop : Continuous fun x : FourierCircle =>
      character (-n) x*fejerKernel L x).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem coefficient_valleeKernel_low (L : ℕ) [NeZero L] (n : ℤ)
    (hn : n.natAbs ≤ L) : coefficient (valleeKernel L) n = 1 := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne L
  rw [coefficient_valleeKernel, Nat.cast_sub (by omega), Nat.cast_sub hn]
  push_cast
  field_simp [hL]
  ring

theorem coefficient_valleeKernel_high (L : ℕ) (n : ℤ)
    (hn : 2*L ≤ n.natAbs) : coefficient (valleeKernel L) n = 0 := by
  simp [coefficient_valleeKernel, Nat.sub_eq_zero_of_le hn,
    Nat.sub_eq_zero_of_le (show L ≤ n.natAbs by omega)]

theorem convolution_character (K : CircleFunction) (n : ℤ) (x : FourierCircle) :
    circleConvolution K (character n) x = character n x * coefficient K n := by
  unfold circleConvolution coefficient
  simp_rw [character_sub]
  rw [show (fun y => K y*(character n x*character (-n) y)) =
      fun y => character n x*(character (-n) y*K y) by funext y; ring,
    integral_const_mul]

theorem vallee_low_character (L : ℕ) [NeZero L] (n : ℤ)
    (hn : n.natAbs ≤ L) (x : FourierCircle) :
    circleConvolution (valleeKernel L) (character n) x = character n x := by
  simp [convolution_character, coefficient_valleeKernel_low L n hn]

theorem vallee_high_character (L : ℕ) (n : ℤ)
    (hn : 2*L ≤ n.natAbs) (x : FourierCircle) :
    circleConvolution (valleeKernel L) (character n) x = 0 := by
  simp [convolution_character, coefficient_valleeKernel_high L n hn]

/-- Norm at most three, with no dependence on the trigonometric degree. -/
theorem vallee_operator_bound (L : ℕ) [NeZero L] (f : CircleFunction)
    (x : FourierCircle) : ‖circleConvolution (valleeKernel L) f x‖ ≤ 3*‖f‖ := by
  exact (norm_convolution_le _ _ ‖f‖ (fun y => f.norm_coe_le_norm y) x).trans
    (mul_le_mul_of_nonneg_right (integral_norm_valleeKernel_le L) (norm_nonneg _))

end Erdos1152.V5
