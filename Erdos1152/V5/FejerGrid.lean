import Erdos1152.V5.FiniteFourier

/-!
The nonnegative finite Fejér grid used to impose the extra sampling constraints.
The grid weights form an exact partition of one and interpolate the coefficient
vector on the grid.  In particular their norm bound does not contain `L`.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset

namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def circleGrid (L : ℕ) (q : ZMod L) : FourierCircle :=
  ((2 * Real.pi * q.val / L : ℝ) : FourierCircle)

noncomputable def oneSidedDirichlet (L : ℕ) : CircleFunction :=
  ∑ j : Fin L, character (j : ℤ)

noncomputable def fejerGridWeight (L : ℕ) (q : ZMod L) : C(FourierCircle, ℝ) where
  toFun x := ‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2
  continuous_toFun := by fun_prop

theorem fejerGridWeight_nonneg (L : ℕ) (q : ZMod L) (x : FourierCircle) :
    0 ≤ fejerGridWeight L q x := by
  change 0 ≤ ‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2
  positivity

theorem character_grid (L : ℕ) [NeZero L] (n : ℤ) (q : ZMod L) :
    character n (circleGrid L q) = ZMod.stdAddChar ((n : ZMod L)*q) := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  calc
    character n (circleGrid L q) =
        Complex.exp (2 * Real.pi * Complex.I * (n * (q.val : ℤ)) / L) := by
      simp only [circleGrid, character, fourier_coe_apply]
      congr 1
      push_cast
      field_simp [hL, hpi]
      <;> ring
    _ = ZMod.stdAddChar ((n * (q.val : ℤ) : ℤ) : ZMod L) := by
      simpa only [Int.cast_mul] using (ZMod.stdAddChar_coe (N := L) (n * (q.val : ℤ))).symm
    _ = ZMod.stdAddChar ((n : ZMod L) * q) := by
      simp only [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]

theorem sum_character_grid (L : ℕ) [NeZero L] (n : ℤ) :
    ∑ q : ZMod L, character n (circleGrid L q) =
      if (n : ZMod L) = 0 then (L : ℂ) else 0 := by
  simp only [character_grid]
  split_ifs with hn
  · simp [hn]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L hn)

theorem fin_sub_cast_zero (L : ℕ) [NeZero L] (i j : Fin L) :
    (((i : ℤ)-(j : ℤ) : ℤ) : ZMod L) = 0 ↔ i = j := by
  rw [Int.cast_sub, sub_eq_zero]
  constructor
  · intro h
    have hv := congrArg ZMod.val h
    simpa [ZMod.val_natCast, Nat.mod_eq_of_lt i.isLt,
      Nat.mod_eq_of_lt j.isLt, Fin.ext_iff] using hv
  · intro h; simp [h]

theorem normSq_dirichlet_expansion (L : ℕ) (x : FourierCircle) :
    (‖oneSidedDirichlet L x‖^2 : ℂ) =
      ∑ i : Fin L, ∑ j : Fin L, character ((i:ℤ)-(j:ℤ)) x := by
  have hnorm : (‖oneSidedDirichlet L x‖^2 : ℂ) =
      oneSidedDirichlet L x * conj (oneSidedDirichlet L x) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hnorm]
  simp only [oneSidedDirichlet, ContinuousMap.sum_apply, map_sum,
    sum_mul_sum]
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  rw [sub_eq_add_neg, character_add]
  congr 1
  exact (fourier_neg (n := (j:ℤ))).symm

/-- Exact nonnegative partition of unity, independent of the grid size. -/
theorem sum_fejerGridWeight (L : ℕ) [NeZero L] (x : FourierCircle) :
    ∑ q : ZMod L, fejerGridWeight L q x = 1 := by
  have hL : (L : ℂ) ≠ 0 := by exact_mod_cast (NeZero.ne L)
  have hsum (i j : Fin L) :
      ∑ q : ZMod L, character ((i:ℤ)-(j:ℤ)) x *
        character (-((i:ℤ)-(j:ℤ))) (circleGrid L q) =
      if i = j then (L : ℂ) else 0 := by
    rw [← mul_sum, sum_character_grid]
    by_cases h : i = j
    · simp [h]
    · have hz : ((-((i:ℤ)-(j:ℤ)) : ℤ) : ZMod L) ≠ 0 := by
        intro hz
        have hz' : (((i:ℤ)-(j:ℤ) : ℤ) : ZMod L) = 0 := by
          apply neg_eq_zero.mp
          simpa only [Int.cast_neg] using hz
        exact h ((fin_sub_cast_zero L i j).mp hz')
      rw [if_neg hz, mul_zero, if_neg h]
  have hweight (q : ZMod L) :
      (fejerGridWeight L q x : ℂ) =
        (∑ i : Fin L, ∑ j : Fin L,
          character ((i:ℤ)-(j:ℤ)) x *
            character (-((i:ℤ)-(j:ℤ))) (circleGrid L q)) / (L : ℂ)^2 := by
    change ((‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2 : ℝ) : ℂ) = _
    simp only [Complex.ofReal_div, Complex.ofReal_pow,
      Complex.ofReal_natCast, normSq_dirichlet_expansion, character_sub]
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, Complex.ofReal_one]
  rw [Finset.sum_congr rfl (fun q _ => hweight q), ← Finset.sum_div]
  have hswap :
      (∑ q : ZMod L, ∑ i : Fin L, ∑ j : Fin L,
        character ((i:ℤ)-(j:ℤ)) x *
          character (-((i:ℤ)-(j:ℤ))) (circleGrid L q)) =
      ∑ i : Fin L, ∑ j : Fin L, ∑ q : ZMod L,
        character ((i:ℤ)-(j:ℤ)) x *
          character (-((i:ℤ)-(j:ℤ))) (circleGrid L q) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_comm
  rw [hswap]
  simp_rw [hsum]
  simp [pow_two, hL]

private theorem finEquiv_apply_eq_natCast (L : ℕ) [NeZero L] (i : Fin L) :
    (ZMod.finEquiv L) i = (i.val : ZMod L) := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    apply Fin.ext
    change i.val = i.val % (n + 1)
    exact (Nat.mod_eq_of_lt i.isLt).symm

theorem grid_dirichlet (L : ℕ) [NeZero L] (p q : ZMod L) :
    oneSidedDirichlet L (circleGrid L p-circleGrid L q) =
      if p = q then (L : ℂ) else 0 := by
  classical
  simp only [oneSidedDirichlet, ContinuousMap.sum_apply, character_sub,
    character_grid, Int.cast_natCast, Int.cast_neg]
  have he (i : Fin L) : ZMod.stdAddChar ((i : ZMod L)*p) *
      ZMod.stdAddChar (-((i : ZMod L))*q) =
      ZMod.stdAddChar ((p-q)*(i : ZMod L)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1; ring
  simp_rw [he]
  have hEquiv : (∑ i : Fin L, ZMod.stdAddChar ((p-q)*(i : ZMod L))) =
      ∑ i : ZMod L, ZMod.stdAddChar ((p-q)*i) := by
    exact Fintype.sum_equiv (ZMod.finEquiv L).toEquiv _ _ (fun i => by
      change ZMod.stdAddChar ((p-q)*(i : ZMod L)) =
        ZMod.stdAddChar ((p-q)*(ZMod.finEquiv L i))
      rw [finEquiv_apply_eq_natCast L i])
  rw [hEquiv]
  by_cases hpq : p = q
  · simp [hpq]
  · rw [if_neg hpq]
    exact AddChar.sum_eq_zero_of_ne_one
      (ZMod.isPrimitive_stdAddChar L (sub_ne_zero.mpr hpq))

@[simp] theorem fejerGridWeight_at_grid (L : ℕ) [NeZero L] (p q : ZMod L) :
    fejerGridWeight L q (circleGrid L p) = if p = q then 1 else 0 := by
  change ‖oneSidedDirichlet L (circleGrid L p-circleGrid L q)‖^2 / (L : ℝ)^2 = _
  rw [grid_dirichlet]
  split_ifs <;> simp [Complex.norm_natCast, NeZero.ne L]

-- The grid is auxiliary and is positive at every construction site.
-- ZMod 0 is infinite, so its unrestricted univ-sum is not well-typed.
noncomputable def fejerGridCombination (L : ℕ) [NeZero L] (a : ZMod L → ℂ) : CircleFunction where
  toFun x := ∑ q : ZMod L, a q * (fejerGridWeight L q x : ℂ)
  continuous_toFun := by fun_prop

@[simp] theorem fejerGridCombination_at_grid (L : ℕ) [NeZero L]
    (a : ZMod L → ℂ) (p : ZMod L) :
    fejerGridCombination L a (circleGrid L p) = a p := by
  simp [fejerGridCombination, fejerGridWeight_at_grid, apply_ite]

theorem norm_fejerGridCombination_le (L : ℕ) [NeZero L]
    (a : ZMod L → ℂ) (C : ℝ) (ha : ∀ q, ‖a q‖ ≤ C) :
    ∀ x, ‖fejerGridCombination L a x‖ ≤ C := by
  intro x
  calc
    ‖∑ q : ZMod L, a q * (fejerGridWeight L q x : ℂ)‖
        ≤ ∑ q : ZMod L, ‖a q * (fejerGridWeight L q x : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ q : ZMod L, C * fejerGridWeight L q x := by
      apply sum_le_sum
      intro q hq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fejerGridWeight_nonneg L q x)]
      exact mul_le_mul_of_nonneg_right (ha q) (fejerGridWeight_nonneg L q x)
    _ = C := by rw [← mul_sum, sum_fejerGridWeight, mul_one]

noncomputable def fejerGridCombinationLinear (L : ℕ) [NeZero L] :
    (ZMod L → ℂ) →ₗ[ℂ] CircleFunction where
  toFun := fejerGridCombination L
  map_add' a b := by ext x; simp [fejerGridCombination, add_mul, sum_add_distrib]
  map_smul' c a := by ext x; simp [fejerGridCombination, mul_assoc, mul_sum]

/-- One grid polynomial satisfying an arbitrary finite family of linear constraints,
normalized at an actual grid point. No mutual separation of the original data enters. -/
theorem exists_normalized_fejer_annihilator (L : ℕ) [NeZero L]
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ < L)
    (Ψ : CircleFunction →ₗ[ℂ] (κ → ℂ)) :
    ∃ a : ZMod L → ℂ, ∃ p : ZMod L,
      a p = 1 ∧ (∀ q, ‖a q‖ ≤ 1) ∧
      Ψ (fejerGridCombination L a) = 0 ∧
      (∀ x, ‖fejerGridCombination L a x‖ ≤ 1) ∧
      fejerGridCombination L a (circleGrid L p) = 1 := by
  obtain ⟨a, ha, hΨ⟩ := exists_common_kernel_vector
    (ι := ZMod L) (κ := κ) (by simpa using hκ)
    (Ψ.comp (fejerGridCombinationLinear L))
  obtain ⟨p, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (ZMod L))
    (fun q => ‖a q‖) (Finset.univ_nonempty)
  have hap : a p ≠ 0 := by
    intro hzero
    apply ha
    ext q
    have hq := hp.2 q (mem_univ q)
    have hq0 : ‖a q‖ ≤ 0 := by simpa [hzero] using hq
    exact norm_le_zero_iff.mp hq0
  let b : ZMod L → ℂ := fun q => (a p)⁻¹ * a q
  have hbn : ∀ q, ‖b q‖ ≤ 1 := by
    intro q
    simp only [b, norm_mul, norm_inv]
    rw [inv_mul_eq_div, div_le_one (norm_pos_iff.mpr hap)]
    exact hp.2 q (mem_univ q)
  have hbp : b p = 1 := inv_mul_cancel₀ hap
  have hbΨ : Ψ (fejerGridCombination L b) = 0 := by
    have he : fejerGridCombination L b = (a p)⁻¹ • fejerGridCombination L a := by
      ext x
      simp [b, fejerGridCombination, mul_assoc, mul_sum]
    rw [he, map_smul]
    change (a p)⁻¹ • (Ψ.comp (fejerGridCombinationLinear L)) a = 0
    rw [hΨ, smul_zero]
  exact ⟨b, p, hbp, hbn, hbΨ, norm_fejerGridCombination_le L b 1 hbn,
    by simpa using hbp⟩

end Erdos1152.V5
