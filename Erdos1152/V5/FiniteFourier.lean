import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.ZMod

/-!
Finite Fourier calculations for the finite-dimensional form of the
Olevskii--Ulanovskii argument.  The circle has period `2π`; its measure here is
normalized Haar measure, not the length measure.  No sampling bound is assumed.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset

namespace Erdos1152.V5

abbrev FourierCircle := AddCircle (2 * Real.pi)
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
abbrev CircleFunction := C(FourierCircle, ℂ)

noncomputable def character (n : ℤ) : CircleFunction := fourier n
noncomputable def circleMeasure : Measure FourierCircle := AddCircle.haarAddCircle

instance : IsProbabilityMeasure circleMeasure := by
  unfold circleMeasure
  infer_instance

@[simp] theorem character_zero (x : FourierCircle) : character 0 x = 1 := by
  simp [character, fourier_zero]

@[simp] theorem character_at_zero (n : ℤ) : character n 0 = 1 := by
  exact fourier_eval_zero n

@[simp] theorem character_add (j k : ℤ) (x : FourierCircle) :
    character (j + k) x = character j x * character k x := fourier_add

@[simp] theorem character_norm (n : ℤ) (x : FourierCircle) :
    ‖character n x‖ = 1 := by
  exact Circle.norm_coe _

theorem character_translate (n : ℤ) (x y : FourierCircle) :
    character n (x + y) = character n x * character n y := by
  simp only [character, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem character_sub (n : ℤ) (x y : FourierCircle) :
    character n (x - y) = character n x * character (-n) y := by
  rw [sub_eq_add_neg, character_translate]
  congr 1
  simp only [character, fourier_apply, smul_neg, neg_smul]

@[simp] theorem character_integral (n : ℤ) :
    ∫ x, character n x ∂circleMeasure = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [if_neg hn]
    let : circleMeasure.IsAddRightInvariant := by
      unfold circleMeasure
      infer_instance
    exact integral_eq_zero_of_add_right_eq_neg
      (μ := circleMeasure) (fourier_add_half_inv_index hn (by positivity))

noncomputable def finiteFourier (s : Finset ℤ) (c : ℤ → ℂ) : CircleFunction :=
  ∑ n ∈ s, c n • character n

@[simp] theorem finiteFourier_apply (s : Finset ℤ) (c : ℤ → ℂ)
    (x : FourierCircle) : finiteFourier s c x = ∑ n ∈ s, c n * character n x := by
  simp [finiteFourier]

theorem integral_character_mul (j k : ℤ) :
    ∫ x, character j x * character k x ∂circleMeasure =
      if j + k = 0 then 1 else 0 := by
  simp only [← character_add, character_integral]

noncomputable def coefficient (f : CircleFunction) (n : ℤ) : ℂ :=
  ∫ x, character (-n) x * f x ∂circleMeasure

theorem coefficient_finiteFourier (s : Finset ℤ) (c : ℤ → ℂ) (n : ℤ) :
    coefficient (finiteFourier s c) n = if n ∈ s then c n else 0 := by
  classical
  unfold coefficient
  simp only [finiteFourier_apply, mul_sum]
  rw [integral_finsetSum]
  · simp_rw [show ∀ j x, character (-n) x * (c j * character j x) =
        c j * (character (-n) x * character j x) by intros; ring,
      integral_const_mul, integral_character_mul]
    simpa [neg_add_eq_zero, eq_comm] using
      (sum_ite_eq' s n c)
  · intro j hj
    exact (by fun_prop : Continuous fun x : FourierCircle =>
      character (-n) x * (c j * character j x)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem norm_coefficient_le (f : CircleFunction) (n : ℤ) :
    ‖coefficient f n‖ ≤ ‖f‖ := by
  unfold coefficient
  simpa using norm_integral_le_of_norm_le_const (μ := circleMeasure)
    (C := ‖f‖) (Filter.Eventually.of_forall fun x => by
      rw [norm_mul, character_norm, one_mul]
      exact f.norm_coe_le_norm x)

noncomputable def circleConvolution (f g : CircleFunction) :
    FourierCircle → ℂ := fun x => ∫ y, f y * g (x-y) ∂circleMeasure

theorem convolution_finiteFourier (s t : Finset ℤ) (c d : ℤ → ℂ)
    (x : FourierCircle) :
    circleConvolution (finiteFourier s c) (finiteFourier t d) x =
      ∑ n ∈ s ∩ t, c n * d n * character n x := by
  classical
  unfold circleConvolution
  simp only [finiteFourier_apply, sum_mul_sum]
  rw [integral_finsetSum]
  · have hInt (j k : ℤ) : Integrable
        (fun y : FourierCircle => c j * character j y * (d k * character k (x-y)))
        circleMeasure :=
      (by fun_prop : Continuous fun y : FourierCircle =>
        c j * character j y * (d k * character k (x-y))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    have hInner (j : ℤ) := integral_finsetSum t (fun k _ => hInt j k)
    simp_rw [hInner]
    have he (j k : ℤ) :
        (∫ y, (c j * character j y) * (d k * character k (x-y))
          ∂circleMeasure) =
        if j = k then c j * d k * character k x else 0 := by
      simp_rw [character_sub]
      rw [show (fun y => c j * character j y *
            (d k * (character k x * character (-k) y))) =
          fun y => (c j*d k*character k x) *
            (character j y * character (-k) y) by funext y; ring,
        integral_const_mul, integral_character_mul]
      by_cases hjk : j = k
      · simp [hjk]
      · have hne : j + -k ≠ 0 := by
          simpa only [← sub_eq_add_neg] using sub_ne_zero.mpr hjk
        simp [hjk, hne]
    simp_rw [he]
    simp [sum_ite_irrel, sum_filter]
  · intro j hj
    exact (by fun_prop : Continuous fun y : FourierCircle =>
      ∑ k ∈ t, c j * character j y * (d k * character k (x-y))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- A real nonnegative convolution kernel has operator bound equal to its mass. -/
theorem norm_convolution_le (f g : CircleFunction) (C : ℝ)
    (hC : ∀ y, ‖g y‖ ≤ C) :
    ∀ x, ‖circleConvolution f g x‖ ≤ (∫ y, ‖f y‖ ∂circleMeasure) * C := by
  intro x
  unfold circleConvolution
  calc
    ‖∫ y, f y * g (x-y) ∂circleMeasure‖
        ≤ ∫ y, ‖f y * g (x-y)‖ ∂circleMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f y‖ * C ∂circleMeasure := by
      apply integral_mono
      · exact (by fun_prop : Continuous fun y : FourierCircle =>
          ‖f y * g (x-y)‖).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · exact (by fun_prop : Continuous fun y : FourierCircle =>
          ‖f y‖*C).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      · intro y
        change ‖f y * g (x-y)‖ ≤ ‖f y‖ * C
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)
    _ = (∫ y, ‖f y‖ ∂circleMeasure)*C := integral_mul_const _ _

/-- The dimension argument in the localized finite sampling construction.
All constraints are actual linear maps on the finite vector of coefficients. -/
theorem exists_common_kernel_vector {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hcard : Fintype.card κ < Fintype.card ι)
    (L : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) :
    ∃ a : ι → ℂ, a ≠ 0 ∧ L a = 0 := by
  by_contra h
  have hzero : ∀ a, L a = 0 → a = 0 := by
    intro a ha
    by_contra hn
    exact h ⟨a, hn, ha⟩
  have hinj : Function.Injective L := by
    intro a b hab
    have hz : L (a-b) = 0 := by simp [map_sub, hab]
    exact sub_eq_zero.mp (hzero _ hz)
  have hf := LinearMap.finrank_le_finrank_of_injective hinj
  simp only [Module.finrank_pi, Module.finrank_self, mul_one] at hf
  exact (not_le_of_gt hcard) hf

end Erdos1152.V5
