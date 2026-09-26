import Erdos1152

/-! The main theorem with Remez, cardinal growth, and the complementary-region
input expanded. The arbitrary row subsequence and finite assigned-node set remain explicit. -/

open Polynomial MeasureTheory Set Filter Topology
open scoped Classical

example (X : ∀ n : ℕ, Fin (n + 1) → Icc (-1 : ℝ) 1)
    (hX : ∀ n, Function.Injective (X n)) (r : ℕ → ℕ) (A : Set ℝ)
    (hR : ∀ (p : ℝ[X]) (E : Set ℝ) (H : ℝ), MeasurableSet E → E ⊆ Icc (-1) 1 →
      0 < volume.real E → 0 ≤ H → (∀ x ∈ E, |p.eval x| ≤ H) →
      ∀ z ∈ Icc (-1) 1, |p.eval z| ≤
        H * (Polynomial.Chebyshev.T ℝ (p.natDegree : ℤ)).eval (4 / volume.real E - 1))
    (hr : Tendsto (fun n => (r n : ℝ) / (n + 1 : ℝ)) atTop (𝓝 0))
    (hg : ∃ B : ℕ → Set ℝ,
      (∀ j, MeasurableSet (B j) ∧ B j ⊆ Icc (-1) 1 ∧
        ∀ S : Finset (Icc (-1 : ℝ) 1),
          let Y := fun n => ((Finset.univ.image (X n)) \ S).image Subtype.val
          let L := fun n z =>
            let P : ℝ[X] := ∏ y ∈ (Y n).erase z, (Polynomial.X - Polynomial.C y)
            P * Polynomial.C (P.eval z)⁻¹
          ∃ rows : ℕ → ℕ, Tendsto rows atTop atTop ∧
            ∃ z : ℕ → ℝ, (∀ n, z n ∈ Y (rows n)) ∧
              ∃ η : ℝ, 0 < η ∧ ∃ E : ℕ → Set ℝ,
                (∀ n, MeasurableSet (E n) ∧ E n ⊆ B j) ∧
                Tendsto (fun n => volume.real (B j \ E n)) atTop (𝓝 0) ∧
                ∀ᶠ n : ℕ in atTop, ∀ x ∈ E n,
                  Real.exp (η * (rows n + 1)) ≤ |(L (rows n) (z n)).eval x|) ∧
      ∀ᵐ x ∂volume.restrict (Ioo (-1) 1), x ∈ A → ∃ j, x ∈ B j)
    (hm : ∀ H : ℝ, 1 < H → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∀ᵐ x ∂volume.restrict (Ioo (-1 : ℝ) 1), x ∉ A → ∀ ε > (0 : ℝ),
        ∃ h : ℝ, 0 < h ∧ h ≤ ε ∧
          ∀ S : Finset (Icc (-1 : ℝ) 1), ∀ N : ℕ, ∃ n ≥ N,
            ∃ v : Icc (-1 : ℝ) 1 → ℝ,
              (∀ i, X n i ∉ S → |v (X n i)| ≤ 1) ∧
              ∀ p : ℝ[X], p.natDegree ≤ n + 1 + r n →
                (∀ i, X n i ∉ S → p.eval (X n i : ℝ) = v (X n i)) →
                volume.real ({y | |p.eval y| ≤ H} ∩ Ioo (x - h) (x + h)) ≤
                  (1 - c) * volume.real (Ioo (x - h) (x + h))) :
    ∃ f : C(Icc (-1 : ℝ) 1, ℝ), ∀ p : ℕ → ℝ[X],
      (∀ n, (p n).natDegree ≤ n + 1 + r n ∧
        ∀ i, (p n).eval (X n i : ℝ) = f (X n i)) →
      ∀ᵐ x ∂volume.restrict (Icc (-1 : ℝ) 1),
        limsup (fun n => ((|(p n).eval x| : ℝ) : EReal)) atTop = ⊤ := by
  exact Erdos1152.ae_limsup_eq_top_of_cardinalGrowth_minimal ⟨X, hX⟩ r A hR hr hg hm
