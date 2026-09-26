import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.LinearCombination

/-! Polynomial corrections for interpolation on a finite set of distinct nodes. -/

open Polynomial

namespace Erdos1152

noncomputable def nodePolynomial (Y : Finset ℝ) : ℝ[X] :=
  ∏ y ∈ Y, (X - C y)

theorem nodePolynomial_monic (Y : Finset ℝ) : (nodePolynomial Y).Monic := by
  exact monic_prod_X_sub_C id Y

@[simp] theorem nodePolynomial_natDegree (Y : Finset ℝ) :
    (nodePolynomial Y).natDegree = Y.card := by
  simp [nodePolynomial, natDegree_prod_of_monic, monic_X_sub_C]

@[simp] theorem nodePolynomial_eval (Y : Finset ℝ) (x : ℝ) :
    (nodePolynomial Y).eval x = ∏ y ∈ Y, (x - y) := by
  simp only [nodePolynomial, eval_prod, eval_sub, eval_X, eval_C]

theorem nodePolynomial_dvd_iff (Y : Finset ℝ) (p : ℝ[X]) :
    nodePolynomial Y ∣ p ↔ ∀ y ∈ Y, p.eval y = 0 := by
  classical
  by_cases hp : p = 0
  · simp [hp]
  change (Y.val.map fun y => X - C y).prod ∣ p ↔ _
  rw [Multiset.prod_X_sub_C_dvd_iff_le_roots hp]
  rw [Finset.val_le_iff_val_subset]
  constructor
  · intro h y hy
    exact (mem_roots hp).1 (h hy)
  · intro h y hy
    exact (mem_roots hp).2 (h y hy)

/-- Every interpolant differs from the prescribed polynomial by a node factor. -/
theorem interpolation_correction (Y : Finset ℝ) (b p : ℝ[X]) (d : ℕ)
    (hb : b.natDegree ≤ Y.card + d) (hp : p.natDegree ≤ Y.card + d)
    (h : ∀ y ∈ Y, p.eval y = b.eval y) :
    ∃ q : ℝ[X], p = b + nodePolynomial Y * q ∧ q.natDegree ≤ d := by
  have hdvd : nodePolynomial Y ∣ p - b := by
    apply (nodePolynomial_dvd_iff Y _).2
    intro y hy
    simp [h y hy]
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, ?_, ?_⟩
  · linear_combination hq
  · by_cases hq0 : q = 0
    · simp [hq0]
    have hdeg := natDegree_sub_le_of_le hp hb
    rw [hq, (nodePolynomial_monic Y).natDegree_mul' hq0,
      nodePolynomial_natDegree] at hdeg
    omega

/-- Removing previously assigned nodes only adds their number to the excess degree. -/
theorem degree_budget_after_removal (X S : Finset ℝ) (r : ℕ) :
    X.card + r = (X \ S).card + (r + (X ∩ S).card) := by
  have := Finset.card_sdiff_add_card_inter X S
  omega

end Erdos1152
