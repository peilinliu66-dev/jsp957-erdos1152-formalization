import Erdos1152.SeparatedSamples
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Choose.Sum

/-! New proof candidate: factorial cancellation in the separated-node
Lagrange estimate. Not compiler checked in the authoring environment. -/
open Polynomial Finset Set
open scoped Classical
namespace Erdos1152

private theorem rising_factorial_product (n : ℕ) :
    (∏ j ∈ Finset.range n, ((j : ℝ) + 1)) = (n.factorial : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, Nat.factorial_succ]
    push_cast
    ring

private theorem descending_gap_product (n : ℕ) :
    (∏ j ∈ Finset.range n, |(n : ℝ) - j|) = (n.factorial : ℝ) := by
  calc
    _ = ∏ j ∈ Finset.range n, (((n - 1 - j : ℕ) : ℝ) + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have hjr : (j : ℝ) < n := by exact_mod_cast hjn
      have hnat : (n - 1 - j) + 1 + j = n := by omega
      have hr : ((n - 1 - j : ℕ) : ℝ) + 1 + j = n := by exact_mod_cast hnat
      rw [abs_of_nonneg (by linarith)]
      linarith
    _ = ∏ j ∈ Finset.range n, ((j : ℝ) + 1) :=
      Finset.prod_range_reflect (fun j : ℕ => (j : ℝ) + 1) n
    _ = (n.factorial : ℝ) := rising_factorial_product n

private theorem natural_gap_product (d i : ℕ) (hi : i ≤ d) :
    (∏ j ∈ (range (d + 1)).erase i, |(i : ℝ) - j|) =
      (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by
  induction d generalizing i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      simp
  | succ d ih =>
      by_cases hid : i ≤ d
      · have hset : (range (d + 1 + 1)).erase i =
            insert (d + 1) ((range (d + 1)).erase i) := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_insert]
          omega
        rw [hset, prod_insert (by simp), ih i hid]
        have hnonpos : (i : ℝ) - (d + 1 : ℕ) ≤ 0 := by
          have hcast : (i : ℝ) ≤ d := by exact_mod_cast hid
          push_cast
          linarith
        rw [abs_of_nonpos hnonpos,
          show d + 1 - i = (d - i) + 1 by omega, Nat.factorial_succ]
        push_cast
        rw [Nat.cast_sub hid]
        ring
      · have hie : i = d + 1 := by omega
        subst i
        have hset : (range (d + 1 + 1)).erase (d + 1) = range (d + 1) := by
          ext j
          simp only [Finset.mem_erase, Finset.mem_range]
          omega
        rw [hset, descending_gap_product]
        simp

private theorem prod_fin_erase_eq (n : ℕ) (i : Fin n) (f : ℕ → ℝ) :
    (∏ j ∈ (univ : Finset (Fin n)).erase i, f j.val) =
      ∏ j ∈ (range n).erase i.val, f j := by
  apply Finset.prod_bij (fun j _ => j.val)
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    exact mem_erase.mpr ⟨(fun h => hj (Fin.ext h)), mem_range.mpr j.isLt⟩
  · intro j hj k hk hjk
    exact Fin.ext hjk
  · intro j hj
    obtain ⟨hji, hjn⟩ := mem_erase.mp hj
    refine ⟨⟨j, mem_range.mp hjn⟩, ?_, rfl⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun h => hji (congrArg Fin.val h)
  · intro j hj
    rfl

/-- Exact denominator for equally spaced indices, including both endpoints. -/
theorem fin_gap_product (d : ℕ) (i : Fin (d + 1)) :
    (∏ j ∈ (univ : Finset (Fin (d + 1))).erase i, |(i.val : ℝ) - j.val|) =
      (i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ) := by
  rw [prod_fin_erase_eq (d + 1) i (fun j => |(i.val : ℝ) - j|)]
  exact natural_gap_product d i.val (by omega)

/-- The binomial sum is the step that prevents a spurious `d log d` restriction. -/
theorem sum_inverse_factorials (d : ℕ) :
    (∑ i : Fin (d + 1), (1 : ℝ) /
      ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ))) =
      (2 : ℝ) ^ d / (d.factorial : ℝ) := by
  have hdf : (d.factorial : ℝ) ≠ 0 := by positivity
  have heach (i : Fin (d + 1)) :
      (1 : ℝ) / ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ)) =
        (d.choose i.val : ℝ) / (d.factorial : ℝ) := by
    have hi : i.val ≤ d := by omega
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.choose_mul_factorial_mul_factorial hi)
    push_cast at h
    apply (div_eq_div_iff (by positivity) hdf).mpr
    nlinarith [h]
  simp_rw [heach]
  rw [← Finset.sum_div, Fin.sum_univ_eq_sum_range (fun i => (d.choose i : ℝ)) (d + 1)]
  congr 1
  exact_mod_cast Nat.sum_range_choose d

/-- A polynomial bounded on separated nodes is bounded on the entire segment. -/
theorem eval_bound_of_separated_nodes (p : ℝ[X]) (d : ℕ) (hp : p.natDegree ≤ d)
    (x : Fin (d + 1) → ℝ) (hmono : StrictMono x) (δ H : ℝ)
    (hδ : 0 < δ) (hH : 0 ≤ H) (hx : ∀ i, x i ∈ Icc (-1 : ℝ) 1)
    (hgap : ∀ i j, δ * |(i.val : ℝ) - j.val| ≤ |x i - x j|)
    (hval : ∀ i, |p.eval (x i)| ≤ H) (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) 1) :
    |p.eval z| ≤ H * (4 / δ) ^ d / (d.factorial : ℝ) := by
  classical
  have hbasis (i : Fin (d + 1)) :
      |(Lagrange.basis univ x i).eval z| ≤ (2 / δ) ^ d /
        ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ)) := by
    let s := (univ : Finset (Fin (d + 1))).erase i
    have hcard : s.card = d := by simp [s]
    have hnum : (∏ j ∈ s, |z - x j|) ≤ (2 : ℝ) ^ d := by
      calc
        _ ≤ ∏ _j ∈ s, (2 : ℝ) := by
          apply prod_le_prod
          · intro j hj; positivity
          · intro j hj
            apply abs_le.mpr
            constructor <;> linarith [(hx j).1, (hx j).2, hz.1, hz.2]
        _ = _ := by simp [hcard]
    have hden : δ ^ d * ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ)) ≤
        ∏ j ∈ s, |x i - x j| := by
      calc
        _ = ∏ j ∈ s, δ * |(i.val : ℝ) - j.val| := by
          rw [prod_mul_distrib, prod_const, hcard]
          rw [show (∏ j ∈ s, |(i.val : ℝ) - j.val|) =
            (i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ) from fin_gap_product d i]
        _ ≤ _ := prod_le_prod (fun j hj => mul_nonneg hδ.le (abs_nonneg _))
          (fun j hj => hgap i j)
    have hdpos : 0 < δ ^ d * ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ)) := by
      positivity
    have hrepr : |(Lagrange.basis univ x i).eval z| =
        (∏ j ∈ s, |z - x j|) / (∏ j ∈ s, |x i - x j|) := by
      simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C,
        eval_sub, eval_X, Finset.abs_prod, abs_mul, abs_inv]
      change (∏ j ∈ s, |x i - x j|⁻¹ * |z - x j|) = _
      rw [prod_mul_distrib, prod_inv_distrib]
      ring
    rw [hrepr]
    calc
      _ ≤ (2 : ℝ) ^ d / (∏ j ∈ s, |x i - x j|) :=
        div_le_div_of_nonneg_right hnum (le_of_lt (hdpos.trans_le hden))
      _ ≤ (2 : ℝ) ^ d / (δ ^ d *
          ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ))) :=
        div_le_div_of_nonneg_left (by positivity) hdpos hden
      _ = _ := by rw [div_pow]; ring
  have hdeg : p.degree < (univ : Finset (Fin (d + 1))).card := by
    simp only [card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt p.degree_le_natDegree
      (WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le hp))
  have heq := Lagrange.eq_interpolate hmono.injective.injOn hdeg
  have heval := congrArg (fun q : ℝ[X] => q.eval z) heq
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C] at heval
  calc
    |p.eval z| = |∑ i : Fin (d + 1), p.eval (x i) * (Lagrange.basis univ x i).eval z| :=
      congrArg abs heval
    _ ≤ ∑ i : Fin (d + 1), |p.eval (x i) * (Lagrange.basis univ x i).eval z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (d + 1), H * ((2 / δ) ^ d /
        ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ))) := by
      apply sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul (hval i) (hbasis i) (abs_nonneg _) hH
    _ = H * (2 / δ) ^ d * (∑ i : Fin (d + 1), (1 : ℝ) /
        ((i.val.factorial : ℝ) * ((d - i.val).factorial : ℝ))) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      ring
    _ = H * (4 / δ) ^ d / (d.factorial : ℝ) := by
      rw [sum_inverse_factorials]
      rw [show (4 : ℝ) / δ = (2 / δ) * 2 by ring, mul_pow]
      ring
end Erdos1152
