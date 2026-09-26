import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

noncomputable section
open Real Finset
namespace Erdos1152.V5

private theorem cube_sum_bound (N : ℕ) :
    (∑n∈range N,(1:ℝ)/((n:ℝ)+1)^3)≤2-2/((N:ℝ)+1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [sum_range_succ]
    have hpoint : (1:ℝ)/((N:ℝ)+1)^3≤2/(((N:ℝ)+1)*((N:ℝ)+2)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) N, sq_nonneg (N:ℝ),
        pow_nonneg (Nat.cast_nonneg (α := ℝ) N) 3]
    have he : (2-2/((N:ℝ)+1))+2/(((N:ℝ)+1)*((N:ℝ)+2))=
        2-2/(((N+1:ℕ):ℝ)+1) := by push_cast; field_simp; ring
    exact (add_le_add ih hpoint).trans_eq he

private theorem integer_distance_cube_sum (K i : ℕ) (hi : i<K) :
    (∑j∈range K,if j=i then (0:ℝ) else 1/|(j:ℝ)-(i:ℝ)|^3)≤4 := by
  have hK : K=(i+1)+(K-i-1) := by omega
  rw [hK,sum_range_add,sum_range_succ]
  simp only [ite_true, add_zero]
  have hleft : (∑j∈range i,if j=i then (0:ℝ) else 1/|(j:ℝ)-(i:ℝ)|^3)=
      ∑j∈range i,(1:ℝ)/((j:ℝ)+1)^3 := by
    rw [←sum_range_reflect (fun j:ℕ => (1:ℝ)/((j:ℝ)+1)^3) i]
    apply sum_congr rfl
    intro j hj
    have hji := mem_range.mp hj
    have hjiR : (j:ℝ)<i := by exact_mod_cast hji
    have hsub : ((i-1-j:ℕ):ℝ)+1=(i:ℝ)-(j:ℝ) := by
      rw [Nat.cast_sub (by omega : j ≤ i-1), Nat.cast_sub (by omega : 1 ≤ i)]
      push_cast
      ring
    rw [if_neg (by omega),abs_of_neg (by linarith),hsub]
    ring
  have hright : (∑j∈range (K-i-1),if i+1+j=i then (0:ℝ) else 1/|((i+1+j:ℕ):ℝ)-(i:ℝ)|^3)=
      ∑j∈range (K-i-1),(1:ℝ)/((j:ℝ)+1)^3 := by
    apply sum_congr rfl
    intro j hj
    rw [if_neg (by omega)]
    push_cast
    have he : (i:ℝ)+1+j-i=(j:ℝ)+1 := by ring
    rw [he,abs_of_pos (by positivity)]
  rw [hleft,hright]
  have hl := cube_sum_bound i
  have hr := cube_sum_bound (K-i-1)
  linarith [div_nonneg (by norm_num : (0:ℝ)≤2) (by positivity : 0≤(i:ℝ)+1),
    div_nonneg (by norm_num : (0:ℝ)≤2) (by positivity : 0≤((K-i-1:ℕ):ℝ)+1)]

theorem fin_distance_cube_sum (K : ℕ) (i : Fin K) :
    (∑j∈(univ:Finset (Fin K)).erase i,(1:ℝ)/|(j.val:ℝ)-(i.val:ℝ)|^3)≤4 := by
  have he : (∑j∈(univ:Finset (Fin K)).erase i,(1:ℝ)/|(j.val:ℝ)-(i.val:ℝ)|^3)=
      ∑j:Fin K,if j.val=i.val then (0:ℝ) else 1/|(j.val:ℝ)-(i.val:ℝ)|^3 := by
    rw [←sum_erase_add _ _ (mem_univ i)]
    simp only [ite_true, add_zero]
    apply sum_congr rfl
    intro j hj
    rw [if_neg (fun he => (mem_erase.mp hj).1 (Fin.ext he))]
  rw [he, Fin.sum_univ_eq_sum_range
    (fun j : ℕ => if j = i.val then (0:ℝ) else 1 / |(j:ℝ)-(i.val:ℝ)|^3) K]
  exact integer_distance_cube_sum K i.val i.isLt

theorem fin_index_distance_ge_one {K : ℕ} {i j : Fin K} (hij : i≠j) :
    (1:ℝ)≤|(i.val:ℝ)-(j.val:ℝ)| := by
  have hn : i.val≠j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hn with h | h
  · have hr : (i.val:ℝ)+1≤j.val := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    rw [abs_of_neg (by linarith)]
    linarith
  · have hr : (j.val:ℝ)+1≤i.val := by exact_mod_cast (Nat.succ_le_iff.mpr h)
    rw [abs_of_pos (by linarith)]
    linarith

/-- Cubic cross contributions near the closest selected center. Only the
non-nearest packets are estimated by their tails. -/
theorem cubic_cross_sum {K : ℕ} (c : Fin K→ℝ) (f : Fin K→ℝ→ℝ)
    (L T D : ℝ) (hL : 0<L) (hT : 0<T) (hD : 0≤D) (hLT : 4*T≤L)
    (hsep : ∀i j,L*|(i.val:ℝ)-(j.val:ℝ)|≤|c i-c j|)
    (i : Fin K) (z : ℝ)
    (htail : ∀j,2*T≤|z-c j|→|f j z|≤D/|z-c j|^3) (hnear : ∀j,|z-c i|≤|z-c j|) :
    (∑j∈(univ:Finset (Fin K)).erase i,|f j z|)≤32*D/L^3 := by
  have hpoint (j : Fin K) (hji : j≠i) :
      |f j z|≤(8*D/L^3)*(1/|(j.val:ℝ)-(i.val:ℝ)|^3) := by
    have hidx := fin_index_distance_ge_one hji
    have htri : |c j-c i|≤2*|z-c j| := by
      have hh := abs_sub_le (c j) z (c i)
      rw [abs_sub_comm (c j) z] at hh
      linarith [hnear j]
    have hdist : L*|(j.val:ℝ)-(i.val:ℝ)|/2≤|z-c j| := by linarith [hsep j i]
    have hfar : 2*T≤|z-c j| := by nlinarith
    have hpos : 0<L*|(j.val:ℝ)-(i.val:ℝ)|/2 := by positivity
    have hcub := pow_le_pow_left₀ hpos.le hdist 3
    apply (htail j hfar).trans
    calc
      D/|z-c j|^3≤D/(L*|(j.val:ℝ)-(i.val:ℝ)|/2)^3 :=
        div_le_div_of_nonneg_left hD (pow_pos hpos 3) hcub
      _=(8*D/L^3)*(1/|(j.val:ℝ)-(i.val:ℝ)|^3) := by field_simp; ring
  have hsum := sum_le_sum (s:=(univ:Finset (Fin K)).erase i)
    (fun j hj => hpoint j (mem_erase.mp hj).1)
  rw [←mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left (fin_distance_cube_sum K i) (by positivity : 0≤8*D/L^3)
  exact hsum.trans (hh.trans_eq (by ring))

/-- A point within rho of one center is closest to that center when L >= 2 rho. -/
theorem own_center_nearest {K : ℕ} (c : Fin K→ℝ) (L ρ : ℝ) (hρ : 0≤ρ) (hL : 2*ρ≤L)
    (hsep : ∀i j,L*|(i.val:ℝ)-(j.val:ℝ)|≤|c i-c j|)
    (i : Fin K) (z : ℝ) (hz : |z-c i|≤ρ) : ∀j,|z-c i|≤|z-c j| := by
  intro j
  by_cases hji : j=i
  · simpa [hji]
  · have hidx := fin_index_distance_ge_one hji
    have htri : |c j-c i|≤|z-c j|+|z-c i| := by
      simpa [abs_sub_comm (c j) z] using abs_sub_le (c j) z (c i)
    have hLs : L≤L*|(j.val:ℝ)-(i.val:ℝ)| := by nlinarith
    linarith [hsep j i]

/-- Existence of a nearest center is finite, not a geometric-density assumption. -/
theorem exists_nearest_center {K : ℕ} (hK : 0<K) (c : Fin K→ℝ) (z : ℝ) :
    ∃i:Fin K,∀j,|z-c i|≤|z-c j| := by
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (univ:Finset (Fin K)) (fun i => |z-c i|) univ_nonempty
  exact ⟨i,fun j => hmin j (mem_univ j)⟩

end Erdos1152.V5
