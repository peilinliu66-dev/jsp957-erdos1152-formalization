import Erdos1152.V5.CircleInterpolation

noncomputable section
open scoped BigOperators Real
open Finset Set Filter
namespace Erdos1152.V5

/-- A dyadic block contributes at least one half. -/
theorem harmonicHeight_double (n : ℕ) (hn : 0<n) :
    harmonicHeight n+1/2≤harmonicHeight (2*n) := by
  rw [show 2*n=n+n by omega]
  unfold harmonicHeight
  rw [sum_range_add]
  apply add_le_add le_rfl
  calc
    (1:ℝ)/2 = ∑j∈range n,(1:ℝ)/(2*n) := by
      simp only [sum_const,card_range,nsmul_eq_mul]
      field_simp
    _ ≤ ∑j∈range n,(1:ℝ)/(n+j+1:ℕ) := by
      apply sum_le_sum
      intro j hj
      apply one_div_le_one_div_of_le
      · positivity
      · have := mem_range.mp hj
        exact_mod_cast (show n+j+1≤2*n by omega)

theorem harmonicHeight_pow_two (j : ℕ) :
    1+(j:ℝ)/2≤harmonicHeight (2^j) := by
  induction j with
  | zero => simp [harmonicHeight]
  | succ j ih =>
    have hs := harmonicHeight_double (2^j) (by positivity)
    rw [Nat.mul_comm 2 (2^j)] at hs
    rw [pow_succ]
    push_cast
    nlinarith [hs]

theorem exists_harmonicHeight_ge (B : ℝ) :
    ∃A : ℕ,0<A ∧ B≤harmonicHeight A := by
  obtain ⟨j,hj⟩ := exists_nat_gt (2*B)
  refine ⟨2^j,by positivity,?_⟩
  exact (show B≤1+(j:ℝ)/2 by linarith).trans (harmonicHeight_pow_two j)

/-- Explicit parameter family for the finite Bernstein localization.
`m=4q`, `k=32q A²`, `ρ=k+2q`, `R₀=k+q` gives an exact node budget
and a band gap independent of the scale parameter `q`.
-/
def localizationDegree (A q : ℕ) : ℕ := 32*q*A*A
def localizationRadius (A q : ℕ) : ℕ := localizationDegree A q+2*q
noncomputable def localizationInner (A q : ℕ) : ℝ := localizationDegree A q+q
noncomputable def localizationBandwidth (A : ℕ) : ℝ :=
  Real.pi*(32*A*A)/(32*A*A+1)
noncomputable def localizationGamma (A : ℕ) : ℝ :=
  Real.pi/(16*(32*A*A+1))

theorem localization_node_budget (A q : ℕ) :
    2*localizationRadius A q+1=2*(8*(4*q)*A*A)+4*q+1 := by
  unfold localizationRadius localizationDegree
  ring

theorem localization_frequency (A q : ℕ) (hq : 0<q) :
    Real.pi*localizationDegree A q/localizationInner A q=localizationBandwidth A := by
  unfold localizationInner localizationBandwidth localizationDegree
  push_cast
  have hqr : (q:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hq)
  have hd : (32*(A:ℝ)*A+1)≠0 := by positivity
  field_simp [hqr,hd]

theorem localization_gap (A : ℕ) :
    localizationBandwidth A+16*localizationGamma A=Real.pi ∧
      0<localizationGamma A := by
  unfold localizationBandwidth localizationGamma
  constructor
  · field_simp
  · positivity

theorem localization_margin (A q : ℕ) :
    (localizationRadius A q:ℝ)-localizationInner A q=q := by
  unfold localizationRadius localizationInner
  push_cast
  ring

end Erdos1152.V5
