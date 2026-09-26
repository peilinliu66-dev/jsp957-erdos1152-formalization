import Erdos1152.V5.FiniteFourier
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Uniform bound for the harmonic sine polynomial.  The Abel estimate, the short
initial block and the long oscillatory tail are proved separately; the bound is
absolute, not logarithmic in the degree.  This supplies the bounded input in
Privalov's construction while its low-frequency part has harmonic-size value.
-/
noncomputable section
open scoped BigOperators Real
open Finset Set
namespace Erdos1152.V5

private theorem abel_finite (z w : ℕ → ℝ) (n : ℕ) :
    ∑ j ∈ range (n+1), w j*z j =
      w n*(∑ j ∈ range (n+1), z j) +
      ∑ j ∈ range n, (w j-w (j+1))*(∑ k ∈ range (j+1), z k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    rw [sum_range_succ (f := fun j =>
      (w j-w (j+1))*(∑ k ∈ range (j+1), z k)) (n := n)]
    rw [sum_range_succ (f := z) (n := n+1)]
    ring

/-- Abel's finite inequality with decreasing nonnegative weights. -/
theorem abs_weighted_sum_le (z w : ℕ → ℝ) (n : ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hw : ∀j≤n, 0≤w j)
    (hmono : ∀j<n, w (j+1)≤w j)
    (hpartial : ∀j≤n, |∑k∈range (j+1),z k|≤C) :
    |∑j∈range (n+1),w j*z j|≤C*w 0 := by
  rw [abel_finite]
  calc
    _ ≤ |w n*(∑j∈range (n+1),z j)|+
        |∑j∈range n,(w j-w (j+1))*(∑k∈range (j+1),z k)| := abs_add_le _ _
    _ ≤ w n*C+∑j∈range n,(w j-w (j+1))*C := by
      apply add_le_add
      · rw [abs_mul, abs_of_nonneg (hw n le_rfl)]
        exact mul_le_mul_of_nonneg_left (hpartial n le_rfl) (hw n le_rfl)
      · apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro j hj
        have hjn := mem_range.mp hj
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hmono j hjn))]
        exact mul_le_mul_of_nonneg_left (hpartial j (by omega))
          (sub_nonneg.mpr (hmono j hjn))
    _ = C*w 0 := by
      rw [← sum_mul, sum_range_sub']
      ring

private theorem sine_step (v t : ℝ) :
    Real.cos (v-t/2)-Real.cos (v+t/2)=2*Real.sin (t/2)*Real.sin v := by
  rw [Real.cos_sub_cos]
  have h1 : (v-t/2+(v+t/2))/2=v := by ring
  have h2 : (v-t/2-(v+t/2))/2=-(t/2) := by ring
  rw [h1,h2,Real.sin_neg]
  ring

theorem partial_sine_identity (a n : ℕ) (t : ℝ) :
    2*Real.sin (t/2)*(∑j∈range n,Real.sin (((a+j : ℕ):ℝ)*t)) =
      Real.cos (((a:ℝ)-1/2)*t)-Real.cos (((a+n:ℕ):ℝ)*t-t/2) := by
  induction n with
  | zero => simp; congr 1 <;> ring
  | succ n ih =>
    rw [sum_range_succ,mul_add,ih]
    have hs := sine_step (((a+n:ℕ):ℝ)*t) t
    rw [← hs]
    push_cast
    ring_nf

private theorem partial_sine_bound (a n : ℕ) {t : ℝ}
    (ht : 0<t) (htπ : t≤Real.pi) :
    |∑j∈range n,Real.sin (((a+j:ℕ):ℝ)*t)|≤Real.pi/t := by
  have hs : t/Real.pi≤Real.sin (t/2) := by
    have hh := Real.mul_le_sin (by linarith : 0≤t/2) (by linarith : t/2≤Real.pi/2)
    convert hh using 1 <;> field_simp <;> ring
  have hpos : 0<Real.sin (t/2) := lt_of_lt_of_le (div_pos ht Real.pi_pos) hs
  have hid := congrArg abs (partial_sine_identity a n t)
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0<(2:ℝ)),
    abs_of_pos hpos] at hid
  have hb : |Real.cos (((a:ℝ)-1/2)*t)-Real.cos (((a+n:ℕ):ℝ)*t-t/2)|≤2 := by
    apply (abs_sub _ _).trans
    have h₁ := Real.abs_cos_le_one (((a:ℝ)-1/2)*t)
    have h₂ := Real.abs_cos_le_one (((a+n:ℕ):ℝ)*t-t/2)
    linarith
  have hn : |∑j∈range n,Real.sin (((a+j:ℕ):ℝ)*t)|≤1/Real.sin (t/2) := by
    apply (le_div_iff₀ hpos).mpr
    nlinarith [hb]
  apply hn.trans
  rw [div_le_div_iff₀ hpos ht]
  have := (div_le_iff₀ Real.pi_pos).mp hs
  nlinarith

private theorem weighted_sine_tail (a n : ℕ) (ha : 0<a) {t : ℝ}
    (ht : 0<t) (htπ : t≤Real.pi) :
    |∑j∈range n,Real.sin (((a+j:ℕ):ℝ)*t)/(a+j:ℕ)|≤
      Real.pi/(t*a) := by
  cases n with
  | zero => simp; positivity
  | succ n =>
    have h := abs_weighted_sum_le
      (fun j => Real.sin (((a+j:ℕ):ℝ)*t))
      (fun j => (1:ℝ)/(a+j:ℕ)) n (Real.pi/t) (by positivity)
      (fun j hj => by positivity)
      (fun j hj => by
        apply one_div_le_one_div_of_le
        · exact_mod_cast (show 0<a+j by omega)
        · exact_mod_cast Nat.le_succ (a+j))
      (fun j hj => partial_sine_bound a (j+1) ht htπ)
    simpa [div_eq_mul_inv, mul_assoc,mul_comm,mul_left_comm] using h

noncomputable def harmonicSine (n : ℕ) (t : ℝ) : ℝ :=
  ∑j∈range n,Real.sin (((j+1:ℕ):ℝ)*t)/(j+1:ℕ)

/-- The uniform harmonic sine bound on the principal half-period. -/
theorem harmonicSine_bound_nonneg (n : ℕ) {t : ℝ}
    (ht : 0≤t) (htπ : t≤Real.pi) : |harmonicSine n t|≤1+Real.pi := by
  by_cases hz : t=0
  · simp [harmonicSine,hz]; positivity
  have ht0 : 0<t := lt_of_le_of_ne ht (Ne.symm hz)
  let M : ℕ := ⌊t⁻¹⌋₊
  have hM : (M:ℝ)≤t⁻¹ := Nat.floor_le (by positivity)
  have hM' : t⁻¹<(M:ℝ)+1 := Nat.lt_floor_add_one _
  have hMt : (M:ℝ)*t≤1 := by
    have := mul_le_mul_of_nonneg_right hM ht
    simpa [inv_mul_cancel₀ hz] using this
  have hMt' : 1≤((M:ℝ)+1)*t := by
    have := mul_lt_mul_of_pos_right hM' ht0
    have : 1<((M:ℝ)+1)*t := by simpa [inv_mul_cancel₀ hz] using this
    exact this.le
  have hsmall (k : ℕ) (hk : k≤M) : |harmonicSine k t|≤1 := by
    calc
      _ ≤ ∑j∈range k,|Real.sin (((j+1:ℕ):ℝ)*t)/(j+1:ℕ)| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑j∈range k,t := by
        apply sum_le_sum
        intro j hj
        rw [abs_div,abs_of_pos (by positivity : 0<((j+1:ℕ):ℝ)),
          div_le_iff₀ (by positivity)]
        calc
          |Real.sin (((j+1:ℕ):ℝ)*t)|≤|((j+1:ℕ):ℝ)*t| := Real.abs_sin_le_abs
          _ = t*((j+1:ℕ):ℝ) := by rw [abs_of_nonneg (by positivity)]; ring
      _ ≤ 1 := by
        simp only [sum_const,card_range,nsmul_eq_mul]
        exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) ht).trans hMt
  by_cases hn : n≤M
  · exact (hsmall n hn).trans (by linarith [Real.pi_pos])
  · have hsplit : harmonicSine n t = harmonicSine M t+
        ∑j∈range (n-M),Real.sin (((M+1+j:ℕ):ℝ)*t)/(M+1+j:ℕ) := by
      conv_lhs => rw [harmonicSine,←Nat.add_sub_of_le (le_of_not_ge hn),sum_range_add]
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [show M+j+1 = M+1+j by omega]
    rw [hsplit]
    have htail := weighted_sine_tail (M+1) (n-M) (by omega) ht0 htπ
    have htail' : Real.pi/(t*((M+1:ℕ):ℝ))≤Real.pi := by
      rw [div_le_iff₀ (by positivity)]
      have hm := mul_le_mul_of_nonneg_left hMt' Real.pi_pos.le
      push_cast
      nlinarith [hm]
    exact (abs_add_le _ _).trans (add_le_add (hsmall M le_rfl) (htail.trans htail'))

theorem harmonicSine_bound (n : ℕ) {t : ℝ} (ht : |t|≤Real.pi) :
    |harmonicSine n t|≤1+Real.pi := by
  by_cases ht0 : 0≤t
  · exact harmonicSine_bound_nonneg n ht0 ((le_abs_self t).trans ht)
  · have he : harmonicSine n (-t) = -harmonicSine n t := by
      simp [harmonicSine, mul_neg, Real.sin_neg, neg_div, sum_neg_distrib]
    have h := harmonicSine_bound_nonneg n (by linarith : 0≤-t)
      (by rwa [abs_of_neg (lt_of_not_ge ht0)] at ht)
    simpa [he] using h

noncomputable def privalovLow (A : ℕ) (t : ℝ) : ℝ :=
  ∑j∈range A,Real.cos (((A-1-j:ℕ):ℝ)*t)/(j+1:ℕ)

noncomputable def privalovHigh (A : ℕ) (t : ℝ) : ℝ :=
  ∑j∈range A,Real.cos (((A+1+j:ℕ):ℝ)*t)/(j+1:ℕ)

/-- The two frequency blocks have bounded difference despite the harmonic peak. -/
theorem privalov_split_identity (A : ℕ) (t : ℝ) :
    privalovLow A t-privalovHigh A t =
      2*Real.sin ((A:ℝ)*t)*harmonicSine A t := by
  unfold privalovLow privalovHigh harmonicSine
  rw [←sum_sub_distrib,mul_sum]
  apply sum_congr rfl
  intro j hj
  have hjA := mem_range.mp hj
  rw [←sub_div,Real.cos_sub_cos]
  have h1 : ((((A-1-j:ℕ):ℝ)*t+((A+1+j:ℕ):ℝ)*t)/2)=(A:ℝ)*t := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast; ring
  have h2 : ((((A-1-j:ℕ):ℝ)*t-((A+1+j:ℕ):ℝ)*t)/2)=-((j+1:ℕ):ℝ)*t := by
    rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega)]
    push_cast; ring
  rw [h1,h2]
  simp only [neg_mul,Real.sin_neg]
  ring

theorem privalov_split_bound (A : ℕ) {t : ℝ} (ht : |t|≤Real.pi) :
    |privalovLow A t-privalovHigh A t|≤2*(1+Real.pi) := by
  rw [privalov_split_identity,abs_mul,abs_mul]
  calc
    |(2:ℝ)| * |Real.sin ((A:ℝ)*t)| * |harmonicSine A t|
        ≤ 2*1*(1+Real.pi) := by
          gcongr
          · norm_num
          · exact Real.abs_sin_le_one _
          · exact harmonicSine_bound A ht
    _ = 2*(1+Real.pi) := by ring

@[simp] theorem privalovLow_zero (A : ℕ) :
    privalovLow A 0 = ∑j∈range A,(1:ℝ)/(j+1:ℕ) := by
  simp [privalovLow]

end Erdos1152.V5
