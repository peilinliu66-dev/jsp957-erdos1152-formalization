import Erdos1152.V4.MinimumPrinciple
import Erdos1152.Interpolation

/-!
# The genuine finite-row external field and its polynomial weight

No auxiliary equally spaced points occur here: Y is the actual undeleted row.
The field is defined from the actual exterior node product. We prove its first
two derivatives, convexity, normalization, and the exact exponential identity,
then lift any local polynomial to a global polynomial with the correct degree.
The construction of the required local polynomial remains a separate task.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped ENNReal Classical

namespace Erdos1152.V4

noncomputable def insideNodes (Y : Finset ℝ) (a h : ℝ) : Finset ℝ :=
  Y.filter (fun t => t ∈ Ioo (a - h) (a + h))

noncomputable def outsideNodes (Y : Finset ℝ) (a h : ℝ) : Finset ℝ :=
  Y \ insideNodes Y a h

noncomputable def finiteField (Y : Finset ℝ) (a h u : ℝ) : ℝ :=
  -(∑ t ∈ outsideNodes Y a h, (Real.log (a + h*u - t) - Real.log (a-t))) /
    (insideNodes Y a h).card

noncomputable def finiteFieldFirst (Y : Finset ℝ) (a h u : ℝ) : ℝ :=
  -(∑ t ∈ outsideNodes Y a h, h / (a + h*u - t)) / (insideNodes Y a h).card

noncomputable def finiteFieldSecond (Y : Finset ℝ) (a h u : ℝ) : ℝ :=
  (∑ t ∈ outsideNodes Y a h, h^2 / (a + h*u - t)^2) / (insideNodes Y a h).card

@[simp] theorem finiteField_zero (Y : Finset ℝ) (a h : ℝ) : finiteField Y a h 0 = 0 := by
  simp [finiteField]

theorem inside_outside_card (Y : Finset ℝ) (a h : ℝ) :
    (insideNodes Y a h).card + (outsideNodes Y a h).card = Y.card := by
  have hsub : insideNodes Y a h ⊆ Y := Finset.filter_subset _ _
  simpa only [outsideNodes, Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hsub

theorem outsideNodes_side {Y : Finset ℝ} {a h t : ℝ}
    (ht : t ∈ outsideNodes Y a h) : t ≤ a-h ∨ a+h ≤ t := by
  have htY := (Finset.mem_sdiff.mp ht).1
  have htI := (Finset.mem_sdiff.mp ht).2
  have hout : t ∉ Ioo (a-h) (a+h) := by
    intro hi
    exact htI (Finset.mem_filter.mpr ⟨htY, hi⟩)
  by_cases hleft : t ≤ a-h
  · exact Or.inl hleft
  · exact Or.inr (le_of_not_gt (fun hr => hout ⟨lt_of_not_ge hleft, hr⟩))

theorem affine_mem_local {a h u : ℝ} (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) :
    a + h*u ∈ Ioo (a-h) (a+h) := by
  have h₁ := mul_lt_mul_of_pos_left hu.1 hh
  have h₂ := mul_lt_mul_of_pos_left hu.2 hh
  constructor <;> nlinarith

theorem outside_affine_ne_zero {Y : Finset ℝ} {a h u t : ℝ}
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) (ht : t ∈ outsideNodes Y a h) :
    a+h*u-t ≠ 0 := by
  have hx := affine_mem_local (a := a) hh hu
  rcases outsideNodes_side ht with hl | hr
  · exact (by linarith [hx.1] : 0 < a+h*u-t).ne'
  · exact (by linarith [hx.2] : a+h*u-t < 0).ne

theorem outside_ratio_pos {Y : Finset ℝ} {a h u t : ℝ}
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) (ht : t ∈ outsideNodes Y a h) :
    0 < (a+h*u-t) / (a-t) := by
  have hx := affine_mem_local (a := a) hh hu
  rcases outsideNodes_side ht with hl | hr
  · exact div_pos (by linarith [hx.1]) (by linarith)
  · exact div_pos_of_neg_of_neg (by linarith [hx.2]) (by linarith)

/-- The actual field's first derivative is an exterior-node reciprocal sum. -/
theorem hasDerivAt_finiteField (Y : Finset ℝ) (a h u : ℝ)
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt (finiteField Y a h) (finiteFieldFirst Y a h u) u := by
  have hd : HasDerivAt
      (fun v => ∑ t ∈ outsideNodes Y a h, (Real.log (a+h*v-t) - Real.log (a-t)))
      (∑ t ∈ outsideNodes Y a h, h/(a+h*u-t)) u := by
    apply HasDerivAt.fun_sum
    intro t ht
    simpa only [id_eq, mul_one] using
      (((((hasDerivAt_id u).const_mul h).const_add a).sub_const t).log
        (outside_affine_ne_zero hh hu ht)).sub_const (Real.log (a-t))
  exact hd.neg.div_const _

/-- The second derivative is the nonnegative squared-reciprocal sum. -/
theorem hasDerivAt_finiteFieldFirst (Y : Finset ℝ) (a h u : ℝ)
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) :
    HasDerivAt (finiteFieldFirst Y a h) (finiteFieldSecond Y a h u) u := by
  have hd : HasDerivAt (fun v => ∑ t ∈ outsideNodes Y a h, h/(a+h*v-t))
      (∑ t ∈ outsideNodes Y a h, -(h^2/(a+h*u-t)^2)) u := by
    apply HasDerivAt.fun_sum
    intro t ht
    simpa only [Pi.div_def, id_eq, mul_one, zero_mul, zero_sub, pow_two, neg_div] using
      (hasDerivAt_const u h).div
        ((((hasDerivAt_id u).const_mul h).const_add a).sub_const t)
        (outside_affine_ne_zero hh hu ht)
  change HasDerivAt (fun v : ℝ => finiteFieldFirst Y a h v) (finiteFieldSecond Y a h u) u
  simpa only [finiteFieldFirst, finiteFieldSecond, Pi.neg_def,
    Finset.sum_neg_distrib, neg_neg] using
    hd.neg.div_const ((insideNodes Y a h).card : ℝ)

theorem finiteFieldSecond_nonneg (Y : Finset ℝ) (a h u : ℝ) :
    0 ≤ finiteFieldSecond Y a h u := by
  unfold finiteFieldSecond
  positivity

/-- Convexity follows directly from log-concavity on a source-free interval;
it is not supplied as a property of a hypothetical field. -/
theorem convexOn_finiteField (Y : Finset ℝ) (a h : ℝ) (hh : 0 < h) :
    ConvexOn ℝ (Ioo (-1 : ℝ) 1) (finiteField Y a h) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro u hu v hv lam θ hlam hθ hsum
  have hs : lam * (∑ t ∈ outsideNodes Y a h, (Real.log (a+h*u-t) - Real.log (a-t))) +
      θ * (∑ t ∈ outsideNodes Y a h, (Real.log (a+h*v-t) - Real.log (a-t))) ≤
      ∑ t ∈ outsideNodes Y a h, (Real.log (a+h*(lam*u+θ*v)-t) - Real.log (a-t)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t ht
    have hj := logProfile_gap_jensen (a-h) (a+h) (a+h*u) (a+h*v) t lam θ
      (affine_mem_local hh hu) (affine_mem_local hh hv) (outsideNodes_side ht) hlam hθ hsum
    have he : lam*(a+h*u)+θ*(a+h*v)-t = a+h*(lam*u+θ*v)-t := by
      calc
        _ = (lam+θ)*a+h*(lam*u+θ*v)-t := by ring
        _ = _ := by rw [hsum]; ring
    simp only [logProfile, Real.log_abs, he] at hj
    have hc : lam*Real.log (a-t) + θ*Real.log (a-t) = Real.log (a-t) := by
      rw [← add_mul, hsum, one_mul]
    nlinarith
  have hneg := mul_le_mul_of_nonneg_right (neg_le_neg hs)
    (inv_nonneg.mpr (Nat.cast_nonneg (insideNodes Y a h).card :
      (0 : ℝ) ≤ (insideNodes Y a h).card))
  simp only [smul_eq_mul]
  unfold finiteField
  simp only [div_eq_mul_inv] at hneg ⊢
  convert hneg using 1 <;> ring

noncomputable def outsidePolynomial (Y : Finset ℝ) (a h : ℝ) : ℝ[X] :=
  nodePolynomial (outsideNodes Y a h)

theorem outsidePolynomial_eval_ne_zero (Y : Finset ℝ) (a h u : ℝ)
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) :
    (outsidePolynomial Y a h).eval (a+h*u) ≠ 0 := by
  rw [outsidePolynomial, nodePolynomial_eval]
  exact Finset.prod_ne_zero_iff.mpr (fun t ht => outside_affine_ne_zero hh hu ht)

theorem outsidePolynomial_origin_ne_zero (Y : Finset ℝ) (a h : ℝ) (hh : 0 < h) :
    (outsidePolynomial Y a h).eval a ≠ 0 := by
  simpa only [mul_zero, add_zero] using
    outsidePolynomial_eval_ne_zero Y a h 0 hh (by constructor <;> norm_num)

/-- The sign of every exterior factor is fixed throughout the local interval. -/
theorem outsidePolynomial_ratio_pos (Y : Finset ℝ) (a h u : ℝ)
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) :
    0 < (outsidePolynomial Y a h).eval (a+h*u) / (outsidePolynomial Y a h).eval a := by
  simp only [outsidePolynomial, nodePolynomial_eval]
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_pos (fun t ht => outside_ratio_pos hh hu ht)

/-- Exact, not asymptotic, equality for the genuine row weight. -/
theorem exp_finiteField_eq_weight (Y : Finset ℝ) (a h u : ℝ)
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) (hs : 0 < (insideNodes Y a h).card) :
    Real.exp (-(insideNodes Y a h).card * finiteField Y a h u) =
      (outsidePolynomial Y a h).eval (a+h*u) / (outsidePolynomial Y a h).eval a := by
  have hlog : Real.log ((outsidePolynomial Y a h).eval (a+h*u) /
      (outsidePolynomial Y a h).eval a) =
      ∑ t ∈ outsideNodes Y a h, (Real.log (a+h*u-t) - Real.log (a-t)) := by
    rw [Real.log_div (outsidePolynomial_eval_ne_zero Y a h u hh hu)
      (outsidePolynomial_origin_ne_zero Y a h hh)]
    simp only [outsidePolynomial, nodePolynomial_eval]
    rw [Real.log_prod (fun t ht => outside_affine_ne_zero hh hu ht),
      Real.log_prod (fun t ht => by
        simpa only [mul_zero, add_zero] using
          outside_affine_ne_zero hh (show (0 : ℝ) ∈ Ioo (-1) 1 by constructor <;> norm_num) ht),
      Finset.sum_sub_distrib]
  have hs' : ((insideNodes Y a h).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs)
  have he : -((insideNodes Y a h).card : ℝ) * finiteField Y a h u =
      ∑ t ∈ outsideNodes Y a h, (Real.log (a+h*u-t) - Real.log (a-t)) := by
    unfold finiteField
    field_simp
  rw [he, ← hlog, Real.exp_log (outsidePolynomial_ratio_pos Y a h u hh hu)]

noncomputable def localAffinePolynomial (a h : ℝ) : ℝ[X] :=
  C h⁻¹ * (Polynomial.X - C a)

noncomputable def liftLocalPolynomial (Y : Finset ℝ) (a h : ℝ) (P : ℝ[X]) : ℝ[X] :=
  C ((outsidePolynomial Y a h).eval a)⁻¹ *
    (outsidePolynomial Y a h * P.comp (localAffinePolynomial a h))

theorem localAffinePolynomial_degree (a h : ℝ) :
    (localAffinePolynomial a h).natDegree ≤ 1 :=
  (natDegree_C_mul_le _ _).trans (by simp)

theorem liftLocalPolynomial_degree (Y : Finset ℝ) (a h : ℝ) (P : ℝ[X])
    (hP : P.natDegree < (insideNodes Y a h).card) :
    (liftLocalPolynomial Y a h P).natDegree < Y.card := by
  have hpcomp : (P.comp (localAffinePolynomial a h)).natDegree ≤ P.natDegree := by
    exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ (localAffinePolynomial_degree a h)).trans
      (by simp))
  have hw : (outsidePolynomial Y a h).natDegree = (outsideNodes Y a h).card :=
    nodePolynomial_natDegree _
  have hb := (natDegree_C_mul_le ((outsidePolynomial Y a h).eval a)⁻¹
    (outsidePolynomial Y a h * P.comp (localAffinePolynomial a h))).trans
      (natDegree_mul_le.trans (Nat.add_le_add_left hpcomp _))
  change (liftLocalPolynomial Y a h P).natDegree ≤ _ at hb
  rw [hw] at hb
  have hc := inside_outside_card Y a h
  omega

theorem liftLocalPolynomial_eval (Y : Finset ℝ) (a h u : ℝ) (P : ℝ[X])
    (hh : 0 < h) (hu : u ∈ Ioo (-1) 1) (hs : 0 < (insideNodes Y a h).card) :
    (liftLocalPolynomial Y a h P).eval (a+h*u) =
      Real.exp (-(insideNodes Y a h).card * finiteField Y a h u) * P.eval u := by
  rw [exp_finiteField_eq_weight Y a h u hh hu hs]
  simp only [liftLocalPolynomial, eval_mul, eval_C, eval_comp,
    localAffinePolynomial, eval_sub, eval_X]
  have he : h⁻¹ * (a+h*u-a) = u := by field_simp; ring
  rw [he]
  ring

theorem liftLocalPolynomial_zero_outside (Y : Finset ℝ) (a h t : ℝ) (P : ℝ[X])
    (ht : t ∈ outsideNodes Y a h) : (liftLocalPolynomial Y a h P).eval t = 0 := by
  have hw : (outsidePolynomial Y a h).eval t = 0 := by
    rw [outsidePolynomial, nodePolynomial_eval]
    exact Finset.prod_eq_zero ht (sub_self t)
  simp only [liftLocalPolynomial, eval_mul, eval_C, hw, zero_mul, mul_zero]

end Erdos1152.V4
