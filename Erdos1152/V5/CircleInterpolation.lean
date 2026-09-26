import Erdos1152.V5.Privalov
import Mathlib.LinearAlgebra.Lagrange

/-! Actual trigonometric interpolation and the finite sampling witness.
The original finite node set is arbitrary; no uniform separation is used. -/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule Polynomial
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

@[simp] theorem character_one_pow (n : ℕ) (x : FourierCircle) :
    character 1 x ^ n=character (n:ℤ) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,ih]
    push_cast
    exact (character_add n 1 x).symm

noncomputable def polynomialCircle (k : ℕ) : ℂ[X]→ₗ[ℂ]CircleFunction where
  toFun p := ⟨fun x => character (-(k:ℤ)) x*p.eval (character 1 x),by fun_prop⟩
  map_add' p q := by ext x; simp [eval_add,mul_add]
  map_smul' c p := by ext x; simp [eval_smul,mul_left_comm]

@[simp] theorem polynomialCircle_apply (k : ℕ) (p : ℂ[X]) (x : FourierCircle) :
    polynomialCircle k p x=character (-(k:ℤ)) x*p.eval (character 1 x) := rfl

@[simp] theorem polynomialCircle_X_pow (k n : ℕ) :
    polynomialCircle k ((Polynomial.X:ℂ[X])^n)=character ((n:ℤ)-k) := by
  ext x
  simp only [polynomialCircle_apply,eval_pow,eval_X,character_one_pow]
  rw [←character_add]
  congr 2
  ring

theorem polynomialCircle_band (k : ℕ) (p : ℂ[X]) (hp : p.natDegree≤2*k) :
    polynomialCircle k p∈bandSpace k := by
  have he : polynomialCircle k p =
      ∑i∈range (p.natDegree+1),p.coeff i•character ((i:ℤ)-k) := by
    ext x
    rw [polynomialCircle_apply,Polynomial.eval_eq_sum_range,mul_sum]
    simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    apply sum_congr rfl
    intro i hi
    rw [character_one_pow,mul_left_comm,←character_add]
    congr 2
    ring
  rw [he]
  apply (bandSpace k).sum_mem
  intro i hi
  apply (bandSpace k).smul_mem
  apply character_mem_spectrum
  have hi := mem_range.mp hi
  simp only [Set.mem_Icc]
  constructor <;> omega

theorem exists_polynomialCircle {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    ∃p : ℂ[X],p.natDegree≤2*k ∧ polynomialCircle k p=f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    change -(k:ℤ) ≤ j ∧ j ≤ k at hj
    refine ⟨(Polynomial.X:ℂ[X])^(j+k).toNat,?_,?_⟩
    · simp only [natDegree_X_pow]
      omega
    · rw [polynomialCircle_X_pow]
      congr 1
      omega
  | zero => exact ⟨0,by simp,by simp⟩
  | add f g hf hg ihf ihg =>
    rcases ihf with ⟨p,hp,he⟩
    rcases ihg with ⟨q,hq,he'⟩
    exact ⟨p+q,(natDegree_add_le _ _).trans (max_le hp hq),by simp [he,he']⟩
  | smul c f hf ih =>
    rcases ih with ⟨p,hp,he⟩
    exact ⟨c•p,(natDegree_smul_le c p).trans hp,by simp [he]⟩

theorem character_one_injective : Function.Injective (fun x:FourierCircle => character 1 x) := by
  intro x y h
  have h' : AddCircle.toCircle x=AddCircle.toCircle y := by
    apply Subtype.ext
    simpa [character,fourier_one] using h
  exact AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0) h'

noncomputable def circleInterpolation (k : ℕ) (T : Finset FourierCircle) :
    CircleFunction→ₗ[ℂ]CircleFunction where
  toFun f := polynomialCircle k (Lagrange.interpolate T (fun x=>character 1 x)
    (fun x=>character k x*f x))
  map_add' f g := by
    have he : (fun x=>character k x*(f+g) x)=
        (fun x=>character k x*f x)+(fun x=>character k x*g x) := by
      ext x; simp [mul_add]
    rw [he,map_add,map_add]
  map_smul' c f := by
    have he : (fun x=>character k x*(c•f) x)=c•(fun x=>character k x*f x) := by
      ext x; simp [mul_left_comm]
    rw [he,map_smul,map_smul]
    rfl

theorem circleInterpolation_range (k : ℕ) (T : Finset FourierCircle)
    (hT : T.card=2*k+1) (f : CircleFunction) :
    circleInterpolation k T f∈bandSpace k := by
  apply polynomialCircle_band
  have h := Lagrange.degree_interpolate_le (s := T)
    (fun x=>character k x*f x) character_one_injective.injOn
  apply Polynomial.natDegree_le_of_degree_le
  simpa [hT] using h

theorem circleInterpolation_at_node (k : ℕ) (T : Finset FourierCircle)
    (f : CircleFunction) (x : FourierCircle) (hx : x∈T) :
    circleInterpolation k T f x=f x := by
  change character (-(k:ℤ)) x*
    (Lagrange.interpolate T (fun x=>character 1 x)
      (fun x=>character k x*f x)).eval (character 1 x)=f x
  rw [Lagrange.eval_interpolate_at_node _ character_one_injective.injOn hx,
    ←mul_assoc,←character_add]
  simp

theorem circleInterpolation_fixes (k : ℕ) (T : Finset FourierCircle)
    (hT : T.card=2*k+1) (f : CircleFunction) (hf : f∈bandSpace k) :
    circleInterpolation k T f=f := by
  obtain ⟨p,hp,rfl⟩ := exists_polynomialCircle hf
  have hv : ∀x,character k x*polynomialCircle k p x=p.eval (character 1 x) := by
    intro x
    rw [polynomialCircle_apply,←mul_assoc,←character_add]
    simp
  change polynomialCircle k (Lagrange.interpolate T (fun x=>character 1 x)
    (fun x=>character k x*polynomialCircle k p x))=polynomialCircle k p
  simp_rw [hv]
  congr 1
  symm
  apply Lagrange.eq_interpolate character_one_injective.injOn
  rw [hT]
  exact (Polynomial.degree_le_of_natDegree_le hp).trans_lt (by exact_mod_cast Nat.lt_succ_self (2*k))

local instance : Infinite FourierCircle := by
  haveI : Infinite (Set.Ico (0:ℝ) (0+2*Real.pi)) := by
    exact (Set.Ico_infinite (by positivity)).to_subtype
  exact Infinite.of_injective _ (AddCircle.equivIco (2*Real.pi) 0).symm.injective

/-- Finite trigonometric sampling lower bound in the exact form needed for
localization. It is now a theorem about every finite node set, not a parameter. -/
theorem finite_trigonometric_sampling_witness (A m : ℕ) (hA : 0<A) (hm : 0<m)
    (Γ : Finset FourierCircle) (hΓ : Γ.card≤2*(8*m*A*A)+m+1) :
    ∃P : CircleFunction,∃z : FourierCircle,
      P∈bandSpace (8*m*A*A) ∧
      (∀x∈Γ,‖P x‖≤1) ∧
      harmonicHeight A/(3*probeNormalization)≤‖P z‖ := by
  classical
  let k := 8*m*A*A
  obtain ⟨S,hΓS,hS⟩ := Infinite.exists_superset_card_eq Γ (2*k+m+1) hΓ
  obtain ⟨T,hTS,hT⟩ := Finset.exists_subset_card_eq
    (show 2*k+1≤S.card by omega)
  have hrest : (S\T).card=m := by
    rw [card_sdiff_of_subset hTS,hS,hT]
    omega
  let e : (↥(S\T))≃Fin m := Fintype.equivFinOfCardEq (by simpa using hrest)
  let U := circleInterpolation k T
  let ψ : Fin m→CircleFunction→ₗ[ℂ]ℂ := fun j =>
    { toFun := fun f => U f (e.symm j)
      map_add' := by intro f g; simp
      map_smul' := by intro c f; simp }
  obtain ⟨g,z,hg,hψ,hgz⟩ := finite_privalov A m hA hm U
    (circleInterpolation_range k T hT) (circleInterpolation_fixes k T hT) ψ
  refine ⟨U g,z,circleInterpolation_range k T hT g,?_,hgz⟩
  intro x hx
  by_cases hxT : x∈T
  · rw [circleInterpolation_at_node k T g x hxT]
    exact hg x
  · have hxrest : x∈S\T := mem_sdiff.mpr ⟨hΓS hx,hxT⟩
    have he := hψ (e ⟨x,hxrest⟩)
    change U g (e.symm (e ⟨x,hxrest⟩))=0 at he
    have hz : U g x=0 := by simpa using he
    simp [hz]

end Erdos1152.V5
