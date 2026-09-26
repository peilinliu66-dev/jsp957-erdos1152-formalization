import Erdos1152.V5.Spectrum
import Erdos1152.V5.SinePolynomial

/-! Explicit low/high trigonometric blocks, and the constraint-annihilating
Fejér grid.  These are the actual finite objects in the sampling lower bound. -/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def cosineCharacter (n : ℤ) : CircleFunction :=
  (2:ℂ)⁻¹ • (character n+character (-n))

theorem character_coe (n : ℤ) (t : ℝ) :
    character n (t : FourierCircle)=Complex.exp (((n:ℝ)*t:ℝ)*Complex.I) := by
  simp only [character,fourier_coe_apply]
  congr 1
  push_cast
  field_simp

@[simp] theorem cosineCharacter_coe (n : ℤ) (t : ℝ) :
    cosineCharacter n (t:FourierCircle)=(Real.cos ((n:ℝ)*t):ℂ) := by
  simp only [cosineCharacter,ContinuousMap.smul_apply,ContinuousMap.add_apply,
    smul_eq_mul,character_coe]
  rw [show ((-n : ℤ) : ℝ) * t = -((n : ℝ) * t) by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg,Real.sin_neg,Complex.ofReal_neg]
  ring

noncomputable def probeLow (A d : ℕ) : CircleFunction :=
  ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(A-1-j:ℕ))

noncomputable def probeHigh (A d : ℕ) : CircleFunction :=
  ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(A+1+j:ℕ))

noncomputable def probeNormalization : ℝ := 2*(1+Real.pi)
noncomputable def boundedProbe (A d : ℕ) : CircleFunction :=
  (probeNormalization:ℂ)⁻¹ • (probeLow A d-probeHigh A d)

noncomputable def harmonicHeight (A : ℕ) : ℝ := ∑j∈range A,(1:ℝ)/(j+1:ℕ)

theorem probeNormalization_pos : 0<probeNormalization := by
  unfold probeNormalization; positivity

@[simp] theorem probeLow_zero (A d : ℕ) : probeLow A d 0=(harmonicHeight A:ℂ) := by
  simp [probeLow,cosineCharacter,harmonicHeight,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem harmonicHeight_nonneg (A : ℕ) : 0≤harmonicHeight A := by
  unfold harmonicHeight
  exact sum_nonneg fun _ _ => by positivity

private theorem character_mul_argument (d : ℕ) (n : ℤ) (x : FourierCircle) :
    character ((d:ℤ)*n) x=character n (d•x) := by
  simp only [character,fourier_apply]
  congr 1
  rw [←natCast_zsmul,smul_smul]
  congr 1
  ring

private theorem cosine_mul_argument (d : ℕ) (n : ℤ) (x : FourierCircle) :
    cosineCharacter ((d:ℤ)*n) x=cosineCharacter n (d•x) := by
  simp only [cosineCharacter,ContinuousMap.smul_apply,ContinuousMap.add_apply,smul_eq_mul]
  rw [character_mul_argument,show -((d:ℤ)*n)=(d:ℤ)*(-n) by ring,
    character_mul_argument]

theorem boundedProbe_norm (A d : ℕ) (x : FourierCircle) :
    ‖boundedProbe A d x‖≤1 := by
  let t := AddCircle.equivIco (2*Real.pi) (-Real.pi) (d•x)
  have ht : |(t:ℝ)|≤Real.pi := by
    have ht₁ := t.2.1
    have ht₂ := t.2.2
    rw [abs_le]
    constructor <;> linarith
  have htx : ((t:ℝ):FourierCircle)=d•x :=
    (AddCircle.equivIco (2*Real.pi) (-Real.pi)).symm_apply_apply _
  have hlo : probeLow A d x=(privalovLow A t:ℂ) := by
    simp only [probeLow,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    simp_rw [cosine_mul_argument,←htx,cosineCharacter_coe]
    simp [privalovLow,div_eq_mul_inv,mul_comm]
  have hhi : probeHigh A d x=(privalovHigh A t:ℂ) := by
    simp only [probeHigh,ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul]
    simp_rw [cosine_mul_argument,←htx,cosineCharacter_coe]
    simp [privalovHigh,div_eq_mul_inv,mul_comm]
  simp only [boundedProbe,ContinuousMap.smul_apply,ContinuousMap.sub_apply,
    smul_eq_mul,hlo,hhi,←Complex.ofReal_sub,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos probeNormalization_pos,inv_mul_eq_div,
    div_le_one probeNormalization_pos]
  exact privalov_split_bound A ht

noncomputable def privalovModes (A : ℕ) : Finset ℤ :=
  ((Finset.Icc (-(2*A:ℕ):ℤ) (2*A:ℕ)).erase (-(A:ℤ))).erase (A:ℤ)

theorem mem_privalovModes (A : ℕ) (n : ℤ) :
    n∈privalovModes A ↔ -(2*A:ℕ)≤n ∧ n≤(2*A:ℕ) ∧ n≠-(A:ℤ) ∧ n≠(A:ℤ) := by
  simp only [privalovModes,mem_erase,Finset.mem_Icc]
  tauto

theorem card_privalovModes (A : ℕ) (hA : 0<A) :
    (privalovModes A).card=4*A-1 := by
  unfold privalovModes
  rw [card_erase_of_mem,card_erase_of_mem]
  · simp only [Int.card_Icc]
    omega
  · simp only [Finset.mem_Icc]; constructor <;> omega
  · simp only [mem_erase,Finset.mem_Icc]
    constructor
    · omega
    · constructor <;> omega

private theorem low_modes (A j : ℕ) (hj : j<A) :
    ((A-1-j:ℕ):ℤ)∈privalovModes A ∧ -((A-1-j:ℕ):ℤ)∈privalovModes A := by
  constructor <;> rw [mem_privalovModes] <;> constructor <;> omega

private theorem high_modes (A j : ℕ) (hj : j<A) :
    ((A+1+j:ℕ):ℤ)∈privalovModes A ∧ -((A+1+j:ℕ):ℤ)∈privalovModes A := by
  constructor <;> rw [mem_privalovModes] <;> constructor <;> omega

noncomputable def modulationConstraints (A d m : ℕ)
    (ψ : Fin m → CircleFunction →ₗ[ℂ] ℂ) :
    CircleFunction →ₗ[ℂ] ((↥(privalovModes A)) × Fin m → ℂ) where
  toFun f q := ψ q.2 (character ((d:ℤ)*q.1) * f)
  map_add' f g := by ext q; simp [mul_add]
  map_smul' c f := by ext q; simp [mul_smul_comm]

/-- All extra-node constraints are imposed simultaneously by one genuine finite
polynomial. The number of grid coefficients exceeds the number of equations. -/
theorem exists_privalov_grid (A d m : ℕ) (hA : 0<A) (hm : 0<m)
    (ψ : Fin m → CircleFunction →ₗ[ℂ] ℂ) :
    ∃ Q : CircleFunction, ∃ t₀ : FourierCircle,
      Q∈bandSpace (4*m*A-1) ∧ Q t₀=1 ∧ (∀x,‖Q x‖≤1) ∧
      ∀q∈privalovModes A,∀j,ψ j (character ((d:ℤ)*q)*Q)=0 := by
  let L := 4*m*A
  haveI : NeZero L := ⟨by dsimp [L]; positivity⟩
  have hc : Fintype.card (↥(privalovModes A) × Fin m)<L := by
    rw [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,card_privalovModes A hA]
    dsimp [L]
    have hh : (4*A-1)*m<4*A*m := Nat.mul_lt_mul_of_pos_right (by omega) hm
    nlinarith
  obtain ⟨a,p,hap,han,hΨ,hQn,hQp⟩ := exists_normalized_fejer_annihilator
    L hc (modulationConstraints A d m ψ)
  refine ⟨fejerGridCombination L a,circleGrid L p,fejerGridCombination_band L a,
    hQp,hQn,?_⟩
  intro q hq j
  exact congrFun hΨ (⟨q,hq⟩,j)

private theorem shifted_modulation (v : FourierCircle) (n : ℤ) (Q : CircleFunction) :
    translateCircle v (character n)*Q=character n v • (character n*Q) := by
  rw [translate_character,smul_mul_assoc]

private theorem shifted_cosine (v : FourierCircle) (n : ℤ) (Q : CircleFunction) :
    translateCircle v (cosineCharacter n)*Q =
      (2:ℂ)⁻¹ • (character n v • (character n*Q)+
        character (-n) v • (character (-n)*Q)) := by
  ext x
  simp [translateCircle,cosineCharacter,character_translate]
  ring

/-- Each translated probe is killed by the original functionals, not merely a
new predicate recording that it ought to be killed. -/
theorem privalov_probe_constraints (A d m : ℕ)
    (ψ : Fin m → CircleFunction →ₗ[ℂ] ℂ) (Q : CircleFunction)
    (hQ : ∀q∈privalovModes A,∀j,ψ j (character ((d:ℤ)*q)*Q)=0)
    (v : FourierCircle) (j : Fin m) :
    ψ j (translateCircle v (boundedProbe A d)*Q)=0 := by
  have hp (freq : ℕ→ℕ) (hf : ∀i<A,
      (freq i:ℤ)∈privalovModes A ∧ -(freq i:ℤ)∈privalovModes A) :
      ψ j (translateCircle v (∑i∈range A,((i+1:ℕ):ℂ)⁻¹ •
        cosineCharacter ((d:ℤ)*(freq i:ℤ)))*Q)=0 := by
    have he : translateCircle v (∑i∈range A,((i+1:ℕ):ℂ)⁻¹ •
        cosineCharacter ((d:ℤ)*(freq i:ℤ)))*Q =
        ∑i∈range A,((i+1:ℕ):ℂ)⁻¹ •
          (translateCircle v (cosineCharacter ((d:ℤ)*(freq i:ℤ)))*Q) := by
      ext x; simp [translateCircle,sum_mul,mul_assoc]
    rw [he,map_sum]
    apply sum_eq_zero
    intro i hi
    rw [map_smul,shifted_cosine,map_smul,map_add,map_smul,map_smul]
    have h1 := hQ _ (hf i (mem_range.mp hi)).1 j
    have h2 := hQ _ (hf i (mem_range.mp hi)).2 j
    rw [h1,show -((d:ℤ)*(freq i:ℤ))=(d:ℤ)*(-(freq i:ℤ)) by ring,h2]
    simp
  have hl := hp (fun i => A-1-i) (fun i hi => low_modes A i hi)
  have hh := hp (fun i => A+1+i) (fun i hi => high_modes A i hi)
  change ψ j (translateCircle v (probeLow A d)*Q)=0 at hl
  change ψ j (translateCircle v (probeHigh A d)*Q)=0 at hh
  have he : translateCircle v (boundedProbe A d)*Q =
      (probeNormalization:ℂ)⁻¹ •
        (translateCircle v (probeLow A d)*Q-translateCircle v (probeHigh A d)*Q) := by
    ext x
    simp [translateCircle,boundedProbe]
    ring
  rw [he,map_smul,map_sub,hl,hh,sub_self,smul_zero]

end Erdos1152.V5
