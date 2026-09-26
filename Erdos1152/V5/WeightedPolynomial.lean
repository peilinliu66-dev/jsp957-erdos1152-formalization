import Erdos1152.V5.TiltBudget
import Erdos1152.V5.SamplingPacket

noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial
namespace Erdos1152.V5

/-- The polynomial is explicit: finite real Lagrange sum, exact amplitude
 precompensation, one scalar normalization, and a finite binomial tilt. -/
def weightedPacket (F F₁ : ℝ→ℝ) (s m k : ℕ) (y : ℝ) (N : ℕ) (c : ℤ→ℝ) : ℝ[X] :=
  Polynomial.C (Real.exp ((s:ℝ)*F y-(m:ℝ)*externalField y)/meshAmplitude m y)*
    tiltPolynomial y (matchedSlope F₁ s m k y) k *
    ∑j∈symmetricIndices N,
      Polynomial.C (c j*meshAmplitude m (meshNode m (packetIndex m y j))*
        Real.exp ((m:ℝ)*externalField (meshNode m (packetIndex m y j))))*
        meshBasis m (packetIndex m y j)

private theorem amplitude_pos_on_segment (m : ℕ) (u : ℝ) (hu : |u|≤1) :
    0<meshAmplitude m u := by
  have hh := abs_le.mp hu
  have hp : 0≤1+u := by linarith [hh.1]
  have hm : 0≤1-u := by linarith [hh.2]
  unfold meshAmplitude
  exact mul_pos
    (gammaAmplitude_pos _ (div_nonneg (mul_nonneg (Nat.cast_nonneg m) hp) (by norm_num)))
    (gammaAmplitude_pos _ (div_nonneg (mul_nonneg (Nat.cast_nonneg m) hm) (by norm_num)))

private theorem precompensated_mesh_basis (m j : ℕ) (hm : 0<m) (hj : j<m)
    (u : ℝ) (hu : |u|≤1) :
    meshAmplitude m (meshNode m j)*Real.exp ((m:ℝ)*externalField (meshNode m j))*
      (meshBasis m j).eval u =
      meshAmplitude m u*Real.exp ((m:ℝ)*externalField u)*
        cardinalSinc ((m:ℝ)*(u-meshNode m j)/2) := by
  have hA := amplitude_pos_on_segment m (meshNode m j) (meshNode_mem m j hm hj).le
  have he := meshKernel_exact m j hm hj u (abs_le.mp hu)
  have hex : Real.exp ((m:ℝ)*externalField u)*
      Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))=
      Real.exp ((m:ℝ)*externalField (meshNode m j)) := by
    rw [←Real.exp_add]; congr 1; ring
  calc
    _ = Real.exp ((m:ℝ)*externalField u)*
        (meshAmplitude m (meshNode m j)*
          (Real.exp (-(m:ℝ)*(externalField u-externalField (meshNode m j)))*
            (meshBasis m j).eval u)) := by rw [←hex]; ring
    _ = Real.exp ((m:ℝ)*externalField u)*
        (meshAmplitude m (meshNode m j)*
          (cardinalSinc ((m:ℝ)*(u-meshNode m j)/2)*meshAmplitude m u/
            meshAmplitude m (meshNode m j))) := by rw [he]
    _ = _ := by field_simp [hA.ne']

/-- Exact weighted evaluation.  The factors A_m(tau_j) are inside the actual
 polynomial coefficients, so the corrected moments remain the correct ones. -/
theorem weightedPacket_eval
    (F F₁ : ℝ→ℝ) (N s m k : ℕ) (hs : 0<s) (hm : 8*(N+2)≤m)
    (y : ℝ) (hy : |y|≤1/4) (c : ℤ→ℝ) (u : ℝ) (hu : |u|≤1) :
    Real.exp (-(s:ℝ)*F u)*(weightedPacket F F₁ s m k y N c).eval u =
      matchedEnvelope F F₁ s m k y u*meshAmplitude m u/meshAmplitude m y*
        finiteSincSum ((m:ℝ)/(s:ℝ)) (packetPhase m y) N c ((s:ℝ)*(u-y)/2) := by
  have hm0 : 0<m := by omega
  have hsR : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  have hAy := amplitude_pos_on_segment m y (hy.trans (by norm_num))
  have hindices := packetIndex_properties N m s hm hs y hy
  have hterm : ∀j∈symmetricIndices N,
      (c j*meshAmplitude m (meshNode m (packetIndex m y j))*
        Real.exp ((m:ℝ)*externalField (meshNode m (packetIndex m y j))))*
          (meshBasis m (packetIndex m y j)).eval u =
      (meshAmplitude m u*Real.exp ((m:ℝ)*externalField u))*
        (c j*cardinalSinc (((m:ℝ)/(s:ℝ))*
          ((s:ℝ)*(u-y)/2-samplePoint ((m:ℝ)/(s:ℝ)) (packetPhase m y) j))) := by
    intro j hj
    have hb := precompensated_mesh_basis m (packetIndex m y j) hm0 (hindices j hj).1 u hu
    have harg : ((m:ℝ)/(s:ℝ))*((s:ℝ)*(u-y)/2-
        samplePoint ((m:ℝ)/(s:ℝ)) (packetPhase m y) j)=
        (m:ℝ)*(u-meshNode m (packetIndex m y j))/2 := by
      rw [←(hindices j hj).2]
      field_simp [hsR]
      ring
    rw [harg]
    nlinarith [congrArg (fun a:ℝ => c j*a) hb]
  have hsum := Finset.sum_congr rfl hterm
  rw [←Finset.mul_sum] at hsum
  unfold weightedPacket
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_finsetSum,
    tiltPolynomial_eval]
  rw [hsum]
  have hex : Real.exp (-(s:ℝ)*F u)*Real.exp ((s:ℝ)*F y-(m:ℝ)*externalField y)*
      Real.exp ((m:ℝ)*externalField u)=
        Real.exp (-(s:ℝ)*(residualField F s m u-residualField F s m y)) := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    unfold residualField
    field_simp [hsR]
    ring
  calc
    _ = (Real.exp (-(s:ℝ)*F u)*Real.exp ((s:ℝ)*F y-(m:ℝ)*externalField y)*
          Real.exp ((m:ℝ)*externalField u))*
        (1+matchedSlope F₁ s m k y*(u-y))^k*meshAmplitude m u/meshAmplitude m y*
        finiteSincSum ((m:ℝ)/(s:ℝ)) (packetPhase m y) N c ((s:ℝ)*(u-y)/2) := by
          unfold finiteSincSum
          ring
    _ = _ := by rw [hex]; rfl

theorem weightedPacket_degree
    (F F₁ : ℝ→ℝ) (N s m k : ℕ) (hs : 0<s) (hm : 8*(N+2)≤m)
    (y : ℝ) (hy : |y|≤1/4) (c : ℤ→ℝ) :
    (weightedPacket F F₁ s m k y N c).natDegree≤m-1+k := by
  have hm0 : 0<m := by omega
  have hi := packetIndex_properties N m s hm hs y hy
  have hb : ∀j∈symmetricIndices N,(meshBasis m (packetIndex m y j)).natDegree=m-1 := by
    intro j hj
    simpa [meshBasis] using Lagrange.natDegree_basis (meshNode_injective m hm0).injOn
      (Finset.mem_range.mpr (hi j hj).1)
  have hsum : (∑j∈symmetricIndices N,
      Polynomial.C (c j*meshAmplitude m (meshNode m (packetIndex m y j))*
        Real.exp ((m:ℝ)*externalField (meshNode m (packetIndex m y j))))*
        meshBasis m (packetIndex m y j)).natDegree≤m-1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_C_mul_le _ _).trans (le_of_eq (hb j hj))
  unfold weightedPacket
  apply Polynomial.natDegree_mul_le.trans
  have htilt : (Polynomial.C (Real.exp ((s:ℝ)*F y-(m:ℝ)*externalField y)/meshAmplitude m y)*
      tiltPolynomial y (matchedSlope F₁ s m k y) k).natDegree ≤ k :=
    (Polynomial.natDegree_C_mul_le _ _).trans
      (tiltPolynomial_degree y (matchedSlope F₁ s m k y) k)
  omega

/-- A scalar error calculation for the exact packet identity. -/
theorem packet_product_error (E A S g η M : ℝ)
    (hE0 : 0≤E) (hE1 : E≤1) (hE : |E-1|≤η)
    (hA : |A-1|≤η) (hS : |S-g|≤η) (hg : |g|≤M) (hη : 0≤η) :
    |E*A*S-g|≤2*η*(M+η)+η := by
  have hEA : |E*A-1|≤2*η := by
    have he : E*A-1=E*(A-1)+(E-1) := by ring
    rw [he]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg hE0]
    have hh := mul_le_mul_of_nonneg_left hA hE0
    nlinarith
  have hSb : |S|≤M+η := by
    have hh := abs_add_le (S-g) g
    rw [sub_add_cancel] at hh
    linarith
  have he : E*A*S-g=(E*A-1)*S+(S-g) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hprod := mul_le_mul hEA hSb (abs_nonneg S) (by positivity : 0≤2*η)
  linarith

/-- Cubic tails transfer to the actual weighted polynomial on the entire local
 interval; the positive amplitude bounds are global, not only microscopic. -/
theorem weightedPacket_tail
    (F F₁ : ℝ→ℝ) (N s m k : ℕ) (hs : 0<s) (hm : 8*(N+2)≤m)
    (y u : ℝ) (hy : |y|≤1/4) (hu : |u|≤1) (c : ℤ→ℝ)
    (a A K T : ℝ) (ha : 0<a) (hA : 0<A) (hK : 0≤K) (hT : 0<T)
    (hamin : a≤meshAmplitude m y) (hamax : meshAmplitude m u≤A)
    (hE0 : 0≤matchedEnvelope F F₁ s m k y u)
    (hE1 : matchedEnvelope F F₁ s m k y u≤1)
    (htail : ∀ξ:ℝ,2*T≤|ξ|→
      |finiteSincSum ((m:ℝ)/(s:ℝ)) (packetPhase m y) N c ξ|≤K/|ξ|^3)
    (hfar : 2*T≤|(s:ℝ)*(u-y)/2|) :
    |Real.exp (-(s:ℝ)*F u)*(weightedPacket F F₁ s m k y N c).eval u|≤
      (A/a)*K/|(s:ℝ)*(u-y)/2|^3 := by
  rw [weightedPacket_eval F F₁ N s m k hs hm y hy c u hu]
  have hAu := amplitude_pos_on_segment m u hu
  have hAy := amplitude_pos_on_segment m y (hy.trans (by norm_num))
  have hratio : meshAmplitude m u/meshAmplitude m y≤A/a :=
    div_le_div₀ hA.le hamax ha hamin
  rw [abs_mul,abs_div,abs_mul,abs_of_nonneg hE0,abs_of_pos hAu,abs_of_pos hAy]
  have hfirst : matchedEnvelope F F₁ s m k y u*meshAmplitude m u/meshAmplitude m y≤A/a := by
    rw [mul_div_assoc]
    exact (mul_le_of_le_one_left (div_nonneg hAu.le hAy.le) hE1).trans hratio
  have hlast := htail _ hfar
  calc
    _≤(A/a)*(K/|(s:ℝ)*(u-y)/2|^3) :=
      mul_le_mul hfirst hlast (abs_nonneg _) (by positivity)
    _=_ := by ring

end Erdos1152.V5
