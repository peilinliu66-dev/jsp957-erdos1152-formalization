import Erdos1152.V5.PrivalovProbe

/-!
Finite Privalov lower bound, with explicit integer parameters.  The theorem is
about an arbitrary projection onto a specified finite trigonometric space and
actual extra linear functionals.  Its conclusion constructs the bounded input;
no sampling lower bound, Bernstein existence theorem or analytic axiom occurs
among its parameters.  Later interpolation specializes the projection.
-/
noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def operatorOrbit (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ : FourierCircle) (n : ℤ) : CircleFunction :=
  translateCircle (-t₀) (character n) * reflectCircle t₀ (U (character n*Q))

theorem operatorOrbit_apply (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ τ : FourierCircle) (n : ℤ) :
    operatorOrbit U Q t₀ n τ =
      U (translateCircle (τ-t₀) (character n)*Q) (t₀-τ) := by
  rw [translate_character,smul_mul_assoc,map_smul U]
  change character n (τ + -t₀) * U (character n*Q) (t₀-τ) =
    character n (τ-t₀) * U (character n*Q) (t₀-τ)
  simp only [sub_eq_add_neg]

theorem operatorOrbit_low (U : CircleFunction→ₗ[ℂ]CircleFunction) (k l : ℕ)
    (hfix : ∀f∈bandSpace k,U f=f) (Q : CircleFunction) (hQ : Q∈bandSpace l)
    (t₀ : FourierCircle) (n : ℤ) (hn : n.natAbs+l≤k) :
    operatorOrbit U Q t₀ n=reflectCircle t₀ Q := by
  have hchar : character n∈bandSpace n.natAbs := by
    apply character_mem_spectrum
    change -(n.natAbs:ℤ)≤n ∧ n≤(n.natAbs:ℤ)
    simpa using abs_le.mp (le_refl |n|)
  have hprod : character n*Q∈bandSpace k := by
    apply spectrum_mono (s := Set.Icc (-(n.natAbs+l:ℕ):ℤ) (n.natAbs+l:ℕ))
      (t := Set.Icc (-(k:ℤ)) k) _ (band_mul hchar hQ)
    intro j hj
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  unfold operatorOrbit
  rw [hfix _ hprod]
  ext τ
  change character n (τ + -t₀) * (character n (t₀-τ) * Q (t₀-τ)) = Q (t₀-τ)
  rw [←mul_assoc,←character_translate]
  simp [sub_eq_add_neg,add_assoc]

theorem operatorOrbit_high (U : CircleFunction→ₗ[ℂ]CircleFunction) (k L : ℕ)
    (hrange : ∀f,U f∈bandSpace k) (Q : CircleFunction)
    (t₀ : FourierCircle) (n : ℤ) (hn : k+2*L≤n.natAbs) :
    operatorOrbit U Q t₀ n∈spectrumSpace {j:ℤ|2*L≤j.natAbs} := by
  unfold operatorOrbit
  apply spectrum_mul (s := {n}) (t := Set.Icc (-(k:ℤ)) k)
  · intro i hi j hj
    have hin : i=n := mem_singleton_iff.mp hi
    subst i
    have hjb : j.natAbs≤k := by
      exact Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using abs_le.mpr hj)
    have htri : n.natAbs≤(n+j).natAbs+j.natAbs := by
      have hh := Int.natAbs_add_le (n+j) (-j)
      simpa using hh
    change 2*L≤(n+j).natAbs
    omega
  · exact translate_spectrum _ (character_mem_spectrum (mem_singleton n))
  · exact reflect_band t₀ (hrange _)

noncomputable def orbitBlock (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ : FourierCircle) (A d : ℕ) (freq : ℕ→ℕ) : CircleFunction :=
  ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ •
    ((2:ℂ)⁻¹ • (operatorOrbit U Q t₀ ((d:ℤ)*(freq j:ℤ))+
      operatorOrbit U Q t₀ (-((d:ℤ)*(freq j:ℤ)))))

noncomputable def boundedProbeOrbit (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ : FourierCircle) (A d : ℕ) : CircleFunction :=
  (probeNormalization:ℂ)⁻¹ •
    (orbitBlock U Q t₀ A d (fun j => A-1-j)-
      orbitBlock U Q t₀ A d (fun j => A+1+j))

theorem orbitBlock_apply (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ τ : FourierCircle) (A d : ℕ) (freq : ℕ→ℕ) :
    orbitBlock U Q t₀ A d freq τ =
      U (translateCircle (τ-t₀) (∑j∈range A,
        ((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(freq j:ℤ)))*Q) (t₀-τ) := by
  have he : translateCircle (τ-t₀) (∑j∈range A,
      ((j+1:ℕ):ℂ)⁻¹ • cosineCharacter ((d:ℤ)*(freq j:ℤ)))*Q =
      ∑j∈range A,((j+1:ℕ):ℂ)⁻¹ •
        ((2:ℂ)⁻¹ •
          (translateCircle (τ-t₀) (character ((d:ℤ)*(freq j:ℤ)))*Q+
           translateCircle (τ-t₀) (character (-((d:ℤ)*(freq j:ℤ))))*Q)) := by
    ext x
    simp [translateCircle,cosineCharacter,sum_mul,mul_add,add_mul,mul_assoc]
  rw [he,map_sum]
  simp only [orbitBlock,ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.add_apply,map_smul,map_add,smul_eq_mul,operatorOrbit_apply]

theorem boundedProbeOrbit_apply (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (Q : CircleFunction) (t₀ τ : FourierCircle) (A d : ℕ) :
    boundedProbeOrbit U Q t₀ A d τ =
      U (translateCircle (τ-t₀) (boundedProbe A d)*Q) (t₀-τ) := by
  have he : translateCircle (τ-t₀) (boundedProbe A d)*Q =
      (probeNormalization:ℂ)⁻¹ •
        (translateCircle (τ-t₀) (probeLow A d)*Q-
         translateCircle (τ-t₀) (probeHigh A d)*Q) := by
    ext x; simp [translateCircle,boundedProbe]; ring
  rw [he,map_smul U,map_sub U]
  simp only [boundedProbeOrbit,ContinuousMap.smul_apply,ContinuousMap.sub_apply,
    smul_eq_mul,orbitBlock_apply,probeLow,probeHigh]

private theorem orbitBlock_low (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (A d L k : ℕ) (hfix : ∀f∈bandSpace k,U f=f)
    (Q : CircleFunction) (hQ : Q∈bandSpace (L-1)) (t₀ : FourierCircle)
    (hbudget : (A-1)*d+(L-1)≤k) :
    orbitBlock U Q t₀ A d (fun j => A-1-j)=
      (harmonicHeight A:ℂ) • reflectCircle t₀ Q := by
  have hc (j : ℕ) (hj : j<A) :
      (((d:ℤ)*(A-1-j:ℕ)):ℤ).natAbs+(L-1)≤k := by
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have := Nat.mul_le_mul_left d (show A-1-j≤A-1 by omega)
    nlinarith
  unfold orbitBlock
  apply ContinuousMap.ext
  intro τ
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,
    ContinuousMap.add_apply,smul_eq_mul]
  have hs (j : ℕ) (hj : j∈range A) :
      ((j+1:ℕ):ℂ)⁻¹*((2:ℂ)⁻¹*
        (operatorOrbit U Q t₀ ((d:ℤ)*(A-1-j:ℕ)) τ+
         operatorOrbit U Q t₀ (-((d:ℤ)*(A-1-j:ℕ))) τ)) =
      ((j+1:ℕ):ℂ)⁻¹*reflectCircle t₀ Q τ := by
    rw [operatorOrbit_low U k (L-1) hfix Q hQ t₀ _ (hc j (mem_range.mp hj)),
      operatorOrbit_low U k (L-1) hfix Q hQ t₀ _ (by simpa using hc j (mem_range.mp hj))]
    ring
  rw [sum_congr rfl hs,←sum_mul]
  simp [harmonicHeight,div_eq_mul_inv]

private theorem orbitBlock_high (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (A d L k : ℕ) (hrange : ∀f,U f∈bandSpace k)
    (Q : CircleFunction) (t₀ : FourierCircle) (hbudget : k+2*L≤(A+1)*d) :
    orbitBlock U Q t₀ A d (fun j => A+1+j)∈
      spectrumSpace {n:ℤ|2*L≤n.natAbs} := by
  unfold orbitBlock
  apply (spectrumSpace _).sum_mem
  intro j hj
  apply (spectrumSpace _).smul_mem
  apply (spectrumSpace _).smul_mem
  apply (spectrumSpace _).add_mem
  · apply operatorOrbit_high U k L hrange
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    nlinarith [Nat.mul_le_mul_left d (show A+1≤A+1+j by omega)]
  · apply operatorOrbit_high U k L hrange
    simp only [Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast]
    nlinarith [Nat.mul_le_mul_left d (show A+1≤A+1+j by omega)]

/-- A finite-dimensional Privalov theorem with explicit parameters
`L=4mA`, `d=2L`, `k=Ad`.  The logarithmic growth is supplied by `harmonicHeight A`.
The input is produced by the Fejér grid, not postulated as a sampling witness. -/
theorem finite_privalov (A m : ℕ) (hA : 0<A) (hm : 0<m)
    (U : CircleFunction→ₗ[ℂ]CircleFunction)
    (hrange : ∀f,U f∈bandSpace (8*m*A*A))
    (hfix : ∀f∈bandSpace (8*m*A*A),U f=f)
    (ψ : Fin m→CircleFunction→ₗ[ℂ]ℂ) :
    ∃g : CircleFunction,∃z : FourierCircle,
      (∀x,‖g x‖≤1) ∧ (∀j,ψ j g=0) ∧
      harmonicHeight A/(3*probeNormalization)≤‖U g z‖ := by
  let L := 4*m*A
  let d := 2*L
  let k := 8*m*A*A
  haveI : NeZero L := ⟨by dsimp [L]; positivity⟩
  obtain ⟨Q,t₀,hQband,hQ0,hQnorm,hQψ⟩ := exists_privalov_grid A d m hA hm ψ
  let G := boundedProbeOrbit U Q t₀ A d
  have hlow : orbitBlock U Q t₀ A d (fun j => A-1-j)=
      (harmonicHeight A:ℂ) • reflectCircle t₀ Q := by
    apply orbitBlock_low U A d L k hfix Q hQband t₀
    dsimp [d,L,k]
    have hsub : A-1+1=A := by omega
    nlinarith [Nat.sub_le (4*m*A) 1]
  have hhigh : orbitBlock U Q t₀ A d (fun j => A+1+j)∈
      spectrumSpace {n:ℤ|2*L≤n.natAbs} := by
    apply orbitBlock_high U A d L k hrange
    dsimp [d,L,k]
    nlinarith
  have hreflect : reflectCircle t₀ Q∈bandSpace L := by
    apply spectrum_mono _ (reflect_band t₀ hQband)
    intro n hn
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  have hfilter : circleConvolution (valleeKernel L) G 0 =
      (harmonicHeight A/(probeNormalization):ℝ) := by
    change circleConvolution (valleeKernel L)
      ((probeNormalization:ℂ)⁻¹ •
        (orbitBlock U Q t₀ A d (fun j => A-1-j)-
         orbitBlock U Q t₀ A d (fun j => A+1+j))) 0 = _
    rw [convolution_smul_right,convolution_sub_right,hlow,
      convolution_smul_right,vallee_fixes_band L hreflect,
      vallee_kills_high L hhigh]
    simp [reflectCircle,hQ0,div_eq_mul_inv,mul_comm]
  obtain ⟨τ,hτ,hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ: Set FourierCircle).Nonempty) G.continuous.norm.continuousOn
  have hnorm : harmonicHeight A/probeNormalization≤3*‖G τ‖ := by
    have hb := norm_convolution_le (valleeKernel L) G ‖G τ‖
      (fun y => hmax (mem_univ y)) 0
    rw [hfilter,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (harmonicHeight_nonneg A) probeNormalization_pos.le)] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (integral_norm_valleeKernel_le L) (norm_nonneg _))
  let g := translateCircle (τ-t₀) (boundedProbe A d)*Q
  refine ⟨g,t₀-τ,?_,?_,?_⟩
  · intro x
    change ‖boundedProbe A d (x+(τ-t₀))*Q x‖≤1
    rw [norm_mul]
    exact (mul_le_mul (boundedProbe_norm A d _) (hQnorm x)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · intro j
    exact privalov_probe_constraints A d m ψ Q hQψ (τ-t₀) j
  · have he : G τ=U g (t₀-τ) := boundedProbeOrbit_apply U Q t₀ τ A d
    rw [←he]
    rw [div_le_iff₀ (mul_pos (by norm_num) probeNormalization_pos)]
    have hh := (div_le_iff₀ probeNormalization_pos).mp hnorm
    nlinarith

end Erdos1152.V5
