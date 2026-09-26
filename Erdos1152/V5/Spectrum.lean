import Erdos1152.V5.FejerFilter
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- Finite trigonometric spectrum, as a genuine subspace of circle functions. -/
noncomputable def spectrumSpace (s : Set ℤ) : Submodule ℂ CircleFunction :=
  Submodule.span ℂ (character '' s)

noncomputable def bandSpace (k : ℕ) : Submodule ℂ CircleFunction :=
  spectrumSpace (Set.Icc (-(k:ℤ)) k)

theorem character_mem_spectrum {s : Set ℤ} {j : ℤ} (hj : j∈s) :
    character j∈spectrumSpace s := subset_span ⟨j,hj,rfl⟩

theorem spectrum_mono {s t : Set ℤ} (hst : s⊆t) : spectrumSpace s≤spectrumSpace t :=
  span_mono (image_mono hst)

theorem spectrum_mul {s t u : Set ℤ} (hsum : ∀j∈s,∀k∈t,j+k∈u)
    {f g : CircleFunction} (hf : f∈spectrumSpace s) (hg : g∈spectrumSpace t) :
    f*g∈spectrumSpace u := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    induction hg using Submodule.span_induction with
    | mem g hg =>
      rcases hg with ⟨k,hk,rfl⟩
      have he : character j*character k=character (j+k) := by
        ext x; exact (character_add j k x).symm
      rw [he]
      exact character_mem_spectrum (hsum j hj k hk)
    | zero => simp
    | add f g hf hg ihf ihg =>
      simpa [mul_add] using (spectrumSpace u).add_mem ihf ihg
    | smul c f hf ih =>
      simpa [mul_smul_comm] using (spectrumSpace u).smul_mem c ih
  | zero => simp
  | add f g hf hg ihf ihg =>
    simpa [add_mul] using (spectrumSpace u).add_mem ihf ihg
  | smul c f hf ih =>
    simpa [smul_mul_assoc] using (spectrumSpace u).smul_mem c ih

theorem band_mul {k l : ℕ} {f g : CircleFunction}
    (hf : f∈bandSpace k) (hg : g∈bandSpace l) : f*g∈bandSpace (k+l) := by
  apply spectrum_mul (s := Set.Icc (-(k:ℤ)) k) (t := Set.Icc (-(l:ℤ)) l) _ hf hg
  intro j hj n hn
  simp only [Set.mem_Icc] at *
  constructor <;> omega

noncomputable def translateCircle (v : FourierCircle) (f : CircleFunction) : CircleFunction where
  toFun x := f (x+v)
  continuous_toFun := by fun_prop

noncomputable def reflectCircle (v : FourierCircle) (f : CircleFunction) : CircleFunction where
  toFun x := f (v-x)
  continuous_toFun := by fun_prop

theorem translate_character (v : FourierCircle) (j : ℤ) :
    translateCircle v (character j) = character j v • character j := by
  ext x
  simp [translateCircle,character_translate,mul_comm]

theorem reflect_character (v : FourierCircle) (j : ℤ) :
    reflectCircle v (character j) = character j v • character (-j) := by
  ext x
  simp [reflectCircle,character_sub]

theorem translate_spectrum (v : FourierCircle) {s : Set ℤ} {f : CircleFunction}
    (hf : f∈spectrumSpace s) : translateCircle v f∈spectrumSpace s := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    rw [translate_character]
    exact (spectrumSpace s).smul_mem _ (character_mem_spectrum hj)
  | zero =>
    change (0 : CircleFunction) ∈ spectrumSpace s
    exact (spectrumSpace s).zero_mem
  | add f g hf hg ihf ihg =>
    have he : translateCircle v (f+g)=translateCircle v f+translateCircle v g := by ext; rfl
    rw [he]; exact (spectrumSpace s).add_mem ihf ihg
  | smul c f hf ih =>
    have he : translateCircle v (c•f)=c•translateCircle v f := by ext; rfl
    rw [he]; exact (spectrumSpace s).smul_mem _ ih

theorem reflect_band (v : FourierCircle) {k : ℕ} {f : CircleFunction}
    (hf : f∈bandSpace k) : reflectCircle v f∈bandSpace k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    rw [reflect_character]
    apply (bandSpace k).smul_mem
    exact character_mem_spectrum (by simp only [Set.mem_Icc] at *; constructor <;> omega)
  | zero =>
    change (0 : CircleFunction) ∈ bandSpace k
    exact (bandSpace k).zero_mem
  | add f g hf hg ihf ihg =>
    have he : reflectCircle v (f+g)=reflectCircle v f+reflectCircle v g := by ext; rfl
    rw [he]; exact (bandSpace k).add_mem ihf ihg
  | smul c f hf ih =>
    have he : reflectCircle v (c•f)=c•reflectCircle v f := by ext; rfl
    rw [he]; exact (bandSpace k).smul_mem _ ih

theorem convolution_add_right (K f g : CircleFunction) (x : FourierCircle) :
    circleConvolution K (f+g) x =circleConvolution K f x+circleConvolution K g x := by
  unfold circleConvolution
  simp only [ContinuousMap.add_apply,mul_add]
  rw [integral_add]
  all_goals
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _

theorem convolution_smul_right (K f : CircleFunction) (c : ℂ)
    (x : FourierCircle) : circleConvolution K (c•f) x=c*circleConvolution K f x := by
  unfold circleConvolution
  simp only [ContinuousMap.smul_apply,smul_eq_mul,mul_left_comm (K _),integral_const_mul]

theorem convolution_sub_right (K f g : CircleFunction) (x : FourierCircle) :
    circleConvolution K (f-g) x =circleConvolution K f x-circleConvolution K g x := by
  unfold circleConvolution
  simp only [ContinuousMap.sub_apply,mul_sub]
  rw [integral_sub]
  all_goals
    apply Continuous.integrable_of_hasCompactSupport
    · fun_prop
    · exact HasCompactSupport.of_compactSpace _

theorem vallee_fixes_band (L : ℕ) [NeZero L] {f : CircleFunction}
    (hf : f∈bandSpace L) : ∀x,circleConvolution (valleeKernel L) f x=f x := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    intro x
    exact vallee_low_character L j (by
      have : |j|≤(L:ℤ) := abs_le.mpr hj
      exact Int.ofNat_le.mp (by simpa only [Int.natCast_natAbs] using this)) x
  | zero => simp [circleConvolution]
  | add f g hf hg ihf ihg =>
    intro x
    rw [convolution_add_right,ihf,ihg,ContinuousMap.add_apply]
  | smul c f hf ih =>
    intro x
    rw [convolution_smul_right,ih]
    rfl

theorem vallee_kills_high (L : ℕ) {f : CircleFunction}
    (hf : f∈spectrumSpace {j : ℤ | 2*L≤j.natAbs}) :
    ∀x,circleConvolution (valleeKernel L) f x=0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨j,hj,rfl⟩
    exact vallee_high_character L j hj
  | zero => simp [circleConvolution]
  | add f g hf hg ihf ihg =>
    intro x
    rw [convolution_add_right,ihf,ihg,add_zero]
  | smul c f hf ih =>
    intro x
    rw [convolution_smul_right,ih,mul_zero]

/-- Recover a finite coefficient list rather than assuming a Fourier expansion. -/
theorem band_expansion {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    ∃c : ℤ→ℂ,f=finiteFourier (Finset.Icc (-(k:ℤ)) k) c := by
  have hs : (Set.Icc (-(k:ℤ)) k)=(Finset.Icc (-(k:ℤ)) k : Set ℤ) := by ext; simp
  rw [bandSpace,spectrumSpace,hs,Submodule.mem_span_image_finset_iff_exists_fun'] at hf
  obtain ⟨c,hc⟩ := hf
  exact ⟨c,hc.symm⟩

theorem fejerGridWeight_band (L : ℕ) [NeZero L] (q : ZMod L) :
    (⟨fun x => (fejerGridWeight L q x : ℂ),by fun_prop⟩ : CircleFunction)
      ∈bandSpace (L-1) := by
  have he : (⟨fun x => (fejerGridWeight L q x : ℂ),by fun_prop⟩ : CircleFunction) =
      (1/(L:ℂ)^2) •
        ∑i:Fin L,∑j:Fin L,translateCircle (-circleGrid L q)
          (character ((i:ℤ)-(j:ℤ))) := by
    ext x
    simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,smul_eq_mul]
    change ((‖oneSidedDirichlet L (x-circleGrid L q)‖^2 / (L : ℝ)^2 : ℝ) : ℂ) =
      (1/(L:ℂ)^2) * ∑ i : Fin L, ∑ j : Fin L,
        character ((i:ℤ)-(j:ℤ)) (x + -circleGrid L q)
    simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,
      normSq_dirichlet_expansion,sub_eq_add_neg]
    ring
  rw [he]
  apply (bandSpace (L-1)).smul_mem
  apply (bandSpace (L-1)).sum_mem
  intro i hi
  apply (bandSpace (L-1)).sum_mem
  intro j hj
  apply translate_spectrum
  apply character_mem_spectrum
  have hi := i.isLt
  have hj := j.isLt
  simp only [Set.mem_Icc]
  constructor <;> omega

theorem fejerGridCombination_band (L : ℕ) [NeZero L] (a : ZMod L→ℂ) :
    fejerGridCombination L a∈bandSpace (L-1) := by
  have he : fejerGridCombination L a =
      ∑q:ZMod L,a q•(⟨fun x => (fejerGridWeight L q x:ℂ),by fun_prop⟩ : CircleFunction) := by
    ext x; simp [fejerGridCombination]
  rw [he]
  exact (bandSpace (L-1)).sum_mem fun q hq =>
    (bandSpace (L-1)).smul_mem _ (fejerGridWeight_band L q)

end Erdos1152.V5
