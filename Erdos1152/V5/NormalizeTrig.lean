import Erdos1152.V5.HarmonicBudget

noncomputable section
open scoped BigOperators ComplexConjugate Real
open MeasureTheory Set Finset Submodule
namespace Erdos1152.V5
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable def conjugateCircle (f : CircleFunction) : CircleFunction where
  toFun x := conj (f x)
  continuous_toFun := by fun_prop

private theorem conjugate_character (n : ℤ) :
    conjugateCircle (character n)=character (-n) := by
  ext x
  exact (fourier_neg (n := n)).symm

theorem conjugate_band {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    conjugateCircle f∈bandSpace k := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨n,hn,rfl⟩
    rw [conjugate_character]
    apply character_mem_spectrum
    simp only [Set.mem_Icc] at *
    constructor <;> omega
  | zero =>
    have he : conjugateCircle 0 = (0 : CircleFunction) := by
      ext x
      simp [conjugateCircle]
    rw [he]
    exact (bandSpace k).zero_mem
  | add f g hf hg ihf ihg =>
    have he : conjugateCircle (f+g)=conjugateCircle f+conjugateCircle g := by
      ext x; simp [conjugateCircle]
    rw [he]; exact (bandSpace k).add_mem ihf ihg
  | smul c f hf ih =>
    have he : conjugateCircle (c•f)=conj c•conjugateCircle f := by
      ext x; simp [conjugateCircle]
    rw [he]; exact (bandSpace k).smul_mem _ ih

noncomputable def realPartCircle (f : CircleFunction) : CircleFunction where
  toFun x := ((f x).re:ℂ)
  continuous_toFun := by fun_prop

theorem realPart_band {k : ℕ} {f : CircleFunction} (hf : f∈bandSpace k) :
    realPartCircle f∈bandSpace k := by
  have he : realPartCircle f=(2:ℂ)⁻¹•(f+conjugateCircle f) := by
    ext x
    change ((f x).re : ℂ) = (2 : ℂ)⁻¹ * (f x + conj (f x))
    rw [Complex.add_conj]
    push_cast
    ring
  rw [he]
  exact (bandSpace k).smul_mem _ ((bandSpace k).add_mem hf (conjugate_band hf))

/-- Normalize at an actual maximum, rotate its phase and take its real part.
Both the global bound and all node bounds survive with constants independent
of the positions of the nodes. -/
theorem normalized_real_trig_witness {k : ℕ} (Γ : Finset FourierCircle)
    (M : ℝ) (hM : 0<M) (P : CircleFunction) (hP : P∈bandSpace k)
    (hnodes : ∀x∈Γ,‖P x‖≤1) (z : FourierCircle) (hz : M≤‖P z‖) :
    ∃Q : CircleFunction,∃t₀ : FourierCircle,
      Q∈bandSpace k ∧ Q t₀=(M:ℂ) ∧
      (∀x,(Q x).im=0) ∧ (∀x,‖Q x‖≤M) ∧ (∀x∈Γ,‖Q x‖≤1) := by
  obtain ⟨t₀,ht₀,hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ:Set FourierCircle).Nonempty) P.continuous.norm.continuousOn
  have hP0 : 0<‖P t₀‖ := lt_of_lt_of_le hM (hz.trans (hmax (mem_univ z)))
  let c : ℂ := (M:ℂ)/P t₀
  have hc : ‖c‖=M/‖P t₀‖ := by
    simp [c,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
  have hc1 : ‖c‖≤1 := by
    rw [hc,div_le_one hP0]
    exact hz.trans (hmax (mem_univ z))
  let Q := realPartCircle (c•P)
  have hQP : Q∈bandSpace k := realPart_band ((bandSpace k).smul_mem c hP)
  have hreal (x) : (Q x).im=0 := by simp [Q,realPartCircle]
  have hnorm (x) : ‖Q x‖≤‖c‖*‖P x‖ := by
    change ‖((c*P x).re : ℂ)‖ ≤ ‖c‖*‖P x‖
    rw [Complex.norm_real,Real.norm_eq_abs]
    simpa only [norm_mul] using Complex.abs_re_le_norm (c*P x)
  refine ⟨Q,t₀,hQP,?_,hreal,?_,?_⟩
  · change ((c*P t₀).re : ℂ) = (M : ℂ)
    dsimp only [c]
    rw [div_mul_cancel₀ _ (norm_pos_iff.mp hP0)]
    rfl
  · intro x
    apply (hnorm x).trans
    rw [hc]
    calc
      M/‖P t₀‖*‖P x‖≤M/‖P t₀‖*‖P t₀‖ :=
        mul_le_mul_of_nonneg_left (hmax (mem_univ x)) (by positivity)
      _=M := div_mul_cancel₀ _ hP0.ne'
  · intro x hx
    exact (hnorm x).trans ((mul_le_mul hc1 (hnodes x hx) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul 1))

/-- A uniformly normalized real trigonometric witness for every finite node set
within the explicit finite sampling budget. -/
theorem real_trig_sampling (A q : ℕ) (hA : 0<A) (hq : 0<q)
    (Γ : Finset FourierCircle) (hΓ : Γ.card≤2*localizationRadius A q+1)
    (M : ℝ) (hM : 0<M) (hheight : M≤harmonicHeight A/(3*probeNormalization)) :
    ∃Q : CircleFunction,∃t₀ : FourierCircle,
      Q∈bandSpace (localizationDegree A q) ∧ Q t₀=(M:ℂ) ∧
      (∀x,(Q x).im=0) ∧ (∀x,‖Q x‖≤M) ∧ (∀x∈Γ,‖Q x‖≤1) := by
  obtain ⟨P,z,hP,hPn,hPz⟩ := finite_trigonometric_sampling_witness A (4*q) hA
    (by omega) Γ (by rwa [localization_node_budget] at hΓ)
  have hk : 8*(4*q)*A*A=localizationDegree A q := by unfold localizationDegree; ring
  rw [hk] at hP
  exact normalized_real_trig_witness Γ M hM P hP hPn z (hheight.trans hPz)

end Erdos1152.V5
