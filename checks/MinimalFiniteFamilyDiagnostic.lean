import Erdos1152.V3.AlternatingMeasure

/-! Diagnostic only: finite-family transfer lemma, not Minimal or Main verification. -/
noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial MeasureTheory Finset
namespace Erdos1152.V5

/-- The finite-index interval family is fed to the existing root-count module;
this is not a substitute for constructing the family in WeightedFamily. -/
theorem low_measure_of_fin_family
    (Y : Finset ℝ) (F : ℝ[X]) (K d : ℕ) (a b : Fin K→ℝ)
    (α β H ℓ c : ℝ) (hαβ : α<β) (hℓ : 0≤ℓ)
    (hF : F.natDegree≤Y.card+d)
    (hab : ∀i,a i<b i) (horder : ∀i j,i<j→b i≤a j)
    (hinside : ∀i,Ioo (a i) (b i)⊆Ioo α β)
    (hlen : ∀i,ℓ≤b i-a i)
    (hnode : ∀i,∀z∈Ioo (a i) (b i),(nodePolynomial Y).eval z≠0)
    (hpeak : ∀i,∀z∈Ioo (a i) (b i),H < |F.eval z|)
    (hsign : ∀i,∀z∈Ioo (a i) (b i),0<(-1:ℝ)^i.val*(F.eval z/(nodePolynomial Y).eval z))
    (hbudget : 2*c*(β-α)≤((K:ℝ)-d-1)*ℓ) :
    ∀p:ℝ[X],p.natDegree≤Y.card+d→(∀z∈Y,p.eval z=F.eval z)→
      volume.real ({z | |p.eval z|≤H}∩Ioo α β)≤(1-c)*volume.real (Ioo α β) := by
  let a' := fun i:ℕ => if hi:i<K then a ⟨i,hi⟩ else 0
  let b' := fun i:ℕ => if hi:i<K then b ⟨i,hi⟩ else 0
  apply V3.low_measure_of_alternating_polynomial Y F K d a' b' α β H ℓ c hαβ hℓ hF
  · intro i hi
    simpa [a',b',hi] using hab ⟨i,hi⟩
  · intro i hi j hj hij
    simpa [a',b',hi,hj] using horder ⟨i,hi⟩ ⟨j,hj⟩ hij
  · intro i hi
    simpa [a',b',hi] using hinside ⟨i,hi⟩
  · intro i hi
    simpa [a',b',hi] using hlen ⟨i,hi⟩
  · intro i hi
    simpa [a',b',hi] using hnode ⟨i,hi⟩
  · intro i hi
    simpa [a',b',hi] using hpeak ⟨i,hi⟩
  · intro i hi
    simpa [a',b',hi] using hsign ⟨i,hi⟩
  · exact hbudget

end Erdos1152.V5

#print axioms Erdos1152.V5.low_measure_of_fin_family
