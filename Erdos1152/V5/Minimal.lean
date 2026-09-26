import Erdos1152.V5.RowGeometry
import Erdos1152.V5.WeightedFamily
import Erdos1152.V4.Main

/-!
# The original minimal-region predicate

H selects the constants. The almost-everywhere point and requested upper
scale select h. Only after h is fixed is the finite assigned-node set S
introduced. The actual original row is selected after S, and the resulting
finite data force the conclusion for every admissible interpolation polynomial.
-/
noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial MeasureTheory Finset
namespace Erdos1152.V5
open V4

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

/-- Construct the original hm. There is no field, sampling, packet, peak-family,
local-amplification or equivalent analytic hypothesis in the parameters. -/
theorem localAmplificationMinimal_canonical (X : NodeArray) (r : ℕ→ℕ)
    (hr : Tendsto (fun n => (r n:ℝ)/(n+1:ℝ)) atTop (𝓝 0)) :
    LocalAmplificationMinimal X r (canonicalHighRegion X) := by
  intro H hH
  obtain ⟨ρ,b,δ,a,ℓ,s₀,hρ,hb0,hb1,hδ,ha,hℓ,hfamily⟩ := actual_weighted_family H hH
  let c := min (1/2:ℝ) (a*ℓ/8)
  have hc : 0<c := lt_min (by norm_num) (by positivity)
  have hc1 : c≤1 := (min_le_left _ _).trans (by norm_num)
  have hcA : c≤a*ℓ/8 := min_le_right _ _
  refine ⟨c,hc,hc1,?_⟩
  filter_upwards [ae_minimum_choose_field_scale X r hr ρ hρ b δ hb0 hb1 hδ] with x hx
  intro hnot ε hε
  obtain ⟨h,hh,hεh,hleft,hright,hm,hrows⟩ := hx hnot ε hε
  refine ⟨h,hh,hεh,?_⟩
  intro S N₀
  obtain ⟨hgeo,hsinf,hexcess⟩ := hrows S
  let s := fun j => (insideNodes (unassignedNodes X S (canonicalRows X j)) x h).card
  let d := fun j => r (canonicalRows X j)+S.card
  have hsmall : Tendsto (fun j => ((d j:ℝ)+1)/(s j:ℝ)) atTop (𝓝 0) := by
    have hone := (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp hsinf
    have hhlim := hexcess.add hone
    convert hhlim using 1
    · ext j
      dsimp [d,s]
      push_cast
      ring
    · ring
  have hlater : ∀ᶠj in atTop,N₀≤canonicalRows X j :=
    (canonicalRows_tendsto X).eventually_ge_atTop N₀
  have hlenough : ∀ᶠj in atTop,s₀≤s j := hsinf.eventually_ge_atTop s₀
  have hdsmall : ∀ᶠj in atTop,((d j:ℝ)+1)/(s j:ℝ)<a/2 :=
    hsmall.eventually_lt_const (half_pos ha)
  obtain ⟨j,hjgeo,hjrow,hjs,hjd⟩ := (hgeo.and (hlater.and (hlenough.and hdsmall))).exists
  let n := canonicalRows X j
  let Y := unassignedNodes X S n
  have hspos : 0<(insideNodes Y x h).card := hjgeo.1
  have hsR : 0<((insideNodes Y x h).card:ℝ) := by exact_mod_cast hspos
  have hfield : ∀q:Fin 3,∀u∈Icc (-b) b,|finiteFieldJet q Y x h u-modelJet q u|≤δ :=
    fun q u hu => (hjgeo.2.2 q u hu).le
  obtain ⟨K,F,α,β,hK,hKa,hFdeg,hFnode,hαβ,horder,hinside,hlength,hnode,hpeak,hsign⟩ :=
    hfamily Y x h hh hjs hjgeo.2.1 hfield
  let v : Segment→ℝ := fun z => F.eval (z:ℝ)
  refine ⟨n,hjrow,v,?_,?_⟩
  · intro i hi
    apply hFnode
    exact (mem_unassignedNodes X S n _).mpr ⟨i,hi,rfl⟩
  · intro p hp hvalues
    have hbudgetDegree : p.natDegree≤Y.card+d j := by
      have hcard := unassignedNodes_card X S n
      dsimp [Y,d,n] at *
      omega
    have hvaluesY : ∀z∈Y,p.eval z=F.eval z := by
      intro z hz
      obtain ⟨i,hi,rfl⟩ := (mem_unassignedNodes X S n z).mp hz
      exact hvalues i hi
    have hFbudget : F.natDegree≤Y.card+d j := by omega
    let w := 2*h*ℓ/((insideNodes Y x h).card:ℝ)
    have hw : 0<w := by dsimp [w]; positivity
    have hd : (d j:ℝ)+1≤a*((insideNodes Y x h).card:ℝ)/2 := by
      have ht := (div_lt_iff₀ hsR).mp hjd
      nlinarith
    have hKgap : a*((insideNodes Y x h).card:ℝ)/2≤(K:ℝ)-d j-1 := by linarith
    have htotal : 2*c*((x+h)-(x-h))≤((K:ℝ)-d j-1)*w := by
      have hm := mul_le_mul_of_nonneg_right hKgap hw.le
      have he : (a*((insideNodes Y x h).card:ℝ)/2)*w=a*h*ℓ := by dsimp [w]; field_simp
      rw [he] at hm
      have hcMul := mul_le_mul_of_nonneg_right hcA (by positivity : 0≤4*h)
      nlinarith
    exact low_measure_of_fin_family Y F K (d j) α β (x-h) (x+h) H w c
      (by linarith) hw.le hFbudget hαβ horder hinside
      (fun i => (hlength i).ge) hnode hpeak hsign htotal p hbudgetDegree hvaluesY

end Erdos1152.V5
