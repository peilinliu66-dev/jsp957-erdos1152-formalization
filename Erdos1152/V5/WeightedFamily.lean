import Erdos1152.V5.SelectedCenters
import Erdos1152.V5.AssemblePeaks
import Erdos1152.V5.LocalWeightedPeak

/-!
# Actual finite weighted peak family

The only analytic premise concerns the actual finite row external field.
Every peak polynomial, interval, sign, root-free property and total-length
budget is constructed. RowGeometry supplies this field premise in Main.
-/
noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial MeasureTheory Finset
namespace Erdos1152.V5
open V4

/-- Constants depend only on H. The local original node count is denoted by s;
it is not a subsequence index and no minimum node separation is assumed. -/
theorem actual_weighted_family (H : ℝ) (hH : 1<H) :
    ∃ρ:ℕ,∃b δ a₀ ℓ₀:ℝ,∃s₀:ℕ,
      0<ρ ∧ 0<b ∧ b<1 ∧ 0<δ ∧ 0<a₀ ∧ 0<ℓ₀ ∧
      ∀Y:Finset ℝ,∀x h:ℝ,0<h→s₀≤(insideNodes Y x h).card→
      (((insideNodes Y x (h/4)).card:ℝ)≤
        (1/4+1/(16*(ρ:ℝ)))*(insideNodes Y x h).card)→
      (∀j:Fin 3,∀u∈Icc (-b) b,|finiteFieldJet j Y x h u-modelJet j u|≤δ)→
      ∃K:ℕ,∃F:ℝ[X],∃α β:Fin K→ℝ,
        0<K ∧ a₀*(insideNodes Y x h).card≤(K:ℝ) ∧
        F.natDegree<Y.card ∧ (∀z∈Y,|F.eval z|≤1) ∧
        (∀i,α i<β i) ∧ (∀i j,i<j→β i≤α j) ∧
        (∀i,Ioo (α i) (β i)⊆Ioo (x-h) (x+h)) ∧
        (∀i,β i-α i=2*h*ℓ₀/((insideNodes Y x h).card:ℝ)) ∧
        (∀i,∀z∈Ioo (α i) (β i),(nodePolynomial Y).eval z≠0) ∧
        (∀i,∀z∈Ioo (α i) (β i),H < |F.eval z|) ∧
        (∀i,∀z∈Ioo (α i) (β i),0<(-1:ℝ)^i.val*(F.eval z/(nodePolynomial Y).eval z)) := by
  let B := 8*(H+1)
  have hB : 1<B := by dsimp [B]; linarith
  obtain ⟨ρ,b,δ,ℓ,T,D,n₀,hρ,hb0,hb1,hδ,hℓ,hT,hD,hlocal⟩ := local_weighted_peak_exists B hB
  obtain ⟨q,hq,hqT,hqρ,hcross⟩ := exists_packet_stride ρ hρ T D hT hD
  let a₀ := 3/(64*(ρ:ℝ)*(ρ+1)*q)
  have ha₀ : 0<a₀ := by dsimp [a₀]; positivity
  have hρR : 0<(ρ:ℝ) := by exact_mod_cast hρ
  have hqR : 0<(q:ℝ) := by exact_mod_cast hq
  obtain ⟨n₁,hn₁⟩ := exists_nat_gt (max (8*(ρ:ℝ)) (max (1/a₀) (128*(ρ:ℝ)*(ρ+1)/3)))
  let s₀ := max (max 1 n₀) n₁
  refine ⟨ρ,b,δ,a₀,ℓ,s₀,hρ,hb0,hb1,hδ,ha₀,hℓ,?_⟩
  intro Y x h hh hs₀ hcentral hfield
  let s := (insideNodes Y x h).card
  have hs : 0<s := by dsimp [s₀,s] at *; omega
  have hsR : 0<(s:ℝ) := by exact_mod_cast hs
  have hn₀ : n₀≤s := by dsimp [s₀,s] at *; omega
  have hn₁s : (n₁:ℝ)≤s := by exact_mod_cast (show n₁≤s by dsimp [s₀,s] at *; omega)
  have hsρ : 8*(ρ:ℝ)≤s := by have := (le_max_left _ _).trans_lt hn₁; linarith
  have hsa : 1<a₀*(s:ℝ) := by
    have hn := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hn₁
    have hns : 1/a₀<(s:ℝ) := hn.trans_le hn₁s
    simpa only [mul_comm] using (div_lt_iff₀ ha₀).mp hns
  have hsG : 2≤3*(s:ℝ)/(64*(ρ:ℝ)*(ρ+1)) := by
    have hn := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hn₁
    have hns : 128*(ρ:ℝ)*(ρ+1)/3<(s:ℝ) := hn.trans_le hn₁s
    rw [le_div_iff₀ (by positivity : 0<64*(ρ:ℝ)*(ρ+1))]
    linarith
  let G := goodBoxes Y x h ρ
  have hGbound : 3*(s:ℝ)/(64*(ρ:ℝ)*(ρ+1))≤(G.card:ℝ) := by
    have he := goodBoxes_card_lower Y x h ρ hh hs hρ hcentral
    change 3*(s:ℝ)/(32*ρ*(ρ+1))-2≤(G.card:ℝ) at he
    have hh : 3*(s:ℝ)/(32*ρ*(ρ+1))=2*(3*(s:ℝ)/(64*ρ*(ρ+1))) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hh] at he
    linarith
  obtain ⟨r,hrq,hr⟩ := exists_large_residue_class G q hq
  let J := G.filter (fun i => i%q=r)
  let K := J.card
  have hKbound : a₀*(s:ℝ)≤(K:ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hGbound hqR.le
    have he : (3*(s:ℝ)/(64*(ρ:ℝ)*(ρ+1)))/(q:ℝ)=a₀*(s:ℝ) := by
      dsimp [a₀]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he] at hdiv
    exact hdiv.trans hr
  have hK : 0<K := by
    have : (0:ℝ)<K := (by linarith : 0<a₀*(s:ℝ)).trans_le hKbound
    exact_mod_cast this
  let e : Fin K→ℕ := J.orderEmbOfFin rfl
  have hemem (i : Fin K) : e i∈J := J.orderEmbOfFin_mem rfl i
  have hemono : StrictMono e := (J.orderEmbOfFin rfl).strictMono
  have hegood (i : Fin K) : e i∈G := (mem_filter.mp (hemem i)).1
  have hemod (i j : Fin K) : e i%q=e j%q := by
    exact (mem_filter.mp (hemem i)).2.trans (mem_filter.mp (hemem j)).2.symm
  have heindex (i : Fin K) : e i<numberOfBoxes s ρ :=
    mem_range.mp (mem_filter.mp (hegood i)).1
  let c := fun i => boxCenter s ρ (e i)
  have hc (i : Fin K) : |2*c i/(s:ℝ)|≤1/4 :=
    (box_geometry s ρ (e i) hs hρ (heindex i)).2.2
  have hgood (i : Fin K) : (countingNodes Y x h (2*c i/(s:ℝ)) ρ).card≤2*ρ+1 :=
    (mem_filter.mp (hegood i)).2
  have hdata (i : Fin K) := hlocal Y x h (2*c i/(s:ℝ)) hh (hc i) hn₀ hfield (hgood i)
  choose P a b' hdeg hnode hab hlen hbox hpeak htail hzero using hdata
  have hcsep := selected_centers s ρ q K hρ hq e hemono hemod
  let L := 2*(ρ:ℝ)*q
  have hL : 0<L := by dsimp [L]; positivity
  have htail' (i : Fin K) (z : ℝ) (hz : z∈Ioo (x-h) (x+h))
      (hfar : 2*T≤|(s:ℝ)*(z-x)/(2*h)-c i|) :
      |(P i).eval z|≤D/|(s:ℝ)*(z-x)/(2*h)-c i|^3 := by
    have he : microCoordinate s x h (2*c i/(s:ℝ)) z=(s:ℝ)*(z-x)/(2*h)-c i := by
      unfold microCoordinate
      field_simp
    have ht := htail i z hz
    -- Normalize both the premise and conclusion before applying the tail bound.
    rw [he] at ht
    exact ht hfar
  have hpeak' (i : Fin K) (ξ : ℝ) (hξ : ξ∈Icc (a i) (b' i)) :
      8*(H+1)-1≤(P i).eval (x+2*h*(c i+ξ)/(s:ℝ)) := by
    have hp := hpeak i ξ hξ
    have he : x+h*(2*c i/(s:ℝ)+2*ξ/(s:ℝ))=x+2*h*(c i+ξ)/(s:ℝ) := by ring
    change 8*(H+1)-1 ≤ (P i).eval
      (x+h*(2*c i/(s:ℝ)+2*ξ/(s:ℝ))) at hp
    rwa [he] at hp
  have hzero' (i : Fin K) (z : ℝ) (hz : z∈Y) (hzout : z∉Ioo (x-h) (x+h)) : (P i).eval z=0 := by
    apply hzero i z
    apply Finset.mem_sdiff.mpr
    refine ⟨hz,?_⟩
    intro hi
    exact hzout (mem_filter.mp hi).2
  obtain ⟨F,α,β,hFdeg,hFnode,hαβ,horder,hinside,hlength,hnroot,hFpeak,hFsign⟩ :=
    assemble_packet_family Y x h s K hh hs hK H ρ ℓ T D L (by linarith)
      hρR hℓ hT hD.le hL hqT hqρ hcross hsρ c P a b' hc hcsep.1 hcsep.2
      hdeg hnode hab hlen hbox hpeak' htail' hzero'
  exact ⟨K,F,α,β,hK,hKbound,hFdeg,hFnode,hαβ,horder,hinside,hlength,hnroot,hFpeak,hFsign⟩

end Erdos1152.V5
