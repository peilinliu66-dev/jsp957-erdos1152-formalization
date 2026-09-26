import Erdos1152.V5.LocalCoordinates
import Mathlib.Combinatorics.Pigeonhole

/-!
The first cell adjacent to the left boundary is discarded, so every counted
node is in the *open* central interval used by RowGeometry. Half-open cells
count shared boundaries only once. The loss is bounded by two cells.
-/
noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial MeasureTheory Finset
namespace Erdos1152.V5
open V4

def numberOfBoxes (s ρ : ℕ) : ℕ := s/(8*ρ)-1

def boxLeft (s ρ i : ℕ) : ℝ := -(s:ℝ)/8+2*(ρ:ℝ)*((i:ℝ)+1)
def boxCenter (s ρ i : ℕ) : ℝ := boxLeft s ρ i+ρ
def normalizedCenter (s ρ i : ℕ) : ℝ := 2*boxCenter s ρ i/(s:ℝ)

def goodBoxes (Y : Finset ℝ) (x h : ℝ) (ρ : ℕ) : Finset ℕ :=
  let s := (insideNodes Y x h).card
  (range (numberOfBoxes s ρ)).filter
    (fun i => (countingNodes Y x h (normalizedCenter s ρ i) ρ).card≤2*ρ+1)

theorem box_geometry (s ρ i : ℕ) (hs : 0<s) (hρ : 0<ρ)
    (hi : i<numberOfBoxes s ρ) :
    -(s:ℝ)/8<boxLeft s ρ i ∧ boxLeft s ρ i+2*ρ≤(s:ℝ)/8 ∧
    |normalizedCenter s ρ i|≤1/4 := by
  have hq : i+2≤s/(8*ρ) := by unfold numberOfBoxes at hi; omega
  have hmul := (Nat.mul_le_mul_right (8*ρ) hq).trans (Nat.div_mul_le_self s (8*ρ))
  have hmulR : ((i:ℝ)+2)*(8*(ρ:ℝ))≤s := by exact_mod_cast hmul
  have hρR : 0<(ρ:ℝ) := by exact_mod_cast hρ
  have hsR : 0<(s:ℝ) := by exact_mod_cast hs
  have hlo : -(s:ℝ)/8<boxLeft s ρ i := by
    unfold boxLeft
    nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have hhi : boxLeft s ρ i+2*ρ≤(s:ℝ)/8 := by unfold boxLeft; nlinarith
  refine ⟨hlo,hhi,?_⟩
  apply abs_le.mpr
  unfold normalizedCenter boxCenter
  constructor
  · rw [le_div_iff₀ hsR]; linarith
  · rw [div_le_iff₀ hsR]; linarith

theorem box_micro_membership (s ρ i : ℕ) (x h z : ℝ) (hs : 0<s) :
    microCoordinate s x h (normalizedCenter s ρ i) z∈Ico (-(ρ:ℝ)) ρ ↔
      (s:ℝ)*(z-x)/h/2∈Ico (boxLeft s ρ i) (boxLeft s ρ i+2*ρ) := by
  have hsR : (s:ℝ)≠0 := by exact_mod_cast hs.ne'
  have he : microCoordinate s x h (normalizedCenter s ρ i) z=
      (s:ℝ)*(z-x)/h/2-boxCenter s ρ i := by
    unfold microCoordinate normalizedCenter
    field_simp
  rw [he]
  unfold boxCenter
  constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith

theorem countingNodes_central_subset (Y : Finset ℝ) (x h : ℝ) (ρ i : ℕ)
    (hh : 0<h) (hs : 0<(insideNodes Y x h).card) (hρ : 0<ρ)
    (hi : i<numberOfBoxes (insideNodes Y x h).card ρ) :
    countingNodes Y x h (normalizedCenter (insideNodes Y x h).card ρ i) ρ ⊆
      insideNodes Y x (h/4) := by
  intro z hz
  have hzY := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1
  have hzbox := (box_micro_membership (insideNodes Y x h).card ρ i x h z hs).mp
    (Finset.mem_filter.mp hz).2
  have hg := box_geometry (insideNodes Y x h).card ρ i hs hρ hi
  have hsR : 0<((insideNodes Y x h).card:ℝ) := by exact_mod_cast hs
  have hzlo : -((insideNodes Y x h).card:ℝ)/8<
      ((insideNodes Y x h).card:ℝ)*(z-x)/h/2 := hg.1.trans_le hzbox.1
  have hzhi := hzbox.2.trans_le hg.2.1
  have hp : 0<((insideNodes Y x h).card:ℝ)/h := div_pos hsR hh
  refine Finset.mem_filter.mpr ⟨hzY,?_⟩
  constructor
  · have hx : -(h/4)<z-x := by
      have hclear := (lt_div_iff₀ hh).mp (show -((insideNodes Y x h).card:ℝ)/4<
        ((insideNodes Y x h).card:ℝ)*(z-x)/h by linarith)
      nlinarith
    linarith
  · have hx : z-x<h/4 := by
      have hclear := (div_lt_iff₀ hh).mp (show ((insideNodes Y x h).card:ℝ)*(z-x)/h<
        ((insideNodes Y x h).card:ℝ)/4 by linarith)
      nlinarith
    linarith

theorem countingNodes_disjoint (Y : Finset ℝ) (x h : ℝ) (ρ : ℕ)
    (hs : 0<(insideNodes Y x h).card) (hρ : 0<ρ) (i j : ℕ) (hij : i≠j) :
    Disjoint (countingNodes Y x h (normalizedCenter (insideNodes Y x h).card ρ i) ρ)
      (countingNodes Y x h (normalizedCenter (insideNodes Y x h).card ρ j) ρ) := by
  apply Finset.disjoint_left.mpr
  intro z hzi hzj
  have hi := (box_micro_membership (insideNodes Y x h).card ρ i x h z hs).mp (mem_filter.mp hzi).2
  have hj := (box_micro_membership (insideNodes Y x h).card ρ j x h z hs).mp (mem_filter.mp hzj).2
  have hρR : 0<(ρ:ℝ) := by exact_mod_cast hρ
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hijR : (i:ℝ)+1≤j := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have he : boxLeft (insideNodes Y x h).card ρ i+2*ρ≤boxLeft (insideNodes Y x h).card ρ j := by
      unfold boxLeft; nlinarith
    linarith [hi.2,hj.1]
  · have hjiR : (j:ℝ)+1 ≤ i := by exact_mod_cast (Nat.succ_le_iff.mpr hji)
    have he : boxLeft (insideNodes Y x h).card ρ j+2*ρ≤boxLeft (insideNodes Y x h).card ρ i := by
      unfold boxLeft; nlinarith
    linarith [hj.2,hi.1]

/-- Actual finite bad-box counting, with an explicit additive rounding loss. -/
theorem goodBoxes_card_lower (Y : Finset ℝ) (x h : ℝ) (ρ : ℕ)
    (hh : 0<h) (hs : 0<(insideNodes Y x h).card) (hρ : 0<ρ)
    (hcentral : ((insideNodes Y x (h/4)).card:ℝ)≤
      (1/4+1/(16*(ρ:ℝ)))*(insideNodes Y x h).card) :
    3*((insideNodes Y x h).card:ℝ)/(32*ρ*(ρ+1))-2≤(goodBoxes Y x h ρ).card := by
  let s := (insideNodes Y x h).card
  let I := range (numberOfBoxes s ρ)
  let bad := I.filter (fun i => 2*ρ+1<(countingNodes Y x h (normalizedCenter s ρ i) ρ).card)
  let C := fun i => countingNodes Y x h (normalizedCenter s ρ i) ρ
  have hdisj : (bad:Set ℕ).PairwiseDisjoint C := by
    intro i hi j hj hij
    exact countingNodes_disjoint Y x h ρ hs hρ i j hij
  have hsub : bad.biUnion C⊆insideNodes Y x (h/4) := by
    intro z hz
    obtain ⟨i,hi,hzi⟩ := mem_biUnion.mp hz
    exact countingNodes_central_subset Y x h ρ i hh hs hρ
      (mem_range.mp (mem_filter.mp hi).1) hzi
  have hsum : (∑i∈bad,(C i).card)≤(insideNodes Y x (h/4)).card := by
    rw [←Finset.card_biUnion hdisj]
    exact card_le_card hsub
  have hbad : (2*ρ+2)*bad.card≤(insideNodes Y x (h/4)).card := by
    have hc := Finset.sum_le_sum (s:=bad) (fun i hi =>
      show 2*ρ+2≤(C i).card from Nat.succ_le_iff.mpr (mem_filter.mp hi).2)
    simp only [sum_const,nsmul_eq_mul] at hc
    calc
      _ ≤ ∑ i ∈ bad, (C i).card := by simpa [Nat.mul_comm] using hc
      _ ≤ _ := hsum
  have hpartition : (goodBoxes Y x h ρ).card+bad.card=numberOfBoxes s ρ := by
    have he : I.filter (fun i => ¬ (C i).card≤2*ρ+1)=bad := by ext i; simp [bad,C]
    simpa [goodBoxes,s,I,he] using card_filter_add_card_filter_not (s:=I) (p:=fun i => (C i).card≤2*ρ+1)
  have hj : (s:ℝ)/(8*ρ)-2≤numberOfBoxes s ρ := by
    have hρN : 0<8*ρ := by omega
    have hdiv : s<(s/(8*ρ)+1)*(8*ρ) := by
      simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ s hρN
    have hcast : (s:ℝ)<((s/(8*ρ):ℕ):ℝ)*(8*ρ)+8*ρ := by
      have hcast' : (s:ℝ)<(((s/(8*ρ):ℕ):ℝ)+1)*(8*(ρ:ℝ)) := by
        exact_mod_cast hdiv
      nlinarith
    have hq : s/(8*ρ)≤numberOfBoxes s ρ+1 := by dsimp [numberOfBoxes]; omega
    have hqR : ((s/(8*ρ):ℕ):ℝ)≤(numberOfBoxes s ρ:ℝ)+1 := by exact_mod_cast hq
    have hρR : 0<(ρ:ℝ) := by exact_mod_cast hρ
    have he : (s:ℝ)/(8*ρ)≤(numberOfBoxes s ρ:ℝ)+2 := by
      rw [div_le_iff₀ (by positivity : 0<8*(ρ:ℝ))]
      nlinarith
    linarith
  have hbadR : (2*(ρ:ℝ)+2)*bad.card≤(insideNodes Y x (h/4)).card := by exact_mod_cast hbad
  have hpartitionR : ((goodBoxes Y x h ρ).card:ℝ)+bad.card=numberOfBoxes s ρ := by exact_mod_cast hpartition
  have hρR : 0<(ρ:ℝ) := by exact_mod_cast hρ
  have he : (s:ℝ)/(8*ρ)-(1/4+1/(16*(ρ:ℝ)))*s/(2*ρ+2)=
      3*(s:ℝ)/(32*ρ*(ρ+1)) := by field_simp; ring
  rw [←he]
  have hbadbound := (le_div_iff₀' (by positivity : 0<2*(ρ:ℝ)+2)).mpr
    (hbadR.trans hcentral)
  linarith

/-- Pigeonhole thinning in a fixed residue class. There is no averaging over
unknown sparse-box counts: the dense good boxes have already been counted. -/
theorem exists_large_residue_class (G : Finset ℕ) (q : ℕ) (hq : 0<q) :
    ∃j<q,((G.card:ℝ)/(q:ℝ))≤(G.filter (fun i => i%q=j)).card := by
  have hcard : (range q).card • ((G.card:ℝ)/(q:ℝ))≤(G.card:ℝ) := by
    simp only [card_range,nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hq.ne' : (q:ℝ)≠0)]
  obtain ⟨j,hj,hjcard⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s:=G) (t:=range q) (f:=fun i => i%q) (b:=(G.card:ℝ)/(q:ℝ))
    (fun i hi => mem_range.mpr (Nat.mod_lt i hq))
    (nonempty_range_iff.mpr hq.ne') hcard
  exact ⟨j,mem_range.mp hj,hjcard⟩

end Erdos1152.V5
