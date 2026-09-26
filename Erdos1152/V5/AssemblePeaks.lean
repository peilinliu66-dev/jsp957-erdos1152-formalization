import Erdos1152.V5.CrossTails
import Erdos1152.V3.AlternatingMeasure

/-!
The sum polynomial and its signs are constructed. Root-free intervals follow
from the one-packet node bound and peak height; they are not presumed to be
root-free as an extra condition on the original nodes.
-/
noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial MeasureTheory Finset
namespace Erdos1152.V5

private theorem same_sign_on_interval (q : ℝ[X]) (a b u v : ℝ)
    (hu : u∈Ioo a b) (hv : v∈Ioo a b)
    (hn : ∀z∈Ioo a b,q.eval z≠0) : 0<q.eval u*q.eval v := by
  by_contra h
  have hle : q.eval u*q.eval v≤0 := le_of_not_gt h
  have hne : q.eval u*q.eval v≠0 := mul_ne_zero (hn u hu) (hn v hv)
  have hneg : q.eval u*q.eval v<0 := lt_of_le_of_ne hle hne
  rcases lt_trichotomy u v with huv | rfl | hvu
  · obtain ⟨z,hz,hqz⟩ := exists_root_between q huv hneg
    exact hn z ⟨hu.1.trans hz.1,hz.2.trans hv.2⟩ hqz
  · nlinarith [sq_nonneg (q.eval u)]
  · obtain ⟨z,hz,hqz⟩ := exists_root_between q hvu (by simpa [mul_comm] using hneg)
    exact hn z ⟨hv.1.trans hz.1,hz.2.trans hu.2⟩ hqz

def intervalOrientation (q : ℝ[X]) (a b : ℝ) : ℝ :=
  if 0<q.eval ((a+b)/2) then 1 else -1

theorem intervalOrientation_abs (q : ℝ[X]) (a b : ℝ) : |intervalOrientation q a b|=1 := by
  unfold intervalOrientation
  split_ifs <;> norm_num

theorem intervalOrientation_pos (q : ℝ[X]) (a b : ℝ) (hab : a<b)
    (hn : ∀z∈Ioo a b,q.eval z≠0) :
    ∀z∈Ioo a b,0 < intervalOrientation q a b*q.eval z := by
  intro z hz
  have hmid : (a+b)/2∈Ioo a b := by constructor <;> linarith
  have hs := same_sign_on_interval q a b ((a+b)/2) z hmid hz hn
  unfold intervalOrientation
  split_ifs with hp
  · simp only [one_mul]
    exact pos_of_mul_pos_right hs hp.le
  · have hm : q.eval ((a+b)/2)<0 := lt_of_le_of_ne (le_of_not_gt hp) (hn _ hmid)
    simp only [neg_one_mul,neg_pos]
    exact neg_of_mul_pos_right hs hm.le

/-- A finite assembly theorem whose inputs are genuine local packet
polynomials. The caller below constructs every one of these inputs. -/
theorem assemble_packet_family
    (Y : Finset ℝ) (x h : ℝ) (s K : ℕ) (hh : 0<h) (hs : 0<s) (hK : 0<K)
    (H ρ ℓ T D L : ℝ) (hH : 0≤H) (hρ : 0<ρ) (hℓ : 0<ℓ) (hT : 0<T)
    (hD : 0≤D) (hL : 0<L) (hLT : 4*T≤L) (hLρ : 4*ρ≤L)
    (hcross : 32*D/L^3≤1/4) (hsize : 8*ρ≤(s:ℝ))
    (c : Fin K→ℝ) (P : Fin K→ℝ[X]) (a b : Fin K→ℝ)
    (hc : ∀i,|2*c i/(s:ℝ)|≤1/4)
    (hcmono : StrictMono c)
    (hsep : ∀i j,L*|(i.val:ℝ)-(j.val:ℝ)|≤|c i-c j|)
    (hdeg : ∀i,(P i).natDegree<Y.card)
    (hnode : ∀i,∀z∈Y,|(P i).eval z|≤3/2)
    (hab : ∀i,a i<b i)
    (hlen : ∀i,b i-a i=ℓ)
    (hbox : ∀i,Icc (a i) (b i)⊆Icc (-ρ) ρ)
    (hpeak : ∀i,∀ξ∈Icc (a i) (b i),8*(H+1)-1≤(P i).eval (x+2*h*(c i+ξ)/(s:ℝ)))
    (htail : ∀i,∀z∈Ioo (x-h) (x+h),2*T≤|(s:ℝ)*(z-x)/(2*h)-c i|→
      |(P i).eval z|≤D/|(s:ℝ)*(z-x)/(2*h)-c i|^3)
    (hzero : ∀i,∀z∈Y,z∉Ioo (x-h) (x+h)→(P i).eval z=0) :
    ∃F:ℝ[X],∃α β:Fin K→ℝ,
      F.natDegree<Y.card ∧ (∀z∈Y,|F.eval z|≤1) ∧
      (∀i,α i<β i) ∧
      (∀i j,i<j→β i≤α j) ∧
      (∀i,Ioo (α i) (β i)⊆Ioo (x-h) (x+h)) ∧
      (∀i,β i-α i=2*h*ℓ/(s:ℝ)) ∧
      (∀i,∀z∈Ioo (α i) (β i),(nodePolynomial Y).eval z≠0) ∧
      (∀i,∀z∈Ioo (α i) (β i),H < |F.eval z|) ∧
      (∀i,∀z∈Ioo (α i) (β i),0<(-1:ℝ)^i.val*(F.eval z/(nodePolynomial Y).eval z)) := by
  have hsR : 0<(s:ℝ) := by exact_mod_cast hs
  let α := fun i => x+2*h*(c i+a i)/(s:ℝ)
  let β := fun i => x+2*h*(c i+b i)/(s:ℝ)
  let Z := fun z:ℝ => (s:ℝ)*(z-x)/(2*h)
  have hzinv (z : ℝ) : x+2*h*Z z/(s:ℝ)=z := by dsimp [Z]; field_simp; ring
  have hαβ (i : Fin K) : α i<β i := by dsimp [α,β]; gcongr; exact hab i
  have hcoord (i : Fin K) (z : ℝ) (hz : z∈Ioo (α i) (β i)) : Z z-c i∈Ioo (a i) (b i) := by
    have hz0 := (lt_div_iff₀ hsR).mp (show z-x<2*h*(c i+b i)/(s:ℝ) by dsimp [β] at hz; linarith [hz.2])
    have hz1 := (div_lt_iff₀ hsR).mp (show 2*h*(c i+a i)/(s:ℝ)<z-x by dsimp [α] at hz; linarith [hz.1])
    dsimp [Z]
    constructor
    · rw [lt_sub_iff_add_lt,lt_div_iff₀ (by positivity : 0<2*h)]; nlinarith
    · rw [sub_lt_iff_lt_add,div_lt_iff₀ (by positivity : 0<2*h)]; nlinarith
  have hinside (i : Fin K) : Ioo (α i) (β i)⊆Ioo (x-h) (x+h) := by
    intro z hz
    have hξ := hcoord i z hz
    have hbnd := hbox i (Ioo_subset_Icc_self hξ)
    have hc' := abs_le.mp (hc i)
    have hcL := (le_div_iff₀ hsR).mp hc'.1
    have hcU := (div_le_iff₀ hsR).mp hc'.2
    have hzR : -(s:ℝ)/2<Z z ∧ Z z<(s:ℝ)/2 := by constructor <;> linarith [hbnd.1,hbnd.2]
    dsimp [Z] at hzR
    have h0 := (lt_div_iff₀ (by positivity : 0<2*h)).mp hzR.1
    have h1 := (div_lt_iff₀ (by positivity : 0<2*h)).mp hzR.2
    constructor <;> nlinarith
  have hordered (i j : Fin K) (hij : i<j) : β i≤α j := by
    have hidx := fin_index_distance_ge_one (ne_of_lt hij)
    have hdist := hsep i j
    rw [abs_of_neg (sub_neg.mpr (hcmono hij))] at hdist
    have ha := hbox j ⟨le_rfl,(hab j).le⟩
    have hb := hbox i ⟨(hab i).le,le_rfl⟩
    have hg : c i+b i≤c j+a j := by nlinarith [ha.1, hb.2]
    dsimp [α,β]
    gcongr
  have hlength (i : Fin K) : β i-α i=2*h*ℓ/(s:ℝ) := by
    dsimp [α,β]
    rw [show x+2*h*(c i+b i)/(s:ℝ)-(x+2*h*(c i+a i)/(s:ℝ))=
      2*h*(b i-a i)/(s:ℝ) by ring,hlen i]
  have hown (i : Fin K) (z : ℝ) (hz : z∈Ioo (α i) (β i)) :
      8*(H+1)-1≤(P i).eval z := by
    have he := hpeak i (Z z-c i) (Ioo_subset_Icc_self (hcoord i z hz))
    have heq : x+2*h*(c i+(Z z-c i))/(s:ℝ)=z := by simpa using hzinv z
    rwa [heq] at he
  have hnroot (i : Fin K) (z : ℝ) (hz : z∈Ioo (α i) (β i)) :
      (nodePolynomial Y).eval z≠0 := by
    have hzY : z∉Y := by
      intro hy
      have hb := (abs_le.mp (hnode i z hy)).2
      have hp := hown i z hz
      linarith
    rw [nodePolynomial_eval]
    exact Finset.prod_ne_zero_iff.mpr (fun t ht hzt => hzY (sub_eq_zero.mp hzt ▸ ht))
  let σ := fun i => intervalOrientation (nodePolynomial Y) (α i) (β i)
  let ε := fun i => (-1:ℝ)^i.val*σ i
  let F : ℝ[X] := Polynomial.C (1/2:ℝ)*∑i:Fin K,Polynomial.C (ε i)*P i
  have hσabs (i : Fin K) : |σ i|=1 := intervalOrientation_abs _ _ _
  have hεabs (i : Fin K) : |ε i|=1 := by dsimp [ε]; simp [abs_mul,abs_pow,hσabs]
  have hεsq (i : Fin K) : (ε i)^2=1 := by nlinarith [sq_abs (ε i),hεabs i]
  have hFeval (z : ℝ) : F.eval z=(1/2:ℝ)*∑i:Fin K,ε i*(P i).eval z := by
    simp [F,Polynomial.eval_finsetSum]
  let f := fun i z => (P i).eval (x+2*h*z/(s:ℝ))
  have hcrossz (i : Fin K) (z : ℝ) (hz : z∈Ioo (x-h) (x+h))
      (hnear : ∀j,|Z z-c i|≤|Z z-c j|) :
      (∑j∈(univ:Finset (Fin K)).erase i,|(P j).eval z|)≤1/4 := by
    have hh := cubic_cross_sum c f L T D hL hT hD hLT hsep i (Z z)
      (fun j hj => by simpa [f,hzinv] using htail j z hz hj) hnear
    simpa [f,hzinv] using hh.trans hcross
  have hnodesum (z : ℝ) (hz : z∈Y) : (∑i:Fin K,|(P i).eval z|)≤2 := by
    by_cases hzI : z∈Ioo (x-h) (x+h)
    · obtain ⟨i,hi⟩ := exists_nearest_center hK c (Z z)
      rw [←sum_erase_add _ _ (mem_univ i)]
      linarith [hcrossz i z hzI hi,hnode i z hz]
    · simp [hzero _ z hz hzI]
  have hdominant (i : Fin K) (z : ℝ) (hz : z∈Ioo (α i) (β i)) : H<ε i*F.eval z := by
    have hξ : |Z z-c i|≤ρ := abs_le.mpr (hbox i (Ioo_subset_Icc_self (hcoord i z hz)))
    have hnear := own_center_nearest c L ρ hρ.le (by linarith) hsep i (Z z) hξ
    have hcros := hcrossz i z (hinside i hz) hnear
    have hothers : |∑j∈(univ:Finset (Fin K)).erase i,ε i*ε j*(P j).eval z|≤1/4 := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      simpa [abs_mul,hεabs] using hcros
    rw [hFeval,←sum_erase_add _ _ (mem_univ i)]
    have he : ε i*((1/2:ℝ)*((∑j∈(univ:Finset (Fin K)).erase i,ε j*(P j).eval z)+ε i*(P i).eval z))=
        (1/2:ℝ)*((P i).eval z+∑j∈(univ:Finset (Fin K)).erase i,ε i*ε j*(P j).eval z) := by
      have hsum : (∑j∈(univ:Finset (Fin K)).erase i,ε i*ε j*(P j).eval z)=
          ε i*(∑j∈(univ:Finset (Fin K)).erase i,ε j*(P j).eval z) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hsum]
      calc
        _ = (1/2:ℝ)*((ε i)^2*(P i).eval z+
            ε i*(∑j∈(univ:Finset (Fin K)).erase i,ε j*(P j).eval z)) := by ring
        _ = _ := by rw [hεsq i,one_mul]
    rw [he]
    have heLow := (abs_le.mp hothers).1
    linarith [hown i z hz]
  refine ⟨F,α,β,?_,?_,hαβ,hordered,hinside,hlength,hnroot,?_,?_⟩
  · have hY : 0<Y.card := lt_of_le_of_lt (Nat.zero_le _) (hdeg ⟨0,hK⟩)
    apply lt_of_le_of_lt (Polynomial.natDegree_C_mul_le _ _) ?_
    apply lt_of_le_of_lt (b := Y.card-1) ?_ (Nat.sub_lt hY (by decide : 0 < 1))
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    exact (Polynomial.natDegree_C_mul_le _ _).trans (Nat.le_pred_of_lt (hdeg i))
  · intro z hz
    rw [hFeval,abs_mul]
    norm_num
    have hb := Finset.abs_sum_le_sum_abs (fun i:Fin K => ε i*(P i).eval z) univ
    simp only [abs_mul,hεabs,one_mul] at hb
    linarith [hnodesum z hz]
  · intro i z hz
    have hd := hdominant i z hz
    have hbound : ε i*F.eval z≤|F.eval z| := by
      calc
        _≤|ε i*F.eval z| := le_abs_self _
        _=|F.eval z| := by rw [abs_mul,hεabs,one_mul]
    exact hd.trans_le hbound
  · intro i z hz
    have hden := intervalOrientation_pos (nodePolynomial Y) (α i) (β i) (hαβ i) (hnroot i) z hz
    have hnum : 0<ε i*F.eval z := lt_of_le_of_lt hH (hdominant i z hz)
    have hsσ : (σ i)^2=1 := by nlinarith [sq_abs (σ i),hσabs i]
    have he : (-1:ℝ)^i.val*(F.eval z/(nodePolynomial Y).eval z)=
        (ε i*F.eval z)/(σ i*(nodePolynomial Y).eval z) := by
      dsimp [ε]
      field_simp [(hnroot i z hz),show σ i≠0 by intro h; simp [h] at hsσ]
    rw [he]
    exact div_pos hnum hden

end Erdos1152.V5
