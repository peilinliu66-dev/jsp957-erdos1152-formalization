import Erdos1152.V5.GoodBoxes
import Erdos1152.SeparatedSamples

noncomputable section
open scoped Topology Real
open Real Set Filter Finset
namespace Erdos1152.V5

private theorem div_lt_of_lt_of_same_mod (u v q : ℕ) (huv : u<v) (hmod : u%q=v%q) :
    u/q<v/q := by
  have hle : u / q ≤ v / q := Nat.div_le_div_right huv.le
  by_contra hnot
  have he : u/q=v/q := Nat.le_antisymm hle (le_of_not_gt hnot)
  have hu := Nat.mod_add_div u q
  have hv := Nat.mod_add_div v q
  rw [hmod,he] at hu
  omega

private theorem same_mod_gap (u v q : ℕ) (hq : 0<q) (huv : u≠v) (hmod : u%q=v%q) :
    (q:ℝ)≤|(u:ℝ)-(v:ℝ)| := by
  have hu : ((u%q:ℕ):ℝ)+(q:ℝ)*(u/q:ℕ)=u := by exact_mod_cast Nat.mod_add_div u q
  have hv : ((v%q:ℕ):ℝ)+(q:ℝ)*(v/q:ℕ)=v := by exact_mod_cast Nat.mod_add_div v q
  have hq0 : 0<(q:ℝ) := by exact_mod_cast hq
  rcases lt_or_gt_of_ne huv with huv | hvu
  · have hd := div_lt_of_lt_of_same_mod u v q huv hmod
    have hdR : ((u/q:ℕ):ℝ)+1≤(v/q:ℕ) := by exact_mod_cast Nat.succ_le_iff.mpr hd
    have huvR : (u:ℝ)<v := by exact_mod_cast huv
    rw [abs_of_neg (by linarith),hmod] at *
    nlinarith
  · have hd := div_lt_of_lt_of_same_mod v u q hvu hmod.symm
    have hdR : ((v/q:ℕ):ℝ)+1≤(u/q:ℕ) := by exact_mod_cast Nat.succ_le_iff.mpr hd
    have huvR : (v:ℝ)<u := by exact_mod_cast hvu
    rw [abs_of_pos (by linarith),hmod] at *
    nlinarith

/-- Sorting one residue class preserves its quantitative spacing. -/
theorem selected_centers (s ρ q K : ℕ) (hρ : 0<ρ) (hq : 0<q)
    (e : Fin K→ℕ) (he : StrictMono e) (hmod : ∀i j,e i%q=e j%q) :
    StrictMono (fun i => boxCenter s ρ (e i)) ∧
      ∀i j,(2*(ρ:ℝ)*q)*|(i.val:ℝ)-(j.val:ℝ)|≤
        |boxCenter s ρ (e i)-boxCenter s ρ (e j)| := by
  have hρR : 0<(ρ:ℝ) := by exact_mod_cast hρ
  have hmono : StrictMono (fun i => boxCenter s ρ (e i)) := by
    intro i j hij
    have heR : (e i:ℝ)<e j := by exact_mod_cast he hij
    dsimp [boxCenter,boxLeft]
    nlinarith
  refine ⟨hmono,?_⟩
  cases K with
  | zero => intro i; exact Fin.elim0 i
  | succ K =>
    apply separated_mono_gap _ (2*(ρ:ℝ)*q) hmono
    intro i j hij
    have hg := same_mod_gap (e i) (e j) q hq (he.injective.ne hij) (hmod i j)
    have hid : boxCenter s ρ (e i)-boxCenter s ρ (e j)=2*(ρ:ℝ)*((e i:ℝ)-(e j:ℝ)) := by
      dsimp [boxCenter,boxLeft]; ring
    rw [hid,abs_mul,abs_of_pos (by positivity : 0<2*(ρ:ℝ))]
    exact mul_le_mul_of_nonneg_left hg (by positivity)

/-- The spacing is fixed before the original nodes and can make the entire
finite cubic cross sum at most 1/4. A coarse explicit threshold suffices. -/
theorem exists_packet_stride (ρ : ℕ) (hρ : 0<ρ) (T D : ℝ) (hT : 0<T) (hD : 0<D) :
    ∃q:ℕ,0<q ∧ 4*T≤2*(ρ:ℝ)*q ∧ 4*(ρ:ℝ)≤2*(ρ:ℝ)*q ∧
      32*D/(2*(ρ:ℝ)*q)^3≤1/4 := by
  obtain ⟨q,hq⟩ := exists_nat_gt (max 2 (max (4*T) (128*D+1)))
  have hq2 : (2:ℝ)<q := lt_of_le_of_lt (le_max_left _ _) hq
  have hqT : 4*T<(q:ℝ) := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hq
  have hqD : 128*D+1<(q:ℝ) := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hq
  have hρR : (1:ℝ)≤ρ := by exact_mod_cast hρ
  have hL : 1≤2*(ρ:ℝ)*q := by nlinarith
  have hLcube : 2*(ρ:ℝ)*q≤(2*(ρ:ℝ)*q)^3 := by nlinarith [sq_nonneg (2*(ρ:ℝ)*q-1)]
  refine ⟨q,by exact_mod_cast (show (0:ℝ)<q by linarith),by nlinarith,by nlinarith,?_⟩
  rw [div_le_iff₀ (by positivity : 0<(2*(ρ:ℝ)*q)^3)]
  nlinarith

end Erdos1152.V5
