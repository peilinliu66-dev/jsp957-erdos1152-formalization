import Erdos1152.V5.WeightedEnvelope
import Erdos1152.V5.MeshKernel

noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial
namespace Erdos1152.V5

def packetMesh (κ : ℝ) (s : ℕ) : ℕ := ⌊(1-κ)*(s:ℝ)⌋₊
def packetTilt (κ : ℝ) (s : ℕ) : ℕ := (s-packetMesh κ s)/2
def packetInterior (κ : ℝ) : ℝ := 1-κ/256
def packetFieldTolerance (κ : ℝ) : ℝ := κ/1024

theorem packet_field_constants (κ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1/4) :
    3/4≤packetInterior κ ∧ packetInterior κ<1 ∧
    0<packetFieldTolerance κ ∧ packetFieldTolerance κ≤κ/512 ∧
    packetFieldTolerance κ≤1 ∧
    Real.log (2/(1+packetInterior κ))≤κ/64 := by
  have hb : 0<1+packetInterior κ := by dsimp [packetInterior]; linarith
  refine ⟨by dsimp [packetInterior]; linarith,by dsimp [packetInterior]; linarith,
    by dsimp [packetFieldTolerance]; positivity,by dsimp [packetFieldTolerance]; linarith,
    by dsimp [packetFieldTolerance]; linarith,?_⟩
  have hlog := Real.log_le_sub_one_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hb)
  apply hlog.trans
  rw [sub_le_iff_le_add,div_le_iff₀ hb]
  dsimp [packetInterior]
  nlinarith

/-- Every finite degree inequality, including the integer rounding losses, is
 paid from the original local node count s. -/
theorem packet_degree_budget (κ t₀ : ℝ) (hκ : 0<κ) (hκ1 : κ≤1/4)
    (ht : t₀<1-κ) :
    ∀ᶠs:ℕ in atTop,
      0<s ∧ 0<packetMesh κ s ∧ packetMesh κ s≤s ∧
      0<packetTilt κ s ∧ packetTilt κ s≤s ∧
      κ*(s:ℝ)≤(s:ℝ)-(packetMesh κ s:ℝ) ∧
      (9/20:ℝ)*((s:ℝ)-(packetMesh κ s:ℝ))≤packetTilt κ s ∧
      t₀≤(packetMesh κ s:ℝ)/(s:ℝ) ∧
      packetMesh κ s-1+packetTilt κ s≤s-1 := by
  have hsD : Tendsto (fun s:ℕ => κ*(s:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hκ
  have hsT : Tendsto (fun s:ℕ => (1-κ-t₀)*(s:ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith)
  filter_upwards [eventually_ge_atTop 4,hsD.eventually_ge_atTop 20,hsT.eventually_ge_atTop 2]
    with s hs hs20 hs2
  let m := packetMesh κ s
  let k := packetTilt κ s
  have hsR : 0<(s:ℝ) := by exact_mod_cast (show 0<s by omega)
  have hx : 0≤(1-κ)*(s:ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg s)
  have hfloor : (m:ℝ)≤(1-κ)*(s:ℝ) := Nat.floor_le hx
  have hfloor' : (1-κ)*(s:ℝ)<(m:ℝ)+1 := Nat.lt_floor_add_one _
  have hmeshLower : (3 / 4 : ℝ) * (s : ℝ) ≤ (1 - κ) * (s : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg s)
  have hm : m≤s := by exact_mod_cast (show (m:ℝ)≤s by nlinarith)
  have hm0 : 0<m := by
    have : (4:ℝ)≤s := by exact_mod_cast hs
    have : (0:ℝ)<m := by linarith
    exact_mod_cast this
  have hcast : ((s-m:ℕ):ℝ)=(s:ℝ)-(m:ℝ) := Nat.cast_sub hm
  have hD20R : (20 : ℝ) ≤ (s : ℝ) - (m : ℝ) := by nlinarith
  have hD20 : 20≤s-m := by
    rw [← hcast] at hD20R
    exact_mod_cast hD20R
  have hk2 : 2*k≤s-m ∧ s-m<2*k+2 := by
    dsimp [k,packetTilt,m]
    omega
  have hk0 : 0<k := by omega
  have hkS : k≤s := by omega
  have hkR : (9/20:ℝ)*((s:ℝ)-(m:ℝ))≤k := by
    have h1 : ((2 * k : ℕ) : ℝ) ≤ ((s - m : ℕ) : ℝ) := by
      exact_mod_cast hk2.1
    have h2 : ((s - m : ℕ) : ℝ) < ((2 * k + 2 : ℕ) : ℝ) := by
      exact_mod_cast hk2.2
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, hcast] at h1 h2
    nlinarith
  refine ⟨by omega,hm0,hm,hk0,hkS,by nlinarith,hkR,?_,by dsimp [m,k] at *; omega⟩
  rw [le_div_iff₀ hsR]
  nlinarith

theorem packetMesh_tendsto_atTop (κ : ℝ) (hκ : κ<1) :
    Tendsto (packetMesh κ) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by linarith : 0<1-κ))

/-- A nearest-center phase obtained by one floor, with no moving-grid ambiguity. -/
def packetCenterIndex (m : ℕ) (y : ℝ) : ℤ := ⌊(m:ℝ)*(1+y)/2⌋
def packetPhase (m : ℕ) (y : ℝ) : ℝ :=
  (packetCenterIndex m y:ℝ)+1/2-(m:ℝ)*(1+y)/2
def packetIndex (m : ℕ) (y : ℝ) (j : ℤ) : ℕ := (packetCenterIndex m y+j).toNat

theorem packetPhase_bound (m : ℕ) (y : ℝ) : |packetPhase m y|≤1/2 := by
  have h0 := Int.floor_le ((m:ℝ)*(1+y)/2)
  have h1 := Int.lt_floor_add_one ((m:ℝ)*(1+y)/2)
  unfold packetPhase packetCenterIndex
  apply abs_le.mpr
  constructor <;> linarith

theorem packetIndex_properties (N m s : ℕ) (hm : 8*(N+2)≤m) (hs : 0<s)
    (y : ℝ) (hy : |y|≤1/4) :
    ∀j∈symmetricIndices N,packetIndex m y j<m ∧
      (s:ℝ)*(meshNode m (packetIndex m y j)-y)/2=
        samplePoint ((m:ℝ)/(s:ℝ)) (packetPhase m y) j := by
  intro j hj
  have hm0 : 0<m := by omega
  have hmR : (8:ℝ)*(N+2)≤m := by exact_mod_cast hm
  have hfloor := Int.floor_le ((m:ℝ)*(1+y)/2)
  have hfloor' := Int.lt_floor_add_one ((m:ℝ)*(1+y)/2)
  have hjs := Finset.mem_Icc.mp hj
  have hjlo : -(N:ℝ)≤(j:ℝ) := by exact_mod_cast hjs.1
  have hjhi : (j:ℝ)≤N := by exact_mod_cast hjs.2
  have hpos : 0≤packetCenterIndex m y+j := by
    have he : (0:ℝ)≤(packetCenterIndex m y:ℝ)+(j:ℝ) := by
      dsimp [packetCenterIndex]
      have hmy := mul_le_mul_of_nonneg_left (abs_le.mp hy).1 (Nat.cast_nonneg m)
      nlinarith
    exact_mod_cast he
  have hlt : packetCenterIndex m y+j<(m:ℤ) := by
    have he : (packetCenterIndex m y:ℝ)+(j:ℝ)<(m:ℝ) := by
      dsimp [packetCenterIndex]
      have hmy := mul_le_mul_of_nonneg_left (abs_le.mp hy).2 (Nat.cast_nonneg m)
      nlinarith
    exact_mod_cast he
  have hcast : (packetIndex m y j:ℤ)=packetCenterIndex m y+j := Int.toNat_of_nonneg hpos
  have hindex : (packetIndex m y j : ℤ) < (m : ℤ) := by
    rw [hcast]
    exact hlt
  refine ⟨by exact_mod_cast hindex,?_⟩
  have hcastR : (packetIndex m y j:ℝ)=(packetCenterIndex m y:ℝ)+(j:ℝ) := by exact_mod_cast hcast
  unfold meshNode samplePoint packetPhase
  rw [hcastR]
  field_simp
  ring

end Erdos1152.V5
