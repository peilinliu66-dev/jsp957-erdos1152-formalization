import Erdos1152.V5.WeightedPolynomial
import Erdos1152.V4.FiniteFieldJet
import Erdos1152.V5.ModelJet

/-!
Uniform finite thresholds for the actual row weight. The threshold is selected
before the node set, physical location, physical scale and moving center.
No rate such as s * ||Q_s-Q|| -> 0 is used.
-/
noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial
namespace Erdos1152.V5
open V4

private theorem amplitude_ratio_near_one (a b η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (ha : |a-1|<η/4) (hb : |b-1|<η/4) :
    0<b ∧ |a/b-1|≤η := by
  have hb0 : 1/2<b := by have := (abs_lt.mp hb).1; linarith
  refine ⟨by linarith,?_⟩
  have hn : |a-b|<η/2 := (abs_sub_le a 1 b).trans_lt (by
    rw [abs_sub_comm 1 b]
    linarith)
  rw [div_sub_one (by linarith : b≠0),abs_div,abs_of_pos (by linarith : 0<b)]
  apply (div_le_iff₀ (by linarith : 0<b)).mpr
  nlinarith

private theorem actual_residual_second_bound (Y : Finset ℝ) (a h b δ : ℝ)
    (s m : ℕ) (hs : 0<s) (hm : m≤s) (hb0 : 0≤b) (hb1 : b<1)
    (hδ : δ≤1)
    (hclose : ∀u,|u|≤b→|finiteFieldSecond Y a h u-1/(1-u^2)|≤δ) :
    ∀u,|u|≤b→|finiteFieldSecond Y a h u-(m:ℝ)/(s:ℝ)/(1-u^2)|≤
      2/(1-b^2)+2 := by
  intro u hu
  have hu1 : |u|<1 := hu.trans_lt hb1
  have hbden : 0<1-b^2 := by nlinarith
  have huden : 0<1-u^2 := by nlinarith [(abs_lt.mp hu1).1,(abs_lt.mp hu1).2]
  have hsq : u^2≤b^2 := by
    rw [← sq_abs u]
    exact pow_le_pow_left₀ (abs_nonneg _) hu 2
  have hq : 0≤1/(1-u^2) := by positivity
  have hqb : 1/(1-u^2)≤1/(1-b^2) := by
    exact one_div_le_one_div_of_le hbden (by linarith)
  have ht0 : 0≤(m:ℝ)/(s:ℝ) := by positivity
  have ht1 : (m:ℝ)/(s:ℝ)≤1 := by
    rw [div_le_one (by exact_mod_cast hs : 0<(s:ℝ))]
    exact_mod_cast hm
  have he : finiteFieldSecond Y a h u-(m:ℝ)/(s:ℝ)/(1-u^2)=
      (finiteFieldSecond Y a h u-1/(1-u^2))+
        (1-(m:ℝ)/(s:ℝ))*(1/(1-u^2)) := by ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hpos : 0≤(1-(m:ℝ)/(s:ℝ))*(1/(1-u^2)) := by positivity
  rw [abs_of_nonneg hpos]
  have hh := mul_le_of_le_one_left hq (show 1-(m:ℝ)/(s:ℝ)≤1 by linarith)
  rw [show 2/(1-b^2) = 2*(1/(1-b^2)) by ring]
  linarith [hclose u hu]

/-- Uniform packet control for genuine exterior-node fields. In the microscopic
conclusion ξ is physical center-relative coordinate s(u-y)/2. -/
theorem uniform_actual_packet_control (κ t₀ ρ M η A a : ℝ) (N : ℕ)
    (hκ : 0<κ) (hκ1 : κ≤1/4) (ht : t₀<1-κ)
    (hρ : 0<ρ) (hM : 0<M) (hη : 0<η) (hη1 : η≤1)
    (hA : 0<A) (ha : 0<a) :
    ∃s₀:ℕ,∀s≥s₀,
      0<s ∧ 8*(N+2)≤packetMesh κ s ∧
      packetMesh κ s-1+packetTilt κ s≤s-1 ∧
      t₀≤(packetMesh κ s:ℝ)/(s:ℝ) ∧ (packetMesh κ s:ℝ)/(s:ℝ)≤1 ∧
      ∀Y:Finset ℝ,∀x h:ℝ,0<h→(insideNodes Y x h).card=s→
      (∀j:Fin 3,∀u∈Icc (-packetInterior κ) (packetInterior κ),
        |finiteFieldJet j Y x h u-modelJet j u|≤packetFieldTolerance κ)→
      ∀y:ℝ,|y|≤1/4→
        (∀u:ℝ,|u|<1→
          0<matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h)
            s (packetMesh κ s) (packetTilt κ s) y u ∧
          matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h)
            s (packetMesh κ s) (packetTilt κ s) y u≤1) ∧
        (∀u:ℝ,|u|≤packetInterior κ→
          |meshAmplitude (packetMesh κ s) u/meshAmplitude (packetMesh κ s) y-1|≤η) ∧
        (∀ξ:ℝ,|ξ|≤ρ→
          |y+2*ξ/(s:ℝ)|≤packetInterior κ ∧
          |matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h)
            s (packetMesh κ s) (packetTilt κ s) y (y+2*ξ/(s:ℝ))-1|≤η) ∧
        (∀u:ℝ,|u|<1→packetInterior κ < |u|→
          matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h)
            s (packetMesh κ s) (packetTilt κ s) y u*(A/a)*(M+η)≤η) := by
  obtain ⟨hb0,hb1,hδ0,hδκ,hδ1,hend⟩ := packet_field_constants κ hκ hκ1
  let b := packetInterior κ
  let δ := packetFieldTolerance κ
  let C₂ := 2/(1-b^2)+2
  have hbpos : 0<b := by dsimp [b]; linarith
  have hbden : 0<1-b^2 := by dsimp [b]; nlinarith
  have hC₂ : 0<C₂ := by dsimp [C₂]; positivity
  have hmesh := packetMesh_tendsto_atTop κ (by linarith)
  have hratio := hmesh.eventually (meshAmplitude_uniform_one b hbpos.le hb1 (η/4) (by positivity))
  have hmicro : ∀ᶠs:ℕ in atTop,4*(C₂+2)*ρ^2/(s:ℝ)≤η := by
    have hh := tendsto_const_div_atTop_nhds_zero_nat (4*(C₂+2)*ρ^2)
    exact (hh.eventually_lt_const hη).mono (fun _ he => he.le)
  have hexp : Tendsto (fun s:ℕ => Real.exp (-κ*(s:ℝ)/16)*(A/a)*(M+η)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun s:ℕ => κ*(s:ℝ)/16) atTop atTop := by
      apply Filter.tendsto_atTop.mpr
      intro R
      obtain ⟨K,hK⟩ := exists_nat_gt (16*R/κ)
      filter_upwards [eventually_ge_atTop K] with s hs
      have hc : (K:ℝ)≤s := by exact_mod_cast hs
      have := (div_lt_iff₀ hκ).mp hK
      nlinarith
    have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hlin)
    simpa only [Function.comp_def, neg_div, neg_mul, mul_zero, zero_mul] using (he.mul_const (A/a)).mul_const (M+η)
  have hsize : ∀ᶠs:ℕ in atTop,8*ρ≤(s:ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  obtain ⟨s₀,hs₀⟩ := eventually_atTop.mp
    ((packet_degree_budget κ t₀ hκ hκ1 ht).and
      ((hmesh.eventually_ge_atTop (8*(N+2))).and
        (hratio.and (hmicro.and (hsize.and (hexp.eventually_lt_const hη))))))
  refine ⟨s₀,?_⟩
  intro s hs
  obtain ⟨hdeg,hmN,hamp,hmic,hsize,hedge⟩ := hs₀ s hs
  obtain ⟨hs0,hm0,hms,hk0,hks,hslack,hkb,hmt,hdegree⟩ := hdeg
  have hsR : 0<(s:ℝ) := by exact_mod_cast hs0
  have hmt1 : (packetMesh κ s:ℝ)/(s:ℝ)≤1 := by
    rw [div_le_one hsR]; exact_mod_cast hms
  refine ⟨hs0,hmN,hdegree,hmt,hmt1,?_⟩
  intro Y x h hh hcard hclose y hy
  have hcl : ∀u,|u|≤b→|finiteField Y x h u-externalField u|≤δ ∧
      |finiteFieldFirst Y x h u-Real.artanh u|≤δ ∧
      |finiteFieldSecond Y x h u-1/(1-u^2)|≤δ := by
    intro u hu
    exact ⟨hclose 0 u (abs_le.mp hu),hclose 1 u (abs_le.mp hu),hclose 2 u (abs_le.mp hu)⟩
  have hFd (u : ℝ) (hu : |u|<1) := hasDerivAt_finiteField Y x h u hh (abs_lt.mp hu)
  have hF₁d (u : ℝ) (hu : |u|<1) := hasDerivAt_finiteFieldFirst Y x h u hh (abs_lt.mp hu)
  have hglobal := matchedEnvelope_global (finiteField Y x h) (finiteFieldFirst Y x h)
    (finiteFieldSecond Y x h) hFd hF₁d (convexOn_finiteField Y x h hh)
    s (packetMesh κ s) (packetTilt κ s) κ b δ y hs0 hκ hms hslack hkb
    hb0 hb1 hδ0.le hδκ hend hy hcl
  have hα := matchedSlope_bound (finiteFieldFirst Y x h) s (packetMesh κ s)
    (packetTilt κ s) κ δ y hs0 hκ hslack hkb hδ0.le hδκ hy
    (hcl y (by dsimp [b]; linarith)).2.1
  have hres := actual_residual_second_bound Y x h b δ s (packetMesh κ s) hs0 hms
    hbpos.le hb1 hδ1 (fun u hu => (hcl u hu).2.2)
  refine ⟨fun u hu => ⟨(hglobal u hu).1,(hglobal u hu).2.1⟩,?_,?_,?_⟩
  · intro u hu
    exact (amplitude_ratio_near_one _ _ η hη hη1 (hamp u hu)
      (hamp y (by dsimp [b]; linarith))).2
  · intro ξ hξ
    have hd : |2*ξ/(s:ℝ)|≤1/4 := by
      rw [abs_div,abs_mul,abs_of_pos hsR]
      norm_num
      apply (div_le_iff₀ hsR).mpr
      linarith
    have hu : |y+2*ξ/(s:ℝ)|≤b := by
      apply (abs_add_le _ _).trans
      dsimp [b]
      linarith
    refine ⟨hu,?_⟩
    have hsmall : |matchedSlope (finiteFieldFirst Y x h) s (packetMesh κ s)
        (packetTilt κ s) y*(y+2*ξ/(s:ℝ)-y)|≤1/2 := by
      rw [add_sub_cancel_left,abs_mul]
      nlinarith [mul_le_mul hα hd (abs_nonneg _) (by norm_num : (0:ℝ)≤3/4)]
    have he := matchedEnvelope_micro_bound (finiteField Y x h) (finiteFieldFirst Y x h)
      (finiteFieldSecond Y x h) s (packetMesh κ s) (packetTilt κ s) b y
      (y+2*ξ/(s:ℝ)) C₂ hs0 hk0 hks hC₂.le (by dsimp [b]; linarith) hu
      (fun v hv => hFd v (hv.trans_lt hb1))
      (fun v hv => hF₁d v (hv.trans_lt hb1)) hb1 hres hα hsmall
      (hglobal _ (hu.trans_lt hb1)).2.1
    apply he.trans
    have hξsq : ξ^2≤ρ^2 := by
      rw [← sq_abs ξ]
      exact pow_le_pow_left₀ (abs_nonneg _) hξ 2
    calc
      (s:ℝ)*(C₂+2)*(y+2*ξ/(s:ℝ)-y)^2=4*(C₂+2)*ξ^2/(s:ℝ) := by field_simp; ring
      _≤4*(C₂+2)*ρ^2/(s:ℝ) := by gcongr
      _≤η := hmic
  · intro u hu hbu
    apply (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((hglobal u hu).2.2 hbu) (by positivity : 0≤A/a))
      (by positivity : 0≤M+η)).trans
    exact hedge.le

end Erdos1152.V5
