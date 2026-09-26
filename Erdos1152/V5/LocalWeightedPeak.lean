import Erdos1152.V5.UniformPacketControl
import Erdos1152.V5.SixthWindow
import Erdos1152.V5.LocalCoordinates

/-!
# Actual weighted polynomial for an arbitrary good counting box

Both the Bernstein function and the finite polynomial are constructed here.
The auxiliary equally spaced mesh does not restrict the original nodes Y.
-/
noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial MeasureTheory
namespace Erdos1152.V5
open V4

/-- Constants are chosen before all original finite nodes and all physical
scales. The output is a genuine global algebraic polynomial, not a postulated
local bump or a function with only a supremum norm lower bound. -/
theorem local_weighted_peak_exists (B : ℝ) (hB : 1<B) :
    ∃ρ:ℕ,∃b δ ℓ T K:ℝ,∃s₀:ℕ,
      0<ρ ∧ 0<b ∧ b<1 ∧ 0<δ ∧ 0<ℓ ∧ 0<T ∧ 0<K ∧
      ∀Y:Finset ℝ,∀x h y:ℝ,0<h→|y|≤1/4→
      s₀≤(insideNodes Y x h).card→
      (∀j:Fin 3,∀u∈Icc (-b) b,|finiteFieldJet j Y x h u-modelJet j u|≤δ)→
      (countingNodes Y x h y ρ).card≤2*ρ+1→
      ∃F:ℝ[X],∃α β:ℝ,
        F.natDegree<Y.card ∧
        (∀z∈Y,|F.eval z|≤3/2) ∧
        α<β ∧ β-α=ℓ ∧ Icc α β⊆Icc (-(ρ:ℝ)) ρ ∧
        (∀ξ∈Icc α β,B-1≤F.eval (x+h*(y+2*ξ/((insideNodes Y x h).card:ℝ)))) ∧
        (∀z∈Ioo (x-h) (x+h),2*T≤|microCoordinate (insideNodes Y x h).card x h y z|→
          |F.eval z|≤K/|microCoordinate (insideNodes Y x h).card x h y z|^3) ∧
        (∀z∈outsideNodes Y x h,F.eval z=0) := by
  obtain ⟨ρ,σ,M,ℓ,C,hρ,hσ0,hσπ,hM,hℓ,hC,hbern⟩ := local_bernstein_decay_exists B hB
  let t₀ := (σ/Real.pi+1)/2
  let κ := (1-t₀)/2
  let b := packetInterior κ
  let δ := packetFieldTolerance κ
  let η := min (1/64:ℝ) (1/(16*(M+1)))
  have ht₀ : 0<t₀ := by dsimp [t₀]; positivity
  have ht₁ : t₀<1 := by
    have := (div_lt_one Real.pi_pos).mpr hσπ
    dsimp [t₀]
    linarith
  have hσt : σ<Real.pi*t₀ := by dsimp [t₀]; field_simp; nlinarith [Real.pi_pos]
  have htlo : 1/2<t₀ := by dsimp [t₀]; have : 0<σ/Real.pi := div_pos hσ0 Real.pi_pos; linarith
  have hκ : 0<κ := by dsimp [κ]; linarith
  have hκ1 : κ≤1/4 := by dsimp [κ]; linarith
  have htt : t₀<1-κ := by dsimp [κ]; linarith
  have hη : 0<η := by dsimp [η]; positivity
  have hη64 : η≤1/64 := min_le_left _ _
  have hηM : η≤1/(16*(M+1)) := min_le_right _ _
  have herr : 2*η*(M+η)+η≤1 := by
    have hh := (le_div_iff₀ (by positivity : 0<16*(M+1))).mp hηM
    have h1 : η^2≤η := by nlinarith
    nlinarith
  obtain ⟨N,hN,T,K₀,hT,hK₀,hpacket⟩ := uniform_corrected_sampling C σ t₀ η hC ht₀ ht₁.le hσt hη
  obtain ⟨a,A,ha,hA,hamp⟩ := meshAmplitude_global_bounds
  obtain ⟨s₀,hs₀⟩ := uniform_actual_packet_control κ t₀ ρ M η A a N hκ hκ1 htt
    (Nat.cast_pos.mpr hρ) hM hη (by linarith) hA ha
  obtain ⟨hb0,hb1,hδ0,hδκ,hδ1,hend⟩ := packet_field_constants κ hκ hκ1
  let K := (A/a)*K₀
  refine ⟨ρ,b,δ,ℓ,T,K,s₀,hρ,by dsimp [b]; linarith,hb1,hδ0,hℓ,hT,by dsimp [K]; positivity,?_⟩
  intro Y x h y hh hy hsz hclose hgood
  let s := (insideNodes Y x h).card
  let m := packetMesh κ s
  let k := packetTilt κ s
  let θ := packetPhase m y
  let t := (m:ℝ)/(s:ℝ)
  have hsdata := hs₀ s hsz
  obtain ⟨hs,hmN,hdegree,ht,ht1,hcontrol⟩ := hsdata
  have hsR : 0<(s:ℝ) := by exact_mod_cast hs
  have htR : 0<t := ht₀.trans_le ht
  obtain ⟨hglobal,hratio,hmicro,hedge⟩ := hcontrol Y x h hh rfl hclose y hy
  let Λ := (countingNodes Y x h y ρ).image (microCoordinate s x h y)
  have hΛ : ∀ξ∈Λ,ξ∈Icc (-(ρ:ℝ)) ρ := by
    intro ξ hξ
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hξ
    exact Ico_subset_Icc_self (Finset.mem_filter.mp hz).2
  have hΛcard : Λ.card≤2*ρ+1 := (Finset.card_image_le).trans hgood
  obtain ⟨g,α,β,hgd,hreal,hbound,hnodes,hext,hαβ,hℓeq,hαβsub,hpeak,hgrowth⟩ := hbern Λ hΛ hΛcard
  obtain ⟨c,hv,hm0,hm1,happrox,htail⟩ := hpacket t θ ht ht1 (packetPhase_bound m y)
    g hgd hreal hgrowth
  let P := weightedPacket (finiteField Y x h) (finiteFieldFirst Y x h) s m k y N c
  let F := liftLocalPolynomial Y x h P
  have hPdeg : P.natDegree<s := by
    have hpd := weightedPacket_degree (finiteField Y x h) (finiteFieldFirst Y x h)
      N s m k hs hmN y hy c
    have hle : P.natDegree≤s-1 := hpd.trans hdegree
    omega
  have hFeval (u : ℝ) (hu : |u|<1) :
      F.eval (x+h*u)=
        matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h) s m k y u*
          (meshAmplitude m u/meshAmplitude m y)*finiteSincSum t θ N c ((s:ℝ)*(u-y)/2) := by
    rw [liftLocalPolynomial_eval Y x h u P hh (abs_lt.mp hu) hs]
    simpa [P,m,k,t,θ,mul_div_assoc] using
      weightedPacket_eval (finiteField Y x h) (finiteFieldFirst Y x h) N s m k hs hmN y hy c u hu.le
  have hAyp : 0<meshAmplitude m y := ha.trans_le (hamp m y (abs_le.mp (hy.trans (by norm_num)))).1
  have hAratio (u : ℝ) (hu : |u|≤1) :
      0<meshAmplitude m u/meshAmplitude m y ∧ meshAmplitude m u/meshAmplitude m y≤A/a := by
    have hhA := hamp m u (abs_le.mp hu)
    have hyA := hamp m y (abs_le.mp (hy.trans (by norm_num)))
    exact ⟨div_pos (ha.trans_le hhA.1) hAyp,
      div_le_div₀ hA.le hhA.2 ha hyA.1⟩
  have hSbound (ξ : ℝ) : |finiteSincSum t θ N c ξ|≤M+η := by
    have h1 := abs_add_le (finiteSincSum t θ N c ξ-(g ξ).re) ((g ξ).re)
    rw [sub_add_cancel] at h1
    have h2 := (Complex.abs_re_le_norm (g ξ)).trans (hbound ξ)
    linarith [happrox ξ]
  have hcoord (u : ℝ) : microCoordinate s x h y (x+h*u)=(s:ℝ)*(u-y)/2 := by
    unfold microCoordinate
    field_simp
    ring
  have hnodeSmall (z : ℝ) (hz : z∈insideNodes Y x h) :
      ‖g (microCoordinate s x h y z)‖≤1 := by
    by_cases hbox : microCoordinate s x h y z∈Ico (-(ρ:ℝ)) ρ
    · exact hnodes _ (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr ⟨hz,hbox⟩,rfl⟩)
    · apply hext
      by_contra hn
      have hn' := abs_lt.mp (lt_of_not_ge hn)
      exact hbox ⟨hn'.1.le,hn'.2⟩
  refine ⟨F,α,β,liftLocalPolynomial_degree Y x h P hPdeg,?_,hαβ,hℓeq,hαβsub,?_,?_,?_⟩
  · intro z hz
    by_cases hzI : z∈insideNodes Y x h
    · let u := (z-x)/h
      have hu : |u|<1 := by
        have hi := (Finset.mem_filter.mp hzI).2
        apply abs_lt.mpr
        constructor
        · rw [lt_div_iff₀ hh]; linarith [hi.1]
        · rw [div_lt_iff₀ hh]; linarith [hi.2]
      have hzrepr : z=x+h*u := by dsimp [u]; field_simp; ring
      have hgsmall : |(g ((s:ℝ)*(u-y)/2)).re|≤1 := by
        have hsml := (Complex.abs_re_le_norm _).trans (hnodeSmall z hzI)
        rw [hzrepr,hcoord] at hsml
        simpa using hsml
      have hSs : |finiteSincSum t θ N c ((s:ℝ)*(u-y)/2)|≤1+η := by
        have he := abs_add_le
          (finiteSincSum t θ N c ((s:ℝ)*(u-y)/2)-(g ((s:ℝ)*(u-y)/2)).re)
          ((g ((s:ℝ)*(u-y)/2)).re)
        rw [sub_add_cancel] at he
        have hap : |finiteSincSum t θ N c ((s:ℝ)*(u-y)/2)-
            (g ((s:ℝ)*(u-y)/2)).re| ≤ η := by
          simpa using happrox ((s:ℝ)*(u-y)/2)
        linarith
      rw [hzrepr,hFeval u hu,abs_mul,abs_mul,
        abs_of_pos (hglobal u hu).1,abs_of_pos (hAratio u hu.le).1]
      by_cases hub : |u|≤b
      · have har : meshAmplitude m u/meshAmplitude m y≤1+η := by
          have := (abs_le.mp (hratio u hub)).2
          linarith
        have hp := mul_le_mul_of_nonneg_left har (hglobal u hu).1.le
        have hfirst : matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h)
            s m k y u*(meshAmplitude m u/meshAmplitude m y)≤1+η := by
          exact hp.trans (mul_le_of_le_one_left (by positivity) (hglobal u hu).2)
        have hmul := mul_le_mul hfirst hSs (abs_nonneg _) (by positivity : 0≤1+η)
        nlinarith
      · have hfirst := mul_le_mul_of_nonneg_left (hAratio u hu.le).2 (hglobal u hu).1.le
        have hmul := mul_le_mul hfirst (hSbound ((s:ℝ)*(u-y)/2)) (abs_nonneg _)
          (show 0≤matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h) s m k y u*(A/a)
            from mul_nonneg (hglobal u hu).1.le (div_pos hA ha).le)
        have he := hedge u hu (lt_of_not_ge hub)
        linarith
    · have ho : z∈outsideNodes Y x h := Finset.mem_sdiff.mpr ⟨hz,hzI⟩
      rw [liftLocalPolynomial_zero_outside Y x h z P ho,abs_zero]
      norm_num
  · intro ξ hξ
    have hξρ : |ξ|≤ρ := abs_le.mpr (hαβsub hξ)
    have hu := (hmicro ξ hξρ).1
    have hu1 : |y+2*ξ/(s:ℝ)|<1 := hu.trans_lt hb1
    have hco : (s:ℝ)*(y+2*ξ/(s:ℝ)-y)/2=ξ := by field_simp; ring
    have hprod := packet_product_error
      (matchedEnvelope (finiteField Y x h) (finiteFieldFirst Y x h) s m k y (y+2*ξ/(s:ℝ)))
      (meshAmplitude m (y+2*ξ/(s:ℝ))/meshAmplitude m y)
      (finiteSincSum t θ N c ξ) ((g ξ).re) η M
      (hglobal _ hu1).1.le (hglobal _ hu1).2 (hmicro ξ hξρ).2
      (hratio _ hu) (happrox ξ) ((Complex.abs_re_le_norm _).trans (hbound ξ)) hη.le
    rw [hFeval _ hu1,hco]
    have he := (abs_le.mp (hprod.trans herr)).1
    linarith [hpeak ξ hξ]
  · intro z hz hfar
    let u := (z-x)/h
    have hu : |u|<1 := by
      apply abs_lt.mpr
      constructor
      · rw [lt_div_iff₀ hh]; linarith [hz.1]
      · rw [div_lt_iff₀ hh]; linarith [hz.2]
    have hzrepr : z=x+h*u := by dsimp [u]; field_simp; ring
    have hfar' : 2*T≤|(s:ℝ)*(u-y)/2| := by simpa [microCoordinate,u] using hfar
    have he := weightedPacket_tail (finiteField Y x h) (finiteFieldFirst Y x h)
      N s m k hs hmN y u hy hu.le c a A K₀ T ha hA hK₀.le hT
      (hamp m y (abs_le.mp (hy.trans (by norm_num)))).1 (hamp m u (abs_le.mp hu.le)).2
      (hglobal u hu).1.le (hglobal u hu).2 htail hfar'
    rw [hzrepr,liftLocalPolynomial_eval Y x h u P hh (abs_lt.mp hu) hs,hcoord]
    exact he
  · intro z hz
    exact liftLocalPolynomial_zero_outside Y x h z P hz

end Erdos1152.V5
