import Erdos1152.V5.TaylorSupport
import Erdos1152.TiltedEnvelope

noncomputable section
open scoped Topology Real
open Real Set Filter Polynomial
namespace Erdos1152.V5

def residualField (F : ℝ→ℝ) (s m : ℕ) (u : ℝ) : ℝ :=
  F u-(m:ℝ)/(s:ℝ)*externalField u

def matchedSlope (F₁ : ℝ→ℝ) (s m k : ℕ) (y : ℝ) : ℝ :=
  (s:ℝ)*(F₁ y-(m:ℝ)/(s:ℝ)*Real.artanh y)/(k:ℝ)

def matchedEnvelope (F F₁ : ℝ→ℝ) (s m k : ℕ) (y u : ℝ) : ℝ :=
  Real.exp (-(s:ℝ)*(residualField F s m u-residualField F s m y))*
    (1+matchedSlope F₁ s m k y*(u-y))^k

theorem matchedSlope_bound (F₁ : ℝ→ℝ) (s m k : ℕ) (κ δ y : ℝ)
    (hs : 0<s) (hκ : 0<κ) (hslack : κ*(s:ℝ)≤(s:ℝ)-(m:ℝ))
    (hk : (9/20:ℝ)*((s:ℝ)-(m:ℝ))≤k) (hδ : 0≤δ) (hδκ : δ≤κ/512)
    (hy : |y|≤1/4) (hfirst : |F₁ y-Real.artanh y|≤δ) :
    |matchedSlope F₁ s m k y|≤3/4 := by
  have hs' : 0<(s:ℝ) := by exact_mod_cast hs
  have hD : 0<(s:ℝ)-(m:ℝ) := lt_of_lt_of_le (mul_pos hκ hs') hslack
  have hk' : 0<(k:ℝ) := lt_of_lt_of_le (by positivity) hk
  have hmatch : (s:ℝ)*(F₁ y-(m:ℝ)/(s:ℝ)*Real.artanh y)=
      (s:ℝ)*(F₁ y-Real.artanh y)+((s:ℝ)-(m:ℝ))*Real.artanh y := by
    field_simp; ring
  have hab := abs_add_le ((s:ℝ)*(F₁ y-Real.artanh y))
    (((s:ℝ)-(m:ℝ))*Real.artanh y)
  have hq := artanh_central_bound y hy
  have hsδ : (s:ℝ)*δ≤((s:ℝ)-(m:ℝ))/512 := by
    have hh := mul_le_mul_of_nonneg_left hδκ hs'.le
    nlinarith
  rw [matchedSlope,abs_div,abs_of_pos hk',hmatch]
  apply (div_le_iff₀ hk').mpr
  rw [abs_mul,abs_mul,abs_of_pos hs',abs_of_pos hD] at hab
  have hf := mul_le_mul_of_nonneg_left hfirst hs'.le
  have hq' := mul_le_mul_of_nonneg_left hq hD.le
  nlinarith

theorem matched_base_pos (α y u : ℝ) (hα : |α|≤3/4) (hy : |y|≤1/4)
    (hu : |u|≤1) : 1/16≤1+α*(u-y) := by
  have hd : |u-y|≤5/4 := (abs_sub _ _).trans (by linarith)
  have hp : |α*(u-y)|≤15/16 := by
    rw [abs_mul]
    nlinarith [mul_le_mul hα hd (abs_nonneg _) (by norm_num : (0:ℝ)≤3/4)]
  linarith [(abs_le.mp hp).1]

private theorem right_residual_support
    (F F₁ : ℝ→ℝ) (hc : ConvexOn ℝ (Ioo (-1:ℝ) 1) F)
    (hF : ∀u,|u|<1→HasDerivAt F (F₁ u) u)
    (t κ b δ y u : ℝ) (ht : t≤1-κ) (hκ : 0<κ)
    (hb0 : 3/4≤b) (hb1 : b<1) (hδ : 0≤δ) (hδκ : δ≤κ/512)
    (hend : Real.log (2/(1+b))≤κ/64) (hy : |y|≤1/4)
    (hu : b≤u) (hu1 : u<1)
    (hclose : ∀v,|v|≤b→|F v-externalField v|≤δ ∧ |F₁ v-Real.artanh v|≤δ) :
    κ/16≤(F u-t*externalField u)-(F y-t*externalField y)-
      (F₁ y-t*Real.artanh y)*(u-y) := by
  have hb : 0<b := by linarith
  have hy1 : |y|<1 := hy.trans_lt (by norm_num)
  have hyb : |y|≤b := by linarith
  have hbb : |b|≤b := by rw [abs_of_pos hb]
  have hs := convex_tangent_line (Ioo (-1:ℝ) 1) F hc b u (F₁ b) (by constructor <;> linarith)
    ⟨by linarith,hu1⟩ (hF b (by rw [abs_of_pos hb]; exact hb1))
  have hQ := model_strong_support y u hy1 (abs_lt.mpr ⟨by linarith,hu1⟩)
  have hRb := model_endpoint_remainder b u hb hb1 hu hu1
  have hbF := abs_le.mp (hclose b hbb).1
  have hbD := abs_le.mp (hclose b hbb).2
  have hyF := abs_le.mp (hclose y hyb).1
  have hyD := abs_le.mp (hclose y hyb).2
  have hdiff : 1/2≤u-y := by have := (abs_le.mp hy).2; linarith
  have hdiffU : u-y≤5/4 := by have := (abs_le.mp hy).1; linarith
  have hub : 0≤u-b := sub_nonneg.mpr hu
  have hubU : u-b≤1/4 := by linarith
  let DQ := externalField u-externalField y-Real.artanh y*(u-y)
  have hDQ : 1/8≤DQ := by dsimp [DQ]; nlinarith
  have he : (1-t)*DQ-
      (externalField u-externalField b-Real.artanh b*(u-b))-4*δ ≤
      (F u-t*externalField u)-(F y-t*externalField y)-
        (F₁ y-t*Real.artanh y)*(u-y) := by
    have h1 := mul_le_mul_of_nonneg_right hbD.1 hub
    have h2 := mul_le_mul_of_nonneg_right hyD.2 (by linarith : 0≤u-y)
    have h3 := mul_le_mul_of_nonneg_left hubU hδ
    have h4 := mul_le_mul_of_nonneg_left hdiffU hδ
    dsimp [DQ]
    nlinarith
  have hprod : κ/8≤(1-t)*DQ := by
    have htt : κ≤1-t := by linarith
    nlinarith [mul_le_mul htt hDQ (by norm_num : (0:ℝ)≤1/8) (by linarith : 0≤1-t)]
  nlinarith

/-- A matched polynomial tilt is controlled on the whole local interval, including
 regions outside the compact set on which the field is close to the model. -/
theorem matchedEnvelope_global
    (F F₁ F₂ : ℝ→ℝ)
    (hF : ∀u,|u|<1→HasDerivAt F (F₁ u) u)
    (hF₁ : ∀u,|u|<1→HasDerivAt F₁ (F₂ u) u)
    (hc : ConvexOn ℝ (Ioo (-1:ℝ) 1) F)
    (s m k : ℕ) (κ b δ y : ℝ)
    (hs : 0<s) (hκ : 0<κ) (hm : m≤s)
    (hslack : κ*(s:ℝ)≤(s:ℝ)-(m:ℝ))
    (hk : (9/20:ℝ)*((s:ℝ)-(m:ℝ))≤k)
    (hb0 : 3/4≤b) (hb1 : b<1) (hδ : 0≤δ) (hδκ : δ≤κ/512)
    (hend : Real.log (2/(1+b))≤κ/64) (hy : |y|≤1/4)
    (hclose : ∀u,|u|≤b→|F u-externalField u|≤δ ∧
      |F₁ u-Real.artanh u|≤δ ∧ |F₂ u-1/(1-u^2)|≤δ) :
    ∀u,|u|<1→0<matchedEnvelope F F₁ s m k y u ∧
      matchedEnvelope F F₁ s m k y u≤1 ∧
      (b < |u| → matchedEnvelope F F₁ s m k y u≤Real.exp (-κ*s/16)) := by
  have hs' : 0<(s:ℝ) := by exact_mod_cast hs
  have hD : 0<(s:ℝ)-(m:ℝ) := lt_of_lt_of_le (mul_pos hκ hs') hslack
  have hk' : 0<(k:ℝ) := lt_of_lt_of_le (by positivity) hk
  have hα := matchedSlope_bound F₁ s m k κ δ y hs hκ hslack hk hδ hδκ hy
    (hclose y (by linarith)).2.1
  let t := (m:ℝ)/(s:ℝ)
  have ht0 : 0≤t := by dsimp [t]; positivity
  have ht : t≤1-κ := by
    dsimp [t]
    rw [div_le_iff₀ hs']
    nlinarith
  let R := residualField F s m
  let R₁ := fun u => F₁ u-t*Real.artanh u
  let R₂ := fun u => F₂ u-t/(1-u^2)
  have hdR (u : ℝ) (hu : |u|<1) : HasDerivAt R (R₁ u) u :=
    (hF u hu).sub ((externalField_derivative (abs_lt.mp hu)).const_mul t)
  have hdR₁ (u : ℝ) (hu : |u|<1) : HasDerivAt R₁ (R₂ u) u := by
    convert! (hF₁ u hu).sub ((artanh_derivative (abs_lt.mp hu)).const_mul t) using 1
    dsimp only [R₂]
    ring
  have hRn (u : ℝ) (hu : |u|≤b) : 0≤R₂ u := by
    have hu1 : |u|<1 := hu.trans_lt hb1
    have hp : 0<1-u^2 := by nlinarith [(abs_lt.mp hu1).1,(abs_lt.mp hu1).2]
    have hunit : 1≤1/(1-u^2) := by rw [le_div_iff₀ hp]; nlinarith [sq_nonneg u]
    have he := (abs_le.mp (hclose u hu).2.2).1
    have htt : κ≤1-t := by linarith
    dsimp [R₂]
    have hprod := mul_le_mul htt hunit (by norm_num : (0:ℝ)≤1) (by linarith : 0≤1-t)
    have hprod' : κ ≤ 1 / (1 - u ^ 2) - t / (1 - u ^ 2) := by
      simpa only [mul_one,mul_one_div,sub_div] using hprod
    linarith
  have hsupport (u : ℝ) (hu : |u|<1) :
      0≤R u-R y-R₁ y*(u-y) ∧ (b < |u| → κ/16≤R u-R y-R₁ y*(u-y)) := by
    by_cases hub : |u|≤b
    · have hh := tangent_of_second_nonneg (Icc (-b) b) (convex_Icc _ _) R R₁ R₂
        (fun v hv => hdR v ((abs_le.mpr hv).trans_lt hb1))
        (fun v hv => hdR₁ v ((abs_le.mpr hv).trans_lt hb1))
        (fun v hv => hRn v (abs_le.mpr hv))
        (abs_le.mp (show |y|≤b by linarith)) (abs_le.mp hub)
      exact ⟨by linarith,by intro hbad; linarith⟩
    · have hbig : b < |u| := lt_of_not_ge hub
      have hh : κ/16≤R u-R y-R₁ y*(u-y) := by
        rcases (abs_lt.mp hu) with ⟨huL,huU⟩
        by_cases hup : 0≤u
        · have hbu : b≤u := by
            rw [abs_of_nonneg hup] at hbig
            exact hbig.le
          exact right_residual_support F F₁ hc hF t κ b δ y u ht hκ hb0 hb1 hδ hδκ
            hend hy hbu huU (fun v hv => ⟨(hclose v hv).1,(hclose v hv).2.1⟩)
        · let Fr := fun v => F (-v)
          let F₁r := fun v => -F₁ (-v)
          have hcr : ConvexOn ℝ (Ioo (-1:ℝ) 1) Fr := by
            refine ⟨convex_Ioo _ _,?_⟩
            intro v hv w hw a d ha hd had
            have he := hc.2 (show -v∈Ioo (-1:ℝ) 1 by constructor <;> linarith [hv.1,hv.2])
              (show -w∈Ioo (-1:ℝ) 1 by constructor <;> linarith [hw.1,hw.2]) ha hd had
            simpa [Fr,smul_eq_mul,neg_add,neg_mul,mul_neg,add_comm] using he
          have hFr (v : ℝ) (hv : |v|<1) : HasDerivAt Fr (F₁r v) v := by
            convert! (hF (-v) (by simpa only [abs_neg] using hv)).comp v
              (hasDerivAt_neg v) using 1
            dsimp only [F₁r]
            ring
          have hartanhNeg (v : ℝ) (hv : |v| < 1) : Real.artanh (-v) = -Real.artanh v := by
            have he : Real.tanh (-Real.artanh v) = -v := by
              rw [Real.tanh_neg, Real.tanh_artanh (abs_lt.mp hv)]
            calc
              Real.artanh (-v) = Real.artanh (Real.tanh (-Real.artanh v)) :=
                congrArg Real.artanh he.symm
              _ = -Real.artanh v := Real.artanh_tanh _
          have hcloseR : ∀v,|v|≤b→|Fr v-externalField v|≤δ ∧ |F₁r v-Real.artanh v|≤δ := by
            intro v hv
            have h := hclose (-v) (by simpa only [abs_neg] using hv)
            refine ⟨?_, ?_⟩
            · simpa only [Fr,externalField_neg] using h.1
            · change |-F₁ (-v) - Real.artanh v| ≤ δ
              have he : -F₁ (-v) - Real.artanh v = -(F₁ (-v) - Real.artanh (-v)) := by
                rw [hartanhNeg v (hv.trans_lt hb1)]
                ring
              rw [he,abs_neg]
              exact h.2.1
          have he := right_residual_support Fr F₁r hcr hFr t κ b δ (-y) (-u)
            ht hκ hb0 hb1 hδ hδκ hend (by simpa only [abs_neg] using hy)
            (by rw [abs_of_neg (lt_of_not_ge hup)] at hbig; linarith) (by linarith) hcloseR
          simp only [Fr,F₁r,neg_neg,externalField_neg,
            hartanhNeg y (hy.trans_lt (by norm_num))] at he
          dsimp only [R,R₁,residualField]
          convert he using 1 <;> ring
      exact ⟨(by positivity : 0≤κ/16).trans hh,fun _ => hh⟩
  intro u hu
  have hbase := matched_base_pos (matchedSlope F₁ s m k y) y u hα hy hu.le
  have hmatch : (k:ℝ)*matchedSlope F₁ s m k y=(s:ℝ)*R₁ y := by
    unfold matchedSlope R₁ t
    field_simp
  have henv : matchedEnvelope F F₁ s m k y u≤
      Real.exp (-(s:ℝ)*(R u-R y-R₁ y*(u-y))) := by
    unfold matchedEnvelope
    apply (mul_le_mul_of_nonneg_left
      (binomial_tilt_le_exp k (matchedSlope F₁ s m k y*(u-y)) (by linarith))
      (Real.exp_pos _).le).trans_eq
    rw [←Real.exp_add]
    congr 1
    rw [←mul_assoc,hmatch]
    ring
  refine ⟨mul_pos (Real.exp_pos _) (pow_pos (by linarith) k),?_,?_⟩
  · apply henv.trans
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs'.le) (hsupport u hu).1
  · intro hbig
    apply henv.trans
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left ((hsupport u hu).2 hbig) hs'.le
    nlinarith

/-- A finite micro-scale error bound; it does not multiply a bare C² error by s.
 The linear drift is cancelled by the exact matching equation. -/
theorem matchedEnvelope_micro_bound
    (F F₁ F₂ : ℝ→ℝ) (s m k : ℕ) (b y u C : ℝ)
    (hs : 0<s) (hk : 0<k) (hks : k≤s) (hC : 0≤C)
    (hy : |y|≤b) (hu : |u|≤b)
    (hF : ∀v,|v|≤b→HasDerivAt F (F₁ v) v)
    (hF₁ : ∀v,|v|≤b→HasDerivAt F₁ (F₂ v) v)
    (hb : b<1)
    (hR₂ : ∀v,|v|≤b→|F₂ v-(m:ℝ)/(s:ℝ)/(1-v^2)|≤C)
    (hα : |matchedSlope F₁ s m k y|≤3/4)
    (hsmall : |matchedSlope F₁ s m k y*(u-y)|≤1/2)
    (hE : matchedEnvelope F F₁ s m k y u≤1) :
    |matchedEnvelope F F₁ s m k y u-1|≤(s:ℝ)*(C+2)*(u-y)^2 := by
  let t := (m:ℝ)/(s:ℝ)
  let R := residualField F s m
  let R₁ := fun v => F₁ v-t*Real.artanh v
  let R₂ := fun v => F₂ v-t/(1-v^2)
  let α := matchedSlope F₁ s m k y
  have hd (v : ℝ) (hv : v∈Icc (-b) b) : HasDerivAt R (R₁ v) v :=
    (hF v (abs_le.mpr hv)).sub ((externalField_derivative (abs_lt.mp
      ((abs_le.mpr hv).trans_lt hb))).const_mul t)
  have hd1 (v : ℝ) (hv : v∈Icc (-b) b) : HasDerivAt R₁ (R₂ v) v := by
    convert! (hF₁ v (abs_le.mpr hv)).sub ((artanh_derivative (abs_lt.mp
      ((abs_le.mpr hv).trans_lt hb))).const_mul t) using 1
    dsimp only [R₂]
    ring
  have hrem := quadratic_remainder_bound (Icc (-b) b) (convex_Icc _ _) R R₁ R₂ hd hd1 C hC
    (fun v hv => hR₂ v (abs_le.mpr hv)) (abs_le.mp hy) (abs_le.mp hu)
  have hlog := log_one_add_error_bound (α*(u-y)) hsmall
  have hk' : (k:ℝ)≠0 := by exact_mod_cast hk.ne'
  have hmatch : (k:ℝ)*α=(s:ℝ)*R₁ y := by dsimp [α,matchedSlope,R₁,t]; field_simp
  have hbase : 0<1+α*(u-y) := by have hh := (abs_le.mp hsmall).1; linarith
  have hpos : 0<matchedEnvelope F F₁ s m k y u :=
    mul_pos (Real.exp_pos _) (pow_pos hbase k)
  have hidentity : Real.log (matchedEnvelope F F₁ s m k y u)=
      -(s:ℝ)*(R u-R y-R₁ y*(u-y))-
        (k:ℝ)*(α*(u-y)-Real.log (1+α*(u-y))) := by
    rw [matchedEnvelope,Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hbase.ne'),
      Real.log_exp,Real.log_pow]
    have hmatch_delta := congrArg (fun z:ℝ => z*(u-y)) hmatch
    dsimp [R]
    nlinarith [hmatch_delta]
  have hlogabs : |Real.log (matchedEnvelope F F₁ s m k y u)|≤(s:ℝ)*(C+2)*(u-y)^2 := by
    rw [hidentity]
    apply (abs_sub _ _).trans
    simp only [abs_mul,abs_neg,Nat.abs_cast,abs_of_nonneg hlog.1]
    have h0 := mul_le_mul_of_nonneg_left hrem (Nat.cast_nonneg s)
    have h1 := mul_le_mul_of_nonneg_left hlog.2 (Nat.cast_nonneg k)
    have hα1 : |α| ≤ 1 := hα.trans (by norm_num)
    have hα2 : α^2≤1 := (sq_le_one_iff_abs_le_one α).mpr hα1
    have hkR : (k:ℝ)≤s := by exact_mod_cast hks
    have hsquare : (α*(u-y))^2≤(u-y)^2 := by
      nlinarith [mul_le_mul_of_nonneg_right hα2 (sq_nonneg (u-y))]
    have hweighted := mul_le_mul_of_nonneg_left hsquare
      (by positivity : 0≤2*(k:ℝ))
    have hdegree := mul_le_mul_of_nonneg_right hkR (sq_nonneg (u-y))
    nlinarith [sq_nonneg (u-y)]
  have hlow := Real.add_one_le_exp (Real.log (matchedEnvelope F F₁ s m k y u))
  rw [Real.exp_log hpos] at hlow
  have hnonpos := Real.log_nonpos hpos.le hE
  rw [abs_of_nonpos (sub_nonpos.mpr hE),abs_of_nonpos hnonpos] at *
  linarith

end Erdos1152.V5
