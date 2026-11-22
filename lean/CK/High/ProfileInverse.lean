module

public import CK.High.CostGeometryBase
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Explicit height-profile inverse bounds on real intervals. An exponential change of variables gives rational and logarithmic formulas. -/

@[expose] public section
set_option autoImplicit false
open Set Filter
open scoped Topology
namespace CK
noncomputable section

def heightDecayRate (v : ℝ) : ℝ :=
  (1-Real.tanh v^2)*Profile.profileAux (Real.tanh v)/
    (Real.tanh v*Profile.meanEntropy (Real.tanh v))

theorem hasDerivAt_heightF {v : ℝ} (hv : 0 < v) :
    HasDerivAt heightF (-heightDecayRate v*heightF v) v := by
  have ht := tanh_mem_Ioo_positive hv
  have h := (Profile.hasDerivAt_entropy_ratio ht).comp v (hasDerivAt_tanh_squared v)
  apply h.congr_deriv
  unfold heightDecayRate heightF
  field_simp [ht.1.ne', (Profile.meanEntropy_pos ⟨by linarith [ht.1],ht.2⟩).ne']

theorem hasDerivAt_log_heightF {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun v => Real.log (heightF v)) (-heightDecayRate v) v := by
  have h := (hasDerivAt_heightF hv).log (heightF_pos hv).ne'
  apply h.congr_deriv
  field_simp [(heightF_pos hv).ne']

theorem heightDecayRate_eq {v : ℝ} (hv : 0 < v) :
    heightDecayRate v=1/Real.tanh v-
      Profile.entropyHyperbolicSlope (Real.tanh v)/Profile.meanEntropy (Real.tanh v) := by
  have ht := tanh_mem_Ioo_positive hv
  have hd : Real.tanh v ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1],ht.2⟩
  unfold heightDecayRate
  rw [Profile.entropyHyperbolicSlope_eq hd,
    show Profile.profileAux (Real.tanh v)=Profile.meanEntropy (Real.tanh v)+
      Real.tanh v*phiSlope (Real.tanh v) from (Profile.meanEntropy_add_slope hd).symm]
  field_simp [ht.1.ne', (Profile.meanEntropy_pos hd).ne']
  ring

theorem heightDecayRate_gt_one {v : ℝ} (hv : 0 < v) : 1 < heightDecayRate v := by
  have ht := tanh_mem_Ioo_positive hv
  have hh := Profile.meanEntropy_pos ⟨by linarith [ht.1],ht.2⟩
  have hneg := div_nonpos_of_nonpos_of_nonneg
    (Profile.entropyHyperbolicSlope_nonpos ⟨ht.1.le,ht.2.le⟩) hh.le
  have hrec : 1 < 1/Real.tanh v := (lt_div_iff₀ ht.1).mpr (by simpa using ht.2)
  rw [heightDecayRate_eq hv]
  linarith only [hneg,hrec]

theorem heightF_strictAnti : StrictAntiOn heightF (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg
    (f' := fun v => -heightDecayRate v*heightF v) (convex_Ioi _)
  · intro v hv
    exact (hasDerivAt_heightF hv).continuousAt.continuousWithinAt
  · intro v hv
    exact (hasDerivAt_heightF (by simpa using hv)).hasDerivWithinAt
  · intro v hv
    have hv0 : 0 < v := by simpa using hv
    exact mul_neg_of_neg_of_pos (by linarith [heightDecayRate_gt_one hv0]) (heightF_pos hv0)

def heightExpParameter (v : ℝ) : ℝ := Real.exp (-2*v)
def scaledHeightF (v : ℝ) : ℝ := Real.exp (2*v)*heightF v
def scaledHeightFSlope (v : ℝ) : ℝ :=
  2*((1-2*heightExpParameter v-heightExpParameter v^2)*
      (Real.log (1+heightExpParameter v)/heightExpParameter v)-2*v*heightExpParameter v)/
    (1-heightExpParameter v)^2

theorem heightExpParameter_bounds {v : ℝ} (hv : 0 < v) :
    heightExpParameter v ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨Real.exp_pos _,?_⟩
  change Real.exp (-2*v) < 1
  exact Real.exp_lt_one_iff.mpr (by linarith only [hv])

theorem tanh_eq_heightExpParameter (v : ℝ) :
    Real.tanh v=(1-heightExpParameter v)/(1+heightExpParameter v) := by
  have hq : heightExpParameter v=(Real.exp v)⁻¹^2 := by
    unfold heightExpParameter
    rw [show -2*v=(-v)+(-v) by ring,Real.exp_add,Real.exp_neg]
    ring
  rw [hq,Real.tanh_eq,Real.exp_neg]
  field_simp

theorem meanEntropy_tanh_exp_formula (v : ℝ) :
    Profile.meanEntropy (Real.tanh v)=Real.log (1+heightExpParameter v)+
      2*v*heightExpParameter v/(1+heightExpParameter v) := by
  have hq : 0 < heightExpParameter v := Real.exp_pos _
  have h1 : 0 < 1+heightExpParameter v := by positivity
  rw [Profile.meanEntropy,tanh_eq_heightExpParameter,
    show (1-(1-heightExpParameter v)/(1+heightExpParameter v))/2 =
      heightExpParameter v/(1+heightExpParameter v) by field_simp; ring]
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    show 1-heightExpParameter v/(1+heightExpParameter v)=1/(1+heightExpParameter v) by field_simp; ring]
  simp only [Real.negMulLog_eq_neg,
    Real.log_div hq.ne' h1.ne',one_div,Real.log_inv]
  rw [show Real.log (heightExpParameter v)=-2*v by unfold heightExpParameter; rw [Real.log_exp]]
  field_simp
  ring

theorem scaledHeightF_exp_formula {v : ℝ} (hv : 0 < v) :
    scaledHeightF v=((1+heightExpParameter v)*
      (Real.log (1+heightExpParameter v)/heightExpParameter v)+2*v)/(1-heightExpParameter v) := by
  have hq := heightExpParameter_bounds hv
  have he : Real.exp (2*v)=(heightExpParameter v)⁻¹ := by
    unfold heightExpParameter
    rw [show -2*v=-(2*v) by ring,Real.exp_neg,inv_inv]
  rw [scaledHeightF,he,heightF,meanEntropy_tanh_exp_formula,tanh_eq_heightExpParameter]
  field_simp [hq.1.ne',ne_of_gt (by linarith [hq.2] : 0 < 1-heightExpParameter v),
    ne_of_gt (by linarith [hq.1] : 0 < 1+heightExpParameter v)]

theorem hasDerivAt_heightExpParameter (v : ℝ) :
    HasDerivAt heightExpParameter (-2*heightExpParameter v) v := by
  apply (((hasDerivAt_id v).const_mul (-2)).exp).congr_deriv
  dsimp [heightExpParameter]
  ring

theorem hasDerivAt_scaledHeightF {v : ℝ} (hv : 0 < v) :
    HasDerivAt scaledHeightF (scaledHeightFSlope v) v := by
  have hq := heightExpParameter_bounds hv
  have hp : 0 < 1+heightExpParameter v := by linarith [hq.1]
  have hm : 0 < 1-heightExpParameter v := by linarith [hq.2]
  have hd := hasDerivAt_heightExpParameter v
  have hlog := (hd.const_add 1).log hp.ne'
  have hL := hlog.div hd hq.1.ne'
  have h := (((hd.const_add 1).mul hL).add ((hasDerivAt_id v).const_mul 2)).div
    (hd.const_sub 1) hm.ne'
  have h' : HasDerivAt (fun v => ((1+heightExpParameter v)*
      (Real.log (1+heightExpParameter v)/heightExpParameter v)+2*v)/(1-heightExpParameter v))
      (scaledHeightFSlope v) v := by
    apply h.congr_deriv
    unfold scaledHeightFSlope
    dsimp only [id_eq,Pi.mul_apply,Pi.add_apply,Pi.div_apply]
    field_simp [hq.1.ne',hp.ne',hm.ne']
    ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hv] with w hw
  exact scaledHeightF_exp_formula hw

theorem scaledHeightFSlope_eq {v : ℝ} (hv : 0 < v) :
    scaledHeightFSlope v=(2-heightDecayRate v)*scaledHeightF v := by
  have h := (((hasDerivAt_id v).const_mul 2).exp).mul (hasDerivAt_heightF hv)
  have heq := (hasDerivAt_scaledHeightF hv).unique h
  dsimp only [id_eq] at heq
  dsimp [scaledHeightF]
  nlinarith only [heq]

theorem log_one_add_second_lower {q : ℝ} (hq : 0 ≤ q) :
    q-q^2/2 ≤ Real.log (1+q) := by
  have hl := Real.le_log_one_add_of_nonneg hq
  have hden : 0 < q+2 := by positivity
  have hpoly : q-q^2/2 ≤ 2*q/(q+2) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [pow_nonneg hq 3]
  exact hpoly.trans hl

theorem log_one_add_ratio_bounds {q : ℝ} (hq : 0 < q) :
    1-q/2 ≤ Real.log (1+q)/q ∧ Real.log (1+q)/q ≤ 1 := by
  constructor
  · apply (le_div_iff₀ hq).mpr
    nlinarith only [log_one_add_second_lower hq.le]
  · apply (div_le_iff₀ hq).mpr
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1+q)
    linarith only [h]

theorem scaledHeightF_bounds {v : ℝ} (hv : 0 < v) :
    2*v+1 ≤ scaledHeightF v ∧
      scaledHeightF v ≤ ((1+heightExpParameter v)/(1-heightExpParameter v))*(2*v+1) := by
  have hq := heightExpParameter_bounds hv
  have hm : 0 < 1-heightExpParameter v := by linarith [hq.2]
  have hp : 0 < 1+heightExpParameter v := by linarith [hq.1]
  have hL := log_one_add_ratio_bounds hq.1
  rw [scaledHeightF_exp_formula hv]
  constructor
  · apply (le_div_iff₀ hm).mpr
    have hprod := mul_le_mul_of_nonneg_left hL.1 hp.le
    have hqprod := mul_nonneg hq.1.le (sub_nonneg.mpr hq.2.le)
    have hvprod := mul_nonneg hv.le hq.1.le
    nlinarith only [hprod,hqprod,hvprod,hq.1.le]
  · apply (div_le_iff₀ hm).mpr
    have hprod := mul_le_mul_of_nonneg_left hL.2 hp.le
    have hvprod := mul_nonneg hv.le hq.1.le
    have hid : ((1+heightExpParameter v)/(1-heightExpParameter v))*(2*v+1)*
        (1-heightExpParameter v)=(1+heightExpParameter v)*(2*v+1) := by field_simp
    rw [hid]
    nlinarith only [hprod,hvprod]

theorem exp_neg_four_lt_one_fiftieth : Real.exp (-4 : ℝ) < 1/50 := by
  have h1 : (27/10 : ℝ) < Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10) h1.le 4
  have he : Real.exp (1 : ℝ)^4=Real.exp 4 := by
    rw [←Real.exp_natCast_mul]
    norm_num
  rw [he] at hp
  have h50 : (50 : ℝ) < Real.exp 4 := by norm_num at hp; linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 50) h50

theorem heightExpParameter_small {v : ℝ} (hv : (2 : ℝ) ≤ v) :
    0 < heightExpParameter v ∧ heightExpParameter v < 1/50 ∧
      v*heightExpParameter v < 1/25 := by
  have hv0 : 0 < v := by linarith
  have hq : heightExpParameter v ≤ Real.exp (-4) :=
    Real.exp_le_exp.mpr (by linarith : -2*v ≤ -4)
  have hd (s : ℝ) : HasDerivAt (fun t => t*heightExpParameter t)
      ((1-2*s)*heightExpParameter s) s := by
    apply ((hasDerivAt_id s).mul (hasDerivAt_heightExpParameter s)).congr_deriv
    dsimp
    ring
  have hanti : AntitoneOn (fun t => t*heightExpParameter t) (Ici (2 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun s => (1-2*s)*heightExpParameter s)
      (convex_Ici _)
    · intro s _
      exact (hd s).continuousAt.continuousWithinAt
    · intro s _
      exact (hd s).hasDerivWithinAt
    · intro s hs
      have hs' : (2 : ℝ) < s := by simpa using hs
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
  have hprod := hanti (by simp : (2 : ℝ) ∈ Ici 2) hv hv
  have hb : (2 : ℝ)*heightExpParameter 2 < 1/25 := by
    norm_num [heightExpParameter] at *
    linarith only [exp_neg_four_lt_one_fiftieth]
  exact ⟨Real.exp_pos _,hq.trans_lt exp_neg_four_lt_one_fiftieth,hprod.trans_lt hb⟩

theorem scaledHeightFSlope_bounds {v : ℝ} (hv : (2 : ℝ) ≤ v) :
    (7/4 : ℝ) < scaledHeightFSlope v ∧ scaledHeightFSlope v < 2 := by
  have hv0 : 0 < v := by linarith
  have hq := heightExpParameter_small hv
  have hL := log_one_add_ratio_bounds hq.1
  have hq2 : heightExpParameter v^2 ≤ (1/50 : ℝ)^2 :=
    pow_le_pow_left₀ hq.1.le hq.2.1.le 2
  have hA : 0 ≤ 1-2*heightExpParameter v-heightExpParameter v^2 := by
    nlinarith only [hq.2.1.le,hq2]
  have hlow := mul_le_mul_of_nonneg_left hL.1 hA
  have hupp := mul_le_mul_of_nonneg_left hL.2 hA
  have hm : 0 < 1-heightExpParameter v := by linarith [hq.2.1]
  have hden : 0 < (1-heightExpParameter v)^2 := sq_pos_of_pos hm
  unfold scaledHeightFSlope
  constructor
  · apply (lt_div_iff₀ hden).mpr
    nlinarith only [hlow,hq.2.1,hq.2.2,hq2,pow_nonneg hq.1.le 3]
  · apply (div_lt_iff₀ hden).mpr
    nlinarith only [hupp,mul_pos hv0 hq.1,sq_nonneg (heightExpParameter v)]

theorem scaledHeightF_pos {v : ℝ} (hv : 0 < v) : 0 < scaledHeightF v :=
  mul_pos (Real.exp_pos _) (heightF_pos hv)

theorem scaledHeightF_upper_seven_fourths {v : ℝ} (hv : (2 : ℝ) ≤ v) :
    scaledHeightF v < (7/4)*(2*v+1) := by
  have hq := heightExpParameter_small hv
  have hv0 : 0 < v := by linarith
  have hr : (1+heightExpParameter v)/(1-heightExpParameter v) < (7/4 : ℝ) := by
    apply (div_lt_iff₀ (by linarith [hq.2.1] : 0 < 1-heightExpParameter v)).mpr
    linarith only [hq.2.1]
  exact (scaledHeightF_bounds hv0).2.trans_lt
    (mul_lt_mul_of_pos_right hr (by linarith : 0 < 2*v+1))

theorem scaledHeightF_logSlope_bounds {v : ℝ} (hv : (2 : ℝ) ≤ v) :
    1 < (2*v+1)*scaledHeightFSlope v/scaledHeightF v ∧
      (2*v+1)*scaledHeightFSlope v/scaledHeightF v < 2 := by
  have hv0 : 0 < v := by linarith
  have hp := scaledHeightF_pos hv0
  have hd := scaledHeightFSlope_bounds hv
  have hmullo := mul_lt_mul_of_pos_left hd.1 (by linarith : 0 < 2*v+1)
  have hmulhi := mul_lt_mul_of_pos_left hd.2 (by linarith : 0 < 2*v+1)
  constructor
  · apply (lt_div_iff₀ hp).mpr
    nlinarith only [hmullo,scaledHeightF_upper_seven_fourths hv]
  · apply (div_lt_iff₀ hp).mpr
    nlinarith only [hmulhi,(scaledHeightF_bounds hv0).1]

theorem heightDecayRate_bounds {v : ℝ} (hv : (2 : ℝ) ≤ v) :
    2-2/(2*v+1) < heightDecayRate v ∧ heightDecayRate v < 2-1/(2*v+1) := by
  have hv0 : 0 < v := by linarith
  have hp := scaledHeightF_pos hv0
  have hden : 0 < 2*v+1 := by linarith
  have h := scaledHeightF_logSlope_bounds hv
  have hid : (2*v+1)*scaledHeightFSlope v/scaledHeightF v=(2*v+1)*(2-heightDecayRate v) := by
    rw [scaledHeightFSlope_eq hv0]
    field_simp
  rw [hid] at h
  have htwo : (2/(2*v+1))*(2*v+1)=(2 : ℝ) := by field_simp
  have hone : (1/(2*v+1))*(2*v+1)=(1 : ℝ) := by field_simp
  constructor
  · nlinarith only [h.2,htwo,hden]
  · nlinarith only [h.1,hone,hden]

theorem heightDecayRate_gt_seven_fourths {v : ℝ} (hv : (4 : ℝ) ≤ v) :
    (7/4 : ℝ) < heightDecayRate v := by
  have h := (heightDecayRate_bounds (by linarith : (2 : ℝ) ≤ v)).1
  have hfrac : 2/(2*v+1) < (1/4 : ℝ) := by
    apply (div_lt_iff₀ (by linarith : 0 < 2*v+1)).mpr
    linarith only [hv]
  linarith only [h,hfrac]

end
end CK
