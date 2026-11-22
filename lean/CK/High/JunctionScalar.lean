module

public import CK.High.ExponentialScalar
public import CK.Low.LocalIntervals

/-! A continuous, uniform proof of the local junction with constant `3/2`.
The additional probability strip is proved by monotonicity of an explicit
logarithmic lower bound; no general local-propagation assumption is used. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def junctionProbability (d : ℝ) : ℝ := 4*d^2/(9+4*d^2)

def junctionLower (d p : ℝ) : ℝ :=
  2*(1-p)*(-Real.log d+1-d)-(1+2*p/d)*(-Real.log p+1)

theorem log_sixtyfour_bounds : (4 : ℝ) ≤ Real.log 64 ∧ Real.log 64 ≤ 1041/250 := by
  have h : Real.log (64 : ℝ)=6*Real.log 2 := by
    rw [show (64 : ℝ)=2^6 by norm_num,Real.log_pow]
    norm_num
  rw [h]
  constructor <;> linarith [Certificate.log_two_coarse_bounds.1,
    Certificate.log_two_coarse_bounds.2]

theorem log_nine_quarters_bounds : (0 : ℝ) ≤ Real.log (9/4) ∧
    Real.log (9/4 : ℝ) ≤ 407/500 := by
  constructor
  · exact Real.log_nonneg (by norm_num)
  · have h : Real.log (9/4 : ℝ)=Real.log 9-2*Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num),show (4 : ℝ)=2^2 by norm_num,
        Real.log_pow]
      norm_num
    rw [h]
    linarith [log_nine_bounds.2,Certificate.log_two_coarse_bounds.1]

theorem junction_delta_log_bounds {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64)) :
    4 ≤ -Real.log d ∧ d*(-Real.log d) ≤ 1041/16000 ∧
      d^2*(-Real.log d) ≤ 1041/1024000 := by
  have hlog := Real.log_le_log hd.1 hd.2
  rw [one_div,Real.log_inv] at hlog
  have hu : 4 ≤ -Real.log d := by linarith [log_sixtyfour_bounds.1]
  have hd0 : 0 < d := hd.1
  have hl := Real.one_sub_inv_le_log_of_pos (show 0 < 64*d by positivity)
  rw [Real.log_mul (by norm_num) hd.1.ne'] at hl
  have hm := mul_le_mul_of_nonneg_left hl hd.1.le
  have he : d*(1-(64*d)⁻¹)=d-1/64 := by
    field_simp [hd.1.ne']
    <;> ring
  rw [he] at hm
  have hm2 := mul_le_mul_of_nonneg_left hd.2
    (show 0 ≤ Real.log 64-1 by linarith [log_sixtyfour_bounds.1])
  have hb : d*(-Real.log d) ≤ 1041/16000 := by
    nlinarith only [hm,hm2,log_sixtyfour_bounds.2]
  have hmul := mul_le_mul_of_nonneg_left hb hd.1.le
  exact ⟨hu,hb,by nlinarith only [hmul,hd.2]⟩

theorem junctionProbability_bounds {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64)) :
    0 < junctionProbability d ∧ junctionProbability d ≤ (4/9)*d^2 ∧
      junctionProbability d ≤ d^2 := by
  have hden : 0 < 9+4*d^2 := by positivity
  have hb : junctionProbability d ≤ (4/9)*d^2 := by
    unfold junctionProbability
    apply (div_le_iff₀ hden).2
    nlinarith only [sq_nonneg (d^2)]
  exact ⟨div_pos (mul_pos (by norm_num) (sq_pos_of_pos hd.1)) hden,hb,by nlinarith only [hb,sq_nonneg d]⟩

theorem junctionProbability_log_bound {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64)) :
    -Real.log (junctionProbability d) ≤
      2*(-Real.log d)+Real.log (9/4)+(4/9)*d^2 := by
  have he : junctionProbability d=d^2/((9/4)*(1+(4/9)*d^2)) := by
    unfold junctionProbability
    field_simp
    <;> ring
  rw [he,Real.log_div (ne_of_gt (sq_pos_of_pos hd.1)) (by positivity),
    Real.log_mul (by norm_num) (by positivity),Real.log_pow]
  have hl := Real.log_le_sub_one_of_pos (show 0 < 1+(4/9)*d^2 by positivity)
  norm_num at *
  linarith

theorem junction_margin {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64)) :
    (1/80 : ℝ) < 1-Real.log (9/4)-
      d*(2+(8/9)*(2*(-Real.log d)+Real.log (9/4)+1))-
      (4*d^2/9)*(2*(-Real.log d)+3) := by
  obtain ⟨hu,hdu,hddu⟩ := junction_delta_log_bounds hd
  have hd2 : d^2 ≤ (1/64 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  have hc := mul_le_mul_of_nonneg_left log_nine_quarters_bounds.2 hd.1.le
  nlinarith only [hd.2,hd2,hdu,hddu,hc,log_nine_quarters_bounds.2]

theorem junctionLower_endpoint {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64)) :
    (1/80 : ℝ) < junctionLower d (junctionProbability d) := by
  let p := junctionProbability d
  let u := -Real.log d
  let C := Real.log (9/4)
  have hp := junctionProbability_bounds hd
  have hu : 4 ≤ u := (junction_delta_log_bounds hd).1
  have hA : 0 ≤ u+1-d := by linarith [hd.2]
  have hB : 0 ≤ 2*u+C+(4/9)*d^2+1 := by
    dsimp [C]
    nlinarith only [hu,log_nine_quarters_bounds.1,sq_nonneg d]
  have hmul1 := mul_le_mul_of_nonneg_right hp.2.1 hA
  have hcoef : 1+2*p/d ≤ 1+(8/9)*d := by
    have hf : 2*p/d ≤ (8/9)*d := (div_le_iff₀ hd.1).2 (by
      dsimp [p]
      nlinarith only [hp.2.1])
    linarith only [hf]
  have hlog := junctionProbability_log_bound hd
  have hc0 : 0 ≤ 1+2*p/d := by
    have hf := div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp.1.le) hd.1.le
    dsimp [p]
    linarith only [hf]
  have hmul2 := mul_le_mul_of_nonneg_left (show -Real.log p+1 ≤
    2*u+C+(4/9)*d^2+1 by dsimp [p,u,C]; linarith only [hlog]) hc0
  have hmul3 := mul_le_mul_of_nonneg_right hcoef hB
  have hpoly : 1-C-d*(2+(8/9)*(2*u+C+1))-(4*d^2/9)*(2*u+3) ≤
      2*(1-(4/9)*d^2)*(u+1-d)-(1+(8/9)*d)*(2*u+C+(4/9)*d^2+1) := by
    nlinarith only [pow_nonneg hd.1.le 3]
  have hmargin := junction_margin hd
  change (1/80 : ℝ) < 1-C-d*(2+(8/9)*(2*u+C+1))-(4*d^2/9)*(2*u+3) at hmargin
  change (1/80 : ℝ) < junctionLower d p
  unfold junctionLower
  change (1/80 : ℝ) < 2*(1-p)*(u+1-d)-(1+2*p/d)*(-Real.log p+1)
  nlinarith only [hmul1,hmul2,hmul3,hpoly,hmargin]

def junctionSlope (d p : ℝ) : ℝ :=
  1/p+(2/d)*Real.log p-2*(-Real.log d+1-d)

theorem hasDerivAt_junctionLower {d p : ℝ} (hd : 0 < d) (hp : 0 < p) :
    HasDerivAt (junctionLower d) (junctionSlope d p) p := by
  have h := ((((hasDerivAt_const p 1).sub (hasDerivAt_id p)).const_mul 2).mul_const
    (-Real.log d+1-d)).sub
    (((hasDerivAt_const p 1).add (((hasDerivAt_id p).const_mul 2).div_const d)).mul
      ((Real.hasDerivAt_log hp.ne').neg.add_const 1))
  apply h.congr_deriv
  dsimp [junctionSlope]
  field_simp [hd.ne',hp.ne']
  <;> ring

theorem junctionSlope_pos {d p : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64))
    (hp : p ∈ Icc (junctionProbability d) (d^2)) : 0 < junctionSlope d p := by
  let u := -Real.log d
  have hp0 : 0 < p := (junctionProbability_bounds hd).1.trans_le hp.1
  obtain ⟨hu,hdu,hddu⟩ := junction_delta_log_bounds hd
  change 4 ≤ u at hu
  change d*u ≤ 1041/16000 at hdu
  change d^2*u ≤ 1041/1024000 at hddu
  have hd2 : d^2 ≤ (1/64 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  have hl := Real.log_le_log (junctionProbability_bounds hd).1 hp.1
  have hl2 := junctionProbability_log_bound hd
  have hlp : -Real.log p ≤ 2*u+1 := by
    dsimp [u]
    linarith only [hl,hl2,hd2,log_nine_quarters_bounds.2]
  have hpd : 2*p/d ≤ 2*d := (div_le_iff₀ hd.1).2 (by nlinarith only [hp.2])
  have hcoef0 : 0 ≤ 2*p/d := div_nonneg (by positivity) hd.1.le
  have hm1 := mul_le_mul_of_nonneg_left hlp hcoef0
  have hm2 := mul_le_mul_of_nonneg_right hpd (show 0 ≤ 2*u+1 by linarith)
  have hm3 := mul_le_mul_of_nonneg_right hp.2 (show 0 ≤ u+1 by linarith)
  have hmargin : 0 < 1-2*d*(2*u+1)-2*d^2*(u+1) := by
    nlinarith only [hdu,hddu,hd.2,hd2]
  have hid : p*junctionSlope d p=1-(2*p/d)*(-Real.log p)-2*p*(u+1-d) := by
    unfold junctionSlope
    dsimp [u]
    field_simp [hp0.ne',hd.1.ne']
    <;> ring
  have hpos : 0 < p*junctionSlope d p := by
    rw [hid]
    have hpd0 := mul_nonneg hp0.le hd.1.le
    nlinarith only [hm1,hm2,hm3,hmargin,hpd0]
  exact (mul_pos_iff_of_pos_left hp0).mp hpos

theorem junctionLower_mono {d : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64)) :
    MonotoneOn (junctionLower d) (Icc (junctionProbability d) (d^2)) := by
  have hf (p : ℝ) (hp : p ∈ Icc (junctionProbability d) (d^2)) :=
    hasDerivAt_junctionLower hd.1 ((junctionProbability_bounds hd).1.trans_le hp.1)
  exact monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
    (fun p hp => (hf p hp).continuousAt.continuousWithinAt)
    (fun p hp => (hf p (interior_subset hp)).hasDerivWithinAt)
    (fun p hp => (junctionSlope_pos hd (interior_subset hp)).le)

theorem localDeficit_junction_strip {d p : ℝ} (hd : d ∈ Ioc (0 : ℝ) (1/64))
    (hp : p ∈ Icc (junctionProbability d) (d^2)) :
    0 < localDeficit (1-2*p) (1-2*d) := by
  have hp0 : 0 < p := (junctionProbability_bounds hd).1.trans_le hp.1
  have hd2 : d^2 ≤ (1/64 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  have hp1 : p < 1 := by linarith [hp.2]
  have hq0 : d ≤ d+p*(1-2*d) := by
    have h := mul_nonneg hp0.le (show 0 ≤ 1-2*d by linarith [hd.2])
    linarith only [h]
  have hq1 : d+p*(1-2*d) ≤ 1/2 := by
    have hpd := mul_nonneg hp0.le hd.1.le
    nlinarith only [hd.2,hd2,hp.2,hpd]
  have hbase := binEntropy_lower_log
    (show d ∈ Ico (0 : ℝ) 1 by exact ⟨hd.1.le,by linarith [hd.2]⟩)
  have hq := Real.binEntropy_strictMonoOn.monotoneOn
    (show d ∈ Icc (0 : ℝ) 2⁻¹ by constructor; exact hd.1.le; norm_num; linarith [hd.2])
    (show d+p*(1-2*d) ∈ Icc (0 : ℝ) 2⁻¹ by constructor; exact hd.1.le.trans hq0; norm_num; exact hq1) hq0
  have hEntropy := hbase.trans hq
  have hpEntropy := binEntropy_upper_log ⟨hp0.le,hp1⟩
  have hB : 0 ≤ -Real.log p+1 := by
    have hl := Real.log_nonpos hp0.le hp1.le
    linarith only [hl]
  have hcoef0 : 0 ≤ 2*d+4*p*(1-p)*(1-2*d) := by
    have hcomp : 0 ≤ 1-p := by linarith
    have hd0 : 0 ≤ d := hd.1.le
    have hfac : 0 ≤ 1-2*d := by linarith [hd.2]
    positivity
  have hcoef : 2*d+4*p*(1-p)*(1-2*d) ≤ 2*d+4*p := by
    have hfac : (1-p)*(1-2*d) ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left (show 1-2*d ≤ 1 by linarith [hd.1])
        (show 0 ≤ 1-p by linarith)
      nlinarith only [hm,hp0]
    have hm := mul_le_mul_of_nonneg_left hfac (show 0 ≤ 4*p by positivity)
    linarith only [hm]
  have hcomp : 0 ≤ 1-p := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hEntropy
    (show 0 ≤ 4*p*(1-p) by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hpEntropy hcoef0
  have hm3 := mul_le_mul_of_nonneg_right hcoef (mul_nonneg hp0.le hB)
  have hlower : (1/80 : ℝ) < junctionLower d p :=
    (junctionLower_endpoint hd).trans_le (junctionLower_mono hd
      ⟨le_rfl,(junctionProbability_bounds hd).2.2⟩ hp hp.1)
  have hpos : 0 < 2*d*p*junctionLower d p :=
    mul_pos (mul_pos (mul_pos (by norm_num) hd.1) hp0) (by linarith)
  have hid : 2*d*p*junctionLower d p=
      4*p*(1-p)*(d*(-Real.log d+1-d))-(2*d+4*p)*(p*(-Real.log p+1)) := by
    unfold junctionLower
    field_simp [hd.1.ne']
    <;> ring
  rw [hid] at hpos
  unfold localDeficit signEntropy
  rw [show (1-(1-2*p)*(1-2*d))/2=d+p*(1-2*d) by ring,
    show (1-(1-2*p))/2=p by ring]
  nlinarith only [hm1,hm2,hm3,hpos]

/-- The local-junction interval, including zero correlation. The upper local threshold controls the large-probability part and the exponential estimate controls the intermediate part. -/
theorem localDeficit_junction_parameter {d p : ℝ}
    (hd : d ∈ Ioc (0 : ℝ) (1/64))
    (hp : p ∈ Icc (junctionProbability d) (1/2)) :
    0 ≤ localDeficit (1-2*p) (1-2*d) := by
  have hp0 : 0 < p := (junctionProbability_bounds hd).1.trans_le hp.1
  have hr : 1-2*p ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2],by linarith⟩
  by_cases hlarge : (1/100 : ℝ) ≤ p
  · exact localDeficit_nonneg_of_threshold hr (by norm_num)
      (show 1-2*d ∈ Icc (76043/100000 : ℝ) 1 by constructor <;> linarith [hd.1,hd.2])
      (localDeficit_threshold_upper_interval ⟨hr.1,by linarith⟩)
  have hpSmall : p < (1/100 : ℝ) := lt_of_not_ge hlarge
  by_cases hstrip : p ≤ d^2
  · exact (localDeficit_junction_strip hd ⟨hp.1,hstrip⟩).le
  have hdp : d^2 ≤ p := (lt_of_not_ge hstrip).le
  let e := Real.sqrt (p/(1-p))
  have hcomp : 0 < 1-p := by linarith
  have he0 : 0 < e := Real.sqrt_pos.mpr (div_pos hp0 hcomp)
  have he2 : e^2=p/(1-p) := Real.sq_sqrt (div_nonneg hp0.le hcomp.le)
  have hepoly : e^2*(1-p)=p := by rw [he2]; field_simp
  have heUpper : e ≤ (1/9 : ℝ) := by
    have hb : p/(1-p) ≤ (1/9 : ℝ)^2 := (div_le_iff₀ hcomp).mpr (by nlinarith only [hpSmall])
    nlinarith only [he2,hb,he0]
  have hde : d ≤ e := by
    have hb : p ≤ e^2 := by
      have hm := mul_nonneg (sq_nonneg e) hp0.le
      nlinarith only [hepoly,hm]
    nlinarith only [hdp,hb,he0,hd.1]
  have heProb : localNoiseProbability e=p := by
    unfold localNoiseProbability
    apply (div_eq_iff (show 1+e^2 ≠ 0 by positivity)).mpr
    nlinarith only [hepoly]
  have heDomain : e ∈ Ioc (0 : ℝ) (1/9) := ⟨he0,heUpper⟩
  have heM := localDeficit_exponential_parameter heDomain
  rw [heProb] at heM
  exact localDeficit_nonneg_of_threshold hr
    (show 1-2*e ∈ Icc (0 : ℝ) 1 by constructor <;> linarith)
    (show 1-2*d ∈ Icc (1-2*e) 1 by constructor <;> linarith [hd.1]) heM.le

end
end CK
