module

public import CK.Low.Local
public import CK.Certificate.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Elementary binary-entropy estimates with all logarithm domains explicit,
for the exponential neighborhood of a dictator. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem log_nine_bounds : (2 : ℝ) ≤ Real.log 9 ∧ Real.log 9 ≤ 11/5 := by
  have h := Certificate.logCertificate_sound (q := 3) (lower := 1) (upper := 11/10)
    (n := 5) (by norm_num [Certificate.logCertificate, Certificate.logSeries,
      Certificate.logRemainder, Finset.sum_range_succ])
  norm_num at h
  have h9 : Real.log (9 : ℝ) = 2*Real.log 3 := by
    rw [show (9 : ℝ) = 3^2 by norm_num, Real.log_pow]
    norm_num
  rw [h9]
  constructor <;> linarith [h.1,h.2]

theorem binEntropy_lower_log {p : ℝ} (hp : p ∈ Set.Ico (0 : ℝ) 1) :
    p * (-Real.log p + 1-p) ≤ Real.binEntropy p := by
  have hlog := Real.log_le_sub_one_of_pos (show 0 < 1-p by linarith [hp.2])
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 1-p by linarith [hp.2])
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_eq_neg]
  nlinarith only [hm]

theorem binEntropy_upper_log {p : ℝ} (hp : p ∈ Set.Ico (0 : ℝ) 1) :
    Real.binEntropy p ≤ p * (-Real.log p + 1) := by
  have hpos : 0 < 1-p := by linarith [hp.2]
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hm := mul_le_mul_of_nonneg_left hlog hpos.le
  have he : (1-p)*(1-(1-p)⁻¹) = -p := by
    field_simp
    <;> ring
  rw [he] at hm
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_eq_neg]
  nlinarith only [hm]

theorem small_delta_log_lower {d : ℝ} (hd : d ∈ Set.Ioc (0 : ℝ) (1/9)) :
    2 ≤ -Real.log d := by
  have hl := Real.log_le_log hd.1 hd.2
  have he : Real.log (1/9 : ℝ) = -Real.log 9 := by
    rw [one_div, Real.log_inv]
  rw [he] at hl
  linarith [log_nine_bounds.1]

theorem small_delta_log_product_bound {d : ℝ} (hd : d ∈ Set.Ioc (0 : ℝ) (1/9)) :
    d * (-Real.log d) ≤ Real.log 9 / 9 := by
  have hpos : 0 < 9*d := mul_pos (by norm_num) hd.1
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  rw [Real.log_mul (by norm_num) (ne_of_gt hd.1)] at hl
  have hm := mul_le_mul_of_nonneg_left hl hd.1.le
  have he : d*(1-(9*d)⁻¹) = d-1/9 := by
    field_simp [ne_of_gt hd.1]
    <;> ring
  rw [he] at hm
  have hm2 := mul_le_mul_of_nonneg_left hd.2
    (show 0 ≤ Real.log 9-1 by linarith [log_nine_bounds.1])
  nlinarith only [hm,hm2]

theorem small_delta_margin {d : ℝ} (hd : d ∈ Set.Ioc (0 : ℝ) (1/9)) :
    (17/1000 : ℝ) < 1-(2*(-Real.log d)+4)*d-4*d^2 := by
  have hs : d^2 ≤ (1/9 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  have hl := small_delta_log_product_bound hd
  nlinarith only [hs,hl,hd.2,log_nine_bounds.2]

theorem binEntropy_deriv_small_lower {d x : ℝ}
    (hd : d ∈ Set.Ioc (0 : ℝ) (1/9)) (hx : x ∈ Set.Icc d (d+d^2)) :
    -Real.log d - (7/3)*d ≤ Real.log (1-x) - Real.log x := by
  have hd2 : d^2 ≤ (1/9 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  have hx0 : 0 < x := hd.1.trans_le hx.1
  have hx1 : x < 1 := by nlinarith only [hx.2,hd.2,hd2]
  have hden : 0 < 1-x := sub_pos.2 hx1
  have hpoly : 0 ≤ 1-7*d-4*d^2 := by nlinarith only [hd.2,hd2]
  have hprod := mul_nonneg hd.1.le hpoly
  have hxmul := mul_le_mul_of_nonneg_left hx.2
    (show 0 ≤ 1+(4/3)*d by linarith [hd.1])
  have hfrac : -(4/3)*d ≤ 1-(1-x)⁻¹ := by
    apply (mul_le_mul_iff_left₀ hden).mp
    have hid : (1-(1-x)⁻¹)*(1-x) = -x := by field_simp; ring
    rw [hid]
    nlinarith only [hprod,hxmul]
  have hlower := hfrac.trans (Real.one_sub_inv_le_log_of_pos hden)
  have hupper := Real.log_le_log hx0 hx.2
  have hid : d+d^2 = d*(1+d) := by ring
  rw [hid, Real.log_mul (ne_of_gt hd.1) (by linarith [hd.1])] at hupper
  have hlogadd := Real.log_le_sub_one_of_pos (show 0 < 1+d by linarith [hd.1])
  linarith

end
end CK
