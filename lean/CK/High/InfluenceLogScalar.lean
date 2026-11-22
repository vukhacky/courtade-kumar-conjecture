module

public import CK.High.InfluenceVariance
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Scalar integral majorant underlying the logarithmic influence bound.
The primitive proves the estimate over the entire integration interval. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace CK
noncomputable section

def influenceLogarithmic (a : ℝ) : ℝ := 2*a*(1-a/4)/Real.log (4/a)

def influencePsi (a : ℝ) : ℝ := min (influencePolynomial a) (influenceLogarithmic a)

def influenceLogPrimitive (a s : ℝ) : ℝ :=
  2*a*Real.exp (-Real.log (4/a)*((1-s)/(1+s)))/Real.log (4/a)

def influenceLogDerivative (a s : ℝ) : ℝ :=
  4*a*Real.exp (-Real.log (4/a)*((1-s)/(1+s)))/(1+s)^2

theorem influence_log_pos {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) : 0 < Real.log (4/a) := by
  apply Real.log_pos
  exact (one_lt_div ha.1).2 (by linarith [ha.2])

theorem hasDerivAt_influenceLogPrimitive {a s : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) 1) (hs : 0 ≤ s) :
    HasDerivAt (influenceLogPrimitive a) (influenceLogDerivative a s) s := by
  have hsden : 1+s ≠ 0 := by linarith
  have hL : Real.log (4/a) ≠ 0 := ne_of_gt (influence_log_pos ha)
  have hr := ((hasDerivAt_id s).const_sub 1).div ((hasDerivAt_id s).const_add 1) hsden
  have he := ((hr.const_mul (-Real.log (4/a))).exp.const_mul (2*a)).div_const (Real.log (4/a))
  apply he.congr_deriv
  unfold influenceLogDerivative
  simp only [id_eq,Pi.div_apply]
  field_simp
  <;> ring

theorem log_one_add_ge_chord {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    r*Real.log 2 ≤ Real.log (1+r) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show (2 : ℝ) ∈ Ioi 0 by norm_num)
    (sub_nonneg.mpr hr.2) hr.1 (show (1-r)+r=1 by ring)
  simp only [smul_eq_mul,Real.log_one,mul_zero,zero_add] at h
  convert h using 1 <;> congr 1 <;> ring

theorem influence_rpow_le_logDerivative {a s : ℝ}
    (ha : a ∈ Ioc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    a^(2/(1+s)) ≤ influenceLogDerivative a s := by
  let r := (1-s)/(1+s)
  have hspos : 0 < 1+s := by linarith [hs.1]
  have hr : r ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hs.2) hspos.le
    · exact (div_le_one hspos).2 (by linarith [hs.1])
  have hlog := log_one_add_ge_chord hr
  have hid : 1+r=2/(1+s) := by dsimp [r]; field_simp; ring
  rw [hid,Real.log_div (by norm_num) (ne_of_gt hspos)] at hlog
  have h4 : Real.log (4 : ℝ)=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  have hmain : Real.log a*(2/(1+s)) ≤
      Real.log (4*a) - Real.log (4/a)*r - Real.log ((1+s)^2) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt ha.1),Real.log_div (by norm_num) (ne_of_gt ha.1),
      Real.log_pow,h4,← hid]
    norm_num
    nlinarith only [hlog]
  have hexp := Real.exp_le_exp.mpr hmain
  rw [Real.rpow_def_of_pos ha.1]
  have he : Real.exp (Real.log (4*a)-Real.log (4/a)*r-Real.log ((1+s)^2)) =
      influenceLogDerivative a s := by
    rw [Real.exp_sub,Real.exp_sub,Real.exp_log (sq_pos_of_pos hspos),
      Real.exp_log (mul_pos (by norm_num) ha.1)]
    unfold influenceLogDerivative
    dsimp [r]
    rw [neg_mul,Real.exp_neg]
    ring
  rw [he] at hexp
  exact hexp

theorem influenceLogPrimitive_endpoints {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    influenceLogPrimitive a 1-influenceLogPrimitive a 0 = influenceLogarithmic a := by
  have ha0 : a ≠ 0 := ne_of_gt ha.1
  have h4 : 0 < 4/a := div_pos (by norm_num) ha.1
  unfold influenceLogPrimitive influenceLogarithmic
  norm_num
  rw [Real.exp_neg,Real.exp_log h4]
  field_simp
  <;> ring

theorem influenceLogDerivative_continuousOn {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    ContinuousOn (influenceLogDerivative a) (Icc (0 : ℝ) 1) := by
  apply ContinuousOn.div
  · apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.rexp
    apply ContinuousOn.mul continuousOn_const
    exact (continuousOn_const.sub continuousOn_id).div
      (continuousOn_const.add continuousOn_id) (fun s hs => by linarith [hs.1])
  · exact (continuousOn_const.add continuousOn_id).pow 2
  · intro s hs
    have h : 0 < 1+s := by linarith [hs.1]
    exact ne_of_gt (sq_pos_of_pos h)

theorem integral_influenceLogDerivative {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..1, influenceLogDerivative a s) = influenceLogarithmic a := by
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (influenceLogPrimitive a) (influenceLogDerivative a s) s := by
    intro s hs
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    exact hasDerivAt_influenceLogPrimitive ha hs.1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · exact influenceLogPrimitive_endpoints ha
  · apply (influenceLogDerivative_continuousOn ha).intervalIntegrable_of_Icc
    norm_num

theorem influenceLogarithmic_zero : influenceLogarithmic 0 = 0 := by simp [influenceLogarithmic]

theorem influenceLogarithmic_nonneg {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    0 ≤ influenceLogarithmic a := by
  rcases eq_or_lt_of_le ha.1 with hz | hp
  · rw [← hz,influenceLogarithmic_zero]
  · unfold influenceLogarithmic
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha.1) (by linarith [ha.2]))
      (influence_log_pos ⟨hp,ha.2⟩).le

theorem influenceLogarithmic_monotoneOn : MonotoneOn influenceLogarithmic (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases ha0 : a=0
  · rw [ha0,influenceLogarithmic_zero]
    exact influenceLogarithmic_nonneg hb
  · have hap : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have hbp : 0 < b := hap.trans_le hab
    have hnum : 2*a*(1-a/4) ≤ 2*b*(1-b/4) := by
      have h := mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ 4-a-b by linarith [ha.2,hb.2])
      nlinarith only [h]
    have hnum0 : 0 ≤ 2*a*(1-a/4) := by
      exact mul_nonneg (mul_nonneg (by norm_num) ha.1) (by linarith [ha.2])
    have hlog : Real.log (4/b) ≤ Real.log (4/a) := by
      apply Real.log_le_log (div_pos (by norm_num) hbp)
      exact div_le_div_of_nonneg_left (by norm_num) hap hab
    unfold influenceLogarithmic
    have hnumB : 0 ≤ 2*b*(1-b/4) := by
      exact mul_nonneg (mul_nonneg (by norm_num) hb.1) (by linarith [hb.2])
    exact div_le_div₀ hnumB hnum (influence_log_pos ⟨hbp,hb.2⟩) hlog

theorem influencePsi_zero : influencePsi 0 = 0 := by
  simp [influencePsi,influencePolynomial,influenceLogarithmic_zero]

theorem influencePsi_monotoneOn : MonotoneOn influencePsi (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  exact min_le_min (influencePolynomial_monotoneOn ha.1 hb.1 hab)
    (influenceLogarithmic_monotoneOn ha hb hab)

end
end CK
