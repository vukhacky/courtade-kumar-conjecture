module

public import CK.Profile.CGNScalar

/-! Odds coordinates for the CGN edge inequality. Every logarithmic
identity below has positive arguments established before use. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

def oddsSign (a : ℝ) : ℝ := (a^2-1)/(a^2+1)

theorem oddsSign_mem {a : ℝ} (ha : 0 < a) : oddsSign a ∈ Ioo (-1 : ℝ) 1 := by
  have hd : 0 < a^2+1 := by positivity
  constructor
  · apply (lt_div_iff₀ hd).2
    nlinarith [sq_pos_of_pos ha]
  · apply (div_lt_iff₀ hd).2
    linarith

theorem artanh_oddsSign {a : ℝ} (ha : 0 < a) : Real.artanh (oddsSign a) = Real.log a := by
  have ht := oddsSign_mem ha
  have hd : a^2+1 ≠ 0 := by positivity
  rw [Real.artanh_eq_half_log ⟨ht.1.le, ht.2.le⟩]
  have heq : (1+oddsSign a)/(1-oddsSign a) = a^2 := by
    unfold oddsSign
    field_simp
    ring
  rw [heq, Real.log_pow]
  ring

theorem meanEntropy_oddsSign {a : ℝ} (ha : 0 < a) :
    (1+a^2)*meanEntropy (oddsSign a) =
      (1+a^2)*Real.log (1+a^2)-2*a^2*Real.log a := by
  have hd : 1+a^2 ≠ 0 := by positivity
  have hp : (1-oddsSign a)/2 = 1/(1+a^2) := by unfold oddsSign; field_simp; ring
  have hq : 1-1/(1+a^2) = a^2/(1+a^2) := by field_simp; ring
  rw [meanEntropy, hp, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hq]
  simp only [Real.negMulLog_def, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hd,
    Real.log_div (pow_ne_zero 2 (ne_of_gt ha)) hd, Real.log_one, Real.log_pow]
  field_simp
  ring

theorem meanEntropy_pair_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a+b)*meanEntropy ((a-b)/(a+b)) =
      (a+b)*Real.log (a+b)-a*Real.log a-b*Real.log b := by
  have hd : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hp : (1-(a-b)/(a+b))/2 = b/(a+b) := by field_simp; ring
  have hq : 1-b/(a+b) = a/(a+b) := by field_simp; ring
  rw [meanEntropy, hp, Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, hq]
  simp only [Real.negMulLog_def, Real.log_div (ne_of_gt ha) hd,
    Real.log_div (ne_of_gt hb) hd]
  field_simp
  ring

theorem odds_entropy_comparison {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    2*(a+b)^2*meanEntropy ((a-b)/(a+b)) ≤
      (1+a^2)*(1+b^2)*(meanEntropy (oddsSign a)+meanEntropy (oddsSign b)) := by
  have hm := cgnComparison_nonneg (mul_pos ha hb)
    (show a*b ≤ (a^2+b^2)/2 by nlinarith [sq_nonneg (a-b)])
  have hdA : 1+a^2 ≠ 0 := by positivity
  have hdB : 1+b^2 ≠ 0 := by positivity
  have hsum : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  unfold cgnComparison at hm
  rw [show 1+2*((a^2+b^2)/2)+(a*b)^2 = (1+a^2)*(1+b^2) by ring,
    show 2*((a^2+b^2)/2+a*b) = (a+b)^2 by ring,
    Real.log_mul hdA hdB, Real.log_pow, Real.log_mul (ne_of_gt ha) (ne_of_gt hb)] at hm
  have hA := congrArg (fun z : ℝ => (1+b^2)*z) (meanEntropy_oddsSign ha)
  have hB := congrArg (fun z : ℝ => (1+a^2)*z) (meanEntropy_oddsSign hb)
  have hT := congrArg (fun z : ℝ => 2*(a+b)*z) (meanEntropy_pair_ratio ha hb)
  ring_nf at hm hA hB hT ⊢
  linarith only [hm, hA, hB, hT]

theorem artanh_pair_ratio {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.artanh ((a-b)/(a+b)) = (Real.log a-Real.log b)/2 := by
  have hd : 0 < a+b := add_pos ha hb
  have ht : (a-b)/(a+b) ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hd).2; linarith
    · apply (div_le_iff₀ hd).2; linarith
  rw [Real.artanh_eq_half_log ht]
  have heq : (1+(a-b)/(a+b))/(1-(a-b)/(a+b)) = a/b := by
    field_simp [ne_of_gt hb]
    ring
  rw [heq, Real.log_div (ne_of_gt ha) (ne_of_gt hb)]
  ring

theorem oddsSign_sqrt_inverse {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    oddsSign (Real.sqrt ((1+x)/(1-x))) = x := by
  have hd : 0 < 1-x := by linarith [hx.2]
  have hn : 0 < 1+x := by linarith [hx.1]
  have hs := Real.sq_sqrt (div_pos hn hd).le
  unfold oddsSign
  rw [hs]
  field_simp
  ring

end
end CK.Profile
