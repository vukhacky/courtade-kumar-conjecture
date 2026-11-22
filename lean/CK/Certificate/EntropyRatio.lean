module

public import CK.Certificate.EntropyQuartic

/-! Monotonicity of H(t)/(1-t²) on [0,1), needed by STOC
`lem:and-rational`. This proof uses concavity of its derivative numerator
and checks continuity at the singular entropy endpoint via x log x. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Certificate
noncomputable section

def entropyRatioNumerator (t : ℝ) : ℝ :=
  2*t*signEntropy t - (1-t^2)*phiSlope t

theorem entropyRatioNumerator_eq (t : ℝ) :
    entropyRatioNumerator t = 2*t*Real.log 2 +
      (1-t)^2*Real.log (1-t)/2 - (1+t)^2*Real.log (1+t)/2 := by
  unfold entropyRatioNumerator
  rw [signEntropy_eq_log_two_sub_phi]
  have h := mulLog_one_add_add_one_sub t
  unfold phiSlope
  nlinarith only [h]

theorem continuous_entropyRatioNumerator : Continuous entropyRatioNumerator := by
  have heq : entropyRatioNumerator = fun t : ℝ => 2*t*Real.log 2 +
      (1-t)*((1-t)*Real.log (1-t))/2 - (1+t)*((1+t)*Real.log (1+t))/2 := by
    funext t
    rw [entropyRatioNumerator_eq]
    ring
  rw [heq]
  have hm := Real.continuous_mul_log.comp (continuous_const.sub continuous_id :
      Continuous (fun t : ℝ => 1-t))
  have hp := Real.continuous_mul_log.comp (continuous_const.add continuous_id :
      Continuous (fun t : ℝ => 1+t))
  exact ((continuous_const.mul continuous_id).mul continuous_const).add
    (((continuous_const.sub continuous_id).mul hm).div_const 2) |>.sub
      (((continuous_const.add continuous_id).mul hp).div_const 2)

theorem hasDerivAt_entropyRatioNumerator {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt entropyRatioNumerator (2*signEntropy t-1) t := by
  have hn : 1-t^2 ≠ 0 := by nlinarith [ht.1, ht.2]
  have h := (((hasDerivAt_id t).const_mul 2).mul (hasDerivAt_signEntropy ht)).sub
    (((hasDerivAt_pow 2 t).const_sub 1).mul (hasDerivAt_phiSlope ht))
  apply h.congr_deriv
  norm_num
  field_simp
  ring

theorem entropyRatioNumerator_concave :
    ConcaveOn ℝ (Icc (0 : ℝ) 1) entropyRatioNumerator := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fun t => 2*signEntropy t-1)
    (f'' := fun t => -2*phiSlope t) (convex_Icc 0 1)
    continuous_entropyRatioNumerator.continuousOn
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact (hasDerivAt_entropyRatioNumerator ⟨by linarith [ht'.1], ht'.2⟩).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    convert (((hasDerivAt_signEntropy ⟨by linarith [ht'.1], ht'.2⟩).const_mul 2).sub_const 1).hasDerivWithinAt using 1 <;> ring
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    have h := le_phiSlope ht'.1.le ht'.2
    linarith [ht'.1]

theorem entropyRatioNumerator_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ entropyRatioNumerator t := by
  have h := entropyRatioNumerator_concave.2
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (show (1-t)+t=1 by ring)
  simpa [entropyRatioNumerator] using h

theorem entropy_ratio_monotoneOn :
    MonotoneOn (fun t : ℝ => signEntropy t / (1-t^2)) (Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun t => entropyRatioNumerator t / (1-t^2)^2) (convex_Ico 0 1)
  · apply continuous_signEntropy.continuousOn.div
      (continuous_const.sub (continuous_pow 2)).continuousOn
    intro t ht
    change 1-t^2 ≠ 0
    nlinarith [ht.1, ht.2]
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    have hn : 1-t^2 ≠ 0 := by nlinarith [ht'.1, ht'.2]
    have h := (hasDerivAt_signEntropy ⟨by linarith [ht'.1], ht'.2⟩).div
      ((hasDerivAt_pow 2 t).const_sub 1) hn
    have hh : HasDerivAt (fun t : ℝ => signEntropy t / (1-t^2))
        (entropyRatioNumerator t / (1-t^2)^2) t := by
      apply h.congr_deriv
      dsimp [entropyRatioNumerator]
      norm_num
      ring
    exact hh.hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact div_nonneg (entropyRatioNumerator_nonneg ⟨ht'.1.le, ht'.2.le⟩) (sq_nonneg _)

end
end CK.Certificate
