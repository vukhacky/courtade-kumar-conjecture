module

public import CK.Certificate.MomentIdentities
public import CK.Certificate.MeanMoments
public import CK.Certificate.AndRational

/-! The mean-compensated two-coordinate entropy bound for a bounded affine Fourier polynomial, with its mean and interaction coefficient. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Certificate
noncomputable section

theorem avg_shift_twoCoreSignal (rho a b c mu : ℝ) :
    avg (fun x => mu + twoCoreSignal rho a b c x) = mu := by
  rw [avg_add, avg_const, avg_twoCoreSignal, add_zero]

theorem centeredMoment_shift_twoCoreSignal (rho a b c mu : ℝ) (k : ℕ) :
    centeredMoment (fun x => mu + twoCoreSignal rho a b c x) k =
      avg (fun x => twoCoreSignal rho a b c x ^ k) := by
  unfold centeredMoment centered
  rw [avg_shift_twoCoreSignal]
  congr 1
  funext x
  congr 1
  ring

theorem twoCore_second_moment_le {rho a b c : ℝ} (hb : 0 ≤ b) (hc : |c| ≤ b) :
    avg (fun x => twoCoreSignal rho a b c x ^ 2) ≤
      avg (fun x => twoCoreSignal rho a b b x ^ 2) := by
  have hc2 : c^2 ≤ b^2 := by nlinarith [sq_abs c, abs_nonneg c]
  have hm := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ rho^4 by positivity)
  rw [avg_twoCoreSignal_sq, avg_twoCoreSignal_sq]
  nlinarith only [hm]

theorem twoCore_fourth_moment_le {rho a b c : ℝ} (hb : 0 ≤ b) (hc : |c| ≤ b) :
    avg (fun x => twoCoreSignal rho a b c x ^ 4) ≤
      avg (fun x => twoCoreSignal rho a b b x ^ 4) := by
  have hc2 : c^2 ≤ b^2 := by nlinarith [sq_abs c, abs_nonneg c]
  have hc4 : c^4 ≤ b^4 := by nlinarith [sq_nonneg (b^2-c^2)]
  have h2 := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ 6*rho^6*(a^2+b^2) by positivity)
  have h4 := mul_le_mul_of_nonneg_left hc4 (show 0 ≤ rho^8 by positivity)
  rw [avg_twoCoreSignal_fourth, avg_twoCoreSignal_fourth]
  nlinarith only [h2, h4]

theorem cubic_coefficient_bound {a : ℝ} (ha : a ∈ Icc (2/3 : ℝ) 1) :
    6*a*(1-a)^2 ≤ 4/9 := by
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hsq : a^2 ≤ a := by nlinarith [mul_nonneg ha0 (sub_nonneg.mpr ha.2)]
  have hq : 0 ≤ 12*a-9*a^2-1 := by nlinarith [ha.1]
  have h := mul_nonneg (show 0 ≤ 3*a-2 by linarith [ha.1]) hq
  nlinarith only [h]

theorem twoCore_third_moment_abs_le {rho a b c : ℝ}
    (hrho : rho ∈ Icc (0 : ℝ) 1) (ha : a ∈ Icc (2/3 : ℝ) 1)
    (hb : 0 ≤ b) (hab : a+b ≤ 1) (hc : |c| ≤ b) :
    |avg (fun x => twoCoreSignal rho a b c x ^ 3)| ≤ 4/9 := by
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hr0 : 0 ≤ rho := hrho.1
  have hr4 : rho^4 ≤ 1 := pow_le_one₀ hr0 hrho.2
  have hb2 : b^2 ≤ (1-a)^2 := by nlinarith [ha.2]
  rw [avg_twoCoreSignal_cube]
  calc
    |6*rho^4*a*b*c| = 6*rho^4*a*b*|c| := by
      rw [abs_mul, abs_of_nonneg (show 0 ≤ 6*rho^4*a*b by positivity)]
    _ ≤ 6*rho^4*a*b*b := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = rho^4*(6*a*b^2) := by ring
    _ ≤ 6*a*b^2 := mul_le_of_le_one_left (by positivity) hr4
    _ ≤ 6*a*(1-a)^2 := mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ ≤ 4/9 := cubic_coefficient_bound ha

theorem twoCore_entropy_compensation_lower {rho a b c mu : ℝ}
    (hrho : rho ∈ Icc (39/40 : ℝ) (49/50))
    (ha : a ∈ Icc (2/3 : ℝ) 1) (hb : 0 ≤ b) (hab : a+b ≤ 1) (hc : |c| ≤ b)
    (hg : ∀ x, mu + twoCoreSignal rho a b c x ∈ Icc (-1 : ℝ) 1) :
    (1-rho^2)*(9/13 - avg (fun x => twoCoreSignal rho a b b x ^ 2)/2 -
        avg (fun x => twoCoreSignal rho a b b x ^ 4)/5 - 1/198) ≤
      (1-rho^2)*avg (fun x => signEntropy (mu + twoCoreSignal rho a b c x)) + phi mu := by
  let lam : ℝ := 1-rho^2
  let M₂ := avg (fun x => twoCoreSignal rho a b c x ^ 2)
  let M₃ := avg (fun x => twoCoreSignal rho a b c x ^ 3)
  let M₄ := avg (fun x => twoCoreSignal rho a b c x ^ 4)
  let N₂ := avg (fun x => twoCoreSignal rho a b b x ^ 2)
  let N₄ := avg (fun x => twoCoreSignal rho a b b x ^ 4)
  have hdom : rho ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [hrho.1, hrho.2]
  have hlam : lam ∈ Icc (0 : ℝ) (1/20) := by
    dsimp [lam]
    constructor <;> nlinarith [hrho.1, hrho.2]
  have hlam0 : 0 ≤ lam := hlam.1
  have hmean := mean_moment_compensation (fun x => mu + twoCoreSignal rho a b c x) hg hlam
  rw [avg_shift_twoCoreSignal] at hmean
  simp only [centeredMoment_shift_twoCoreSignal] at hmean
  change lam*(Real.log 2-M₂/2-(Real.log 2-1/2)*M₄)-(2/5 : ℝ)*lam^2*M₃^2 ≤ _ at hmean
  have h2 : M₂ ≤ N₂ := twoCore_second_moment_le hb hc
  have h4 : M₄ ≤ N₄ := twoCore_fourth_moment_le hb hc
  have h40 : 0 ≤ M₄ := by
    have h := avg_mono (fun x => show (0 : ℝ) ≤ twoCoreSignal rho a b c x ^ 4 by positivity)
    rwa [avg_const] at h
  have hκ : Real.log 2 - 1/2 ≤ (1/5 : ℝ) := by linarith [log_two_coarse_bounds.2]
  have hκ4 := mul_le_mul_of_nonneg_right hκ h40
  have hlog : (9/13 : ℝ) ≤ Real.log 2 := by linarith [log_two_coarse_bounds.1]
  have hmain : (9/13 : ℝ)-N₂/2-N₄/5 ≤ Real.log 2-M₂/2-(Real.log 2-1/2)*M₄ := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hmain hlam0
  have h3abs : |M₃| ≤ 4/9 := twoCore_third_moment_abs_le hdom ha hb hab hc
  have h3sq : M₃^2 ≤ (16/81 : ℝ) := by nlinarith [sq_abs M₃, abs_nonneg M₃]
  have herr0 := mul_le_mul_of_nonneg_left h3sq (show 0 ≤ (2/5 : ℝ)*lam^2 by positivity)
  have hlamsq : lam^2 ≤ lam/20 := by
    have h := mul_le_mul_of_nonneg_left hlam.2 hlam0
    nlinarith only [h]
  have herr : (2/5 : ℝ)*lam^2*M₃^2 ≤ lam/198 := by nlinarith only [herr0, hlamsq, hlam0]
  change lam*(9/13-N₂/2-N₄/5-1/198) ≤ _
  nlinarith only [hmean, hm, herr]

/-- The two-coordinate entropy bound by the polynomial in manuscript equation `eq:local-moment-polynomial`. -/
theorem twoCore_entropy_moment_lower_bound {rho a b c mu : ℝ}
    (hrho : rho ∈ Icc (39/40 : ℝ) (49/50))
    (ha : a ∈ Icc (2/3 : ℝ) (76043/100000)) (hb : 0 ≤ b)
    (hab : a+b ≤ 1) (hc : |c| ≤ b)
    (hg : ∀ x, mu + twoCoreSignal rho a b c x ∈ Icc (-1 : ℝ) 1) :
    (1-rho^2)*localMomentQ rho a b ≤
      (rho^2*(a+b)-1)*signEntropy rho - (1-rho^2)*rho^2*b/5 +
        (1-rho^2)*avg (fun x => signEntropy (mu + twoCoreSignal rho a b c x)) + phi mu := by
  have hcomp := twoCore_entropy_compensation_lower hrho ⟨ha.1, by linarith [ha.2]⟩ hb hab hc hg
  have hlam : 0 < 1-rho^2 := by nlinarith [hrho.1, hrho.2]
  have hH := (div_lt_iff₀ hlam).mp (entropy_ratio_lt_seventeen_twelfths hrho)
  have hK : rho^2*(a+b)-1 ≤ 0 := by
    have hm := mul_le_mul_of_nonneg_left hab (sq_nonneg rho)
    nlinarith [hrho.1, hrho.2]
  have hKH := mul_le_mul_of_nonpos_left hH.le hK
  rw [localMomentQ_eq_moments]
  nlinarith only [hcomp, hKH]

end
end CK.Certificate
