module

public import CK.Certificate.EntropyRatio
public import CK.Certificate.AndRationalLogs

/-! STOC `lem:and-rational`: full-interval scalar estimates for the
AND two-coordinate entropy, on 39/40 ≤ rho ≤ 49/50. The logarithm
endpoint checks use proved rational remainder bounds. The interval
arguments are analytic, not sampling. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Certificate
noncomputable section

theorem entropy_ratio_endpoint_lt :
    signEntropy (49/50 : ℝ) / (1-(49/50 : ℝ)^2) < 17/12 := by
  have he : signEntropy (49/50 : ℝ) =
      (1/100 : ℝ)*Real.log 100 + (99/100 : ℝ)*Real.log (100/99 : ℝ) := by
    rw [signEntropy, binEntropy_eq_log_inv]
    norm_num
  rw [he]
  norm_num
  nlinarith only [AndLogs.log_hundred_bounds.2, AndLogs.log_hundred_ratio_bounds.2]

theorem entropy_ratio_lt_seventeen_twelfths {rho : ℝ}
    (hrho : rho ∈ Icc (39/40 : ℝ) (49/50)) :
    signEntropy rho / (1-rho^2) < 17/12 := by
  have h := entropy_ratio_monotoneOn
    (show rho ∈ Ico (0 : ℝ) 1 by constructor <;> linarith [hrho.1, hrho.2])
    (by norm_num : (49/50 : ℝ) ∈ Ico 0 1) hrho.2
  exact h.trans_lt entropy_ratio_endpoint_lt

theorem binEntropy_one_eightieth_lt : Real.binEntropy (1/80 : ℝ) < 7/100 := by
  rw [binEntropy_eq_log_inv]
  norm_num
  nlinarith only [AndLogs.log_eighty_bounds.2, AndLogs.log_eighty_ratio_bounds.2]

theorem binEntropy_small_lt {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1/80)) :
    Real.binEntropy p < 7/100 := by
  have h := Real.binEntropy_strictMonoOn.monotoneOn
    (show p ∈ Icc (0 : ℝ) 2⁻¹ by constructor; exact hp.1; norm_num; linarith [hp.2])
    (by norm_num : (1/80 : ℝ) ∈ Icc 0 2⁻¹) hp.2
  exact h.trans_lt binEntropy_one_eightieth_lt

def entropyComplement (s : ℝ) : ℝ := Real.negMulLog (1-s)

theorem hasDerivAt_entropyComplement {s : ℝ} (hs : s < 1) :
    HasDerivAt entropyComplement (Real.log (1-s)+1) s := by
  have h := (Real.hasDerivAt_negMulLog (show 1-s ≠ 0 by linarith)).comp s
    ((hasDerivAt_id s).const_sub 1)
  apply h.congr_deriv
  ring

theorem complement_double_lower {p : ℝ} (hp0 : 0 ≤ p) (hp1 : 2*p < 1) :
    2*entropyComplement p - p^2/(1-2*p) ≤ entropyComplement (2*p) := by
  let F : ℝ → ℝ := fun s => entropyComplement s + s^2/(2*(1-2*p))
  have hdpos : 0 < 1-2*p := by linarith
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (2*p)) :
      HasDerivAt F (Real.log (1-s)+1+s/(1-2*p)) s := by
    have h := (hasDerivAt_entropyComplement (lt_of_le_of_lt hs.2 hp1)).add
      ((hasDerivAt_pow 2 s).div_const (2*(1-2*p)))
    apply h.congr_deriv
    norm_num
    field_simp
  have hdd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (2*p)) :
      HasDerivAt (fun s => Real.log (1-s)+1+s/(1-2*p))
        (-1/(1-s)+1/(1-2*p)) s := by
    have h := ((((hasDerivAt_id s).const_sub 1).log
      (show 1-s ≠ 0 by linarith [hs.2])).add_const 1).add
      ((hasDerivAt_id s).div_const (1-2*p))
    exact h
  have hc : ConvexOn ℝ (Icc (0 : ℝ) (2*p)) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 (2*p))
      (f' := fun s => Real.log (1-s)+1+s/(1-2*p))
      (f'' := fun s => -1/(1-s)+1/(1-2*p))
    · dsimp [F, entropyComplement]
      fun_prop
    · intro s hs
      exact (hd s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      exact (hdd s (interior_subset hs)).hasDerivWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) (2*p) := interior_subset hs
      have h := one_div_le_one_div_of_le hdpos (show 1-2*p ≤ 1-s by linarith [hs'.2])
      rw [neg_div]
      linarith
  have h := hc.2 (show (0 : ℝ) ∈ Icc 0 (2*p) by constructor <;> linarith)
    (show 2*p ∈ Icc (0 : ℝ) (2*p) by constructor <;> linarith)
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ)+1/2=1)
  simp only [smul_eq_mul, mul_zero, zero_add, show (1/2 : ℝ)*(2*p)=p by ring] at h
  have h0 : entropyComplement 0 = 0 := by simp [entropyComplement]
  dsimp [F] at h
  rw [h0] at h
  simp only [div_eq_mul_inv, mul_inv_rev] at h ⊢
  norm_num at h ⊢
  nlinarith only [h]

theorem binEntropy_eq_complement (p : ℝ) :
    Real.binEntropy p = -p*Real.log p + entropyComplement p := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [entropyComplement, Real.negMulLog_eq_neg]
  ring

theorem binEntropy_double_lower {p : ℝ} (hp0 : 0 ≤ p) (hp1 : 2*p < 1) :
    2*Real.binEntropy p - 2*p*Real.log 2 - p^2/(1-2*p) ≤ Real.binEntropy (2*p) := by
  by_cases h0 : p = 0
  · simp [h0]
  have hlog : Real.log (2*p) = Real.log 2 + Real.log p :=
    Real.log_mul (by norm_num) h0
  have hL := complement_double_lower hp0 hp1
  rw [binEntropy_eq_complement, binEntropy_eq_complement, hlog]
  nlinarith only [hL]

theorem binEntropy_scale_lower {p t : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    t*Real.binEntropy p ≤ Real.binEntropy (t*p) := by
  have h := Real.strictConcave_binEntropy.concaveOn.2
    (show (0 : ℝ) ∈ Icc 0 1 by norm_num) hp
    (sub_nonneg.mpr ht.2) ht.1 (show (1-t)+t=1 by ring)
  simpa only [smul_eq_mul, mul_zero, zero_add, Real.binEntropy_zero] using h

def andEntropyExpressionP (p : ℝ) : ℝ :=
  (Real.binEntropy (p^2)+2*Real.binEntropy (p*(1-p))+
    Real.binEntropy (2*p-p^2))/4

def andEntropyExpression (rho : ℝ) : ℝ := andEntropyExpressionP ((1-rho)/2)

theorem and_entropy_gap_bound {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1/80)) :
    Real.binEntropy p - andEntropyExpressionP p ≤
      p*((Real.binEntropy p+Real.log 2)/2+p/(4*(1-2*p))) := by
  have hp' : p ∈ Icc (0 : ℝ) 1 := ⟨hp.1, by linarith [hp.2]⟩
  have h2p : 2*p ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.1], by linarith [hp.2]⟩
  have h1 := binEntropy_scale_lower hp' hp'
  rw [← pow_two] at h1
  have h2 := binEntropy_scale_lower hp' (show 1-p ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hp.1, hp.2])
  rw [mul_comm (1-p) p] at h2
  have h3 := binEntropy_scale_lower h2p (show 1-p/2 ∈ Icc (0 : ℝ) 1 by constructor <;> linarith [hp.1, hp.2])
  rw [show (1-p/2)*(2*p)=2*p-p^2 by ring] at h3
  have hd := binEntropy_double_lower hp.1 (by linarith [hp.2])
  have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ 1-p/2 by linarith [hp.2])
  have hx : 0 ≤ p^2*Real.log 2/4 + p^3/(8*(1-2*p)) := by
    have hp0 := hp.1
    have hd0 : 0 < 1-2*p := by linarith [hp.2]
    positivity
  dsimp [andEntropyExpressionP]
  simp only [div_eq_mul_inv, mul_inv_rev] at h1 h2 h3 hm hx ⊢
  norm_num at h1 h2 h3 hm hx ⊢
  nlinarith only [h1, h2, h3, hm, hx]

theorem and_entropy_rational_P {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1/80)) :
    Real.binEntropy p - (2/5 : ℝ)*p*(1-p) ≤ andEntropyExpressionP p := by
  have hH := binEntropy_small_lt hp
  have hlog : Real.log 2 < 7/10 := lt_of_le_of_lt log_two_coarse_bounds.2 (by norm_num)
  have hD : 0 < 1-2*p := by linarith [hp.2]
  have hfrac : p/(4*(1-2*p)) ≤ 1/312 := by
    rw [div_le_iff₀ (by positivity : 0 < 4*(1-2*p))]
    linarith [hp.2]
  have hbracket : (Real.binEntropy p+Real.log 2)/2+p/(4*(1-2*p)) ≤ (2/5 : ℝ)*(1-p) := by
    linarith [hp.2]
  have hmul := mul_le_mul_of_nonneg_left hbracket hp.1
  have hgap := and_entropy_gap_bound hp
  nlinarith only [hmul, hgap]

theorem and_entropy_rational {rho : ℝ} (hrho : rho ∈ Icc (39/40 : ℝ) (49/50)) :
    signEntropy rho - (1-rho^2)/10 ≤ andEntropyExpression rho := by
  have hp : (1-rho)/2 ∈ Icc (0 : ℝ) (1/80) := by constructor <;> linarith [hrho.1, hrho.2]
  have h := and_entropy_rational_P hp
  change Real.binEntropy ((1-rho)/2) - (1-rho^2)/10 ≤ andEntropyExpressionP ((1-rho)/2)
  nlinarith only [h]

end
end CK.Certificate
