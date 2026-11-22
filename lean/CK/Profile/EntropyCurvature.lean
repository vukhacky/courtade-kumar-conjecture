module

public import CK.Profile.Tangent
public import CK.Certificate.EntropyRatio

/-! A scalar entropy inequality controlling the logarithmic curvature of
the profile. The proof uses compact-interval concavity of x² log x and
avoids an asymptotic cancellation at the singular entropy endpoint. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

def entropyLogImbalance (p : ℝ) : ℝ :=
  p^2*Real.log p-(1-p)^2*Real.log (1-p)

theorem continuous_entropyLogImbalance : Continuous entropyLogImbalance := by
  have heq : entropyLogImbalance = fun p : ℝ =>
      p*(p*Real.log p)-(1-p)*((1-p)*Real.log (1-p)) := by
    funext p
    unfold entropyLogImbalance
    ring
  rw [heq]
  exact (continuous_id.mul Real.continuous_mul_log).sub
    ((continuous_const.sub continuous_id).mul
      (Real.continuous_mul_log.comp (continuous_const.sub continuous_id)))

theorem hasDerivAt_entropyLogImbalance {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt entropyLogImbalance (1-2*Real.binEntropy p) p := by
  have hp0 := ne_of_gt hp.1
  have hr0 : 1-p ≠ 0 := by linarith [hp.2]
  have h := ((hasDerivAt_pow 2 p).mul (Real.hasDerivAt_log hp0)).sub
    ((((hasDerivAt_id p).const_sub 1).pow 2).mul
      (((hasDerivAt_id p).const_sub 1).log hr0))
  apply h.congr_deriv
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  dsimp only [id_eq, Pi.pow_apply]
  field_simp
  ring

theorem entropyLogImbalance_concave :
    ConcaveOn ℝ (Icc (0 : ℝ) (1/2)) entropyLogImbalance := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (f' := fun p => 1-2*Real.binEntropy p)
    (f'' := fun p => 2*(Real.log p-Real.log (1-p)))
    (convex_Icc 0 (1/2)) continuous_entropyLogImbalance.continuousOn
  · intro p hp
    have hp' : p ∈ Ioo (0 : ℝ) (1/2) := by simpa using hp
    exact (hasDerivAt_entropyLogImbalance ⟨hp'.1, by linarith [hp'.2]⟩).hasDerivWithinAt
  · intro p hp
    have hp' : p ∈ Ioo (0 : ℝ) (1/2) := by simpa using hp
    have h := (((Real.hasDerivAt_binEntropy (ne_of_gt hp'.1)
      (show p ≠ 1 by linarith [hp'.2])).const_mul 2).const_sub 1)
    convert h.hasDerivWithinAt using 1 <;> ring
  · intro p hp
    have hp' : p ∈ Ioo (0 : ℝ) (1/2) := by simpa using hp
    have h := Real.log_le_log hp'.1 (show p ≤ 1-p by linarith [hp'.2])
    linarith

theorem entropyLogImbalance_nonneg {p : ℝ} (hp : p ∈ Icc (0 : ℝ) (1/2)) :
    0 ≤ entropyLogImbalance p := by
  have h := entropyLogImbalance_concave.2
    (by norm_num : (0 : ℝ) ∈ Icc 0 (1/2))
    (by norm_num : (1/2 : ℝ) ∈ Icc 0 (1/2))
    (show 0 ≤ 1-2*p by linarith [hp.2]) (show 0 ≤ 2*p by linarith [hp.1])
    (show (1-2*p)+(2*p)=1 by ring)
  have heq : (1-2*p)*(0 : ℝ)+(2*p)*(1/2)=p := by ring
  change (1-2*p)*entropyLogImbalance 0+(2*p)*entropyLogImbalance (1/2) ≤
    entropyLogImbalance ((1-2*p)*0+(2*p)*(1/2)) at h
  have h0 : entropyLogImbalance 0 = 0 := by norm_num [entropyLogImbalance]
  have hh : entropyLogImbalance (1/2) = 0 := by norm_num [entropyLogImbalance]
  rw [heq, h0, hh] at h
  simpa using h

theorem log_product_lt_binEntropy {p : ℝ} (hp : p ∈ Ioc (0 : ℝ) (1/2)) :
    Real.log p*Real.log (1-p) < Real.binEntropy p := by
  have hr : 0 < 1-p := by linarith [hp.2]
  have hp1 : p < 1 := by linarith [hp.2]
  have hl : 0 < -Real.log p := neg_pos.mpr (Real.log_neg hp.1 hp1)
  have hn : (1-p)⁻¹ ≠ 1 := by
    intro h
    have hh := inv_eq_one.mp h
    linarith [hp.1]
  have hb := Real.log_lt_sub_one_of_pos (inv_pos.mpr hr) hn
  rw [Real.log_inv] at hb
  have hb' := mul_lt_mul_of_pos_left hb hr
  have hprod : (1-p)*(1-p)⁻¹=1 := mul_inv_cancel₀ (ne_of_gt hr)
  have hb'' : -(1-p)*Real.log (1-p) < p := by nlinarith only [hb', hprod]
  have hmul := mul_lt_mul_of_pos_left hb'' hl
  have hk := entropyLogImbalance_nonneg ⟨hp.1.le, hp.2⟩
  dsimp [entropyLogImbalance] at hk
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def]
  apply (mul_lt_mul_iff_right₀ hr).mp
  nlinarith only [hmul, hk]

/-- The determinant controlling log-concavity of cosh(v) H(tanh(v))
is strictly negative, expressed without hyperbolic substitutions. -/
theorem profile_curvature_negative {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    profileAux t ^ 2-phiSlope t ^ 2-meanEntropy t < 0 := by
  let p := (1-t)/2
  have hp : p ∈ Ioc (0 : ℝ) (1/2) := by
    dsimp [p]
    constructor <;> linarith [ht.1, ht.2]
  have hprod := log_product_lt_binEntropy hp
  have hm : 1-t ≠ 0 := by linarith [ht.2]
  have ha : 1+t ≠ 0 := by linarith [ht.1]
  have hg : 1-t^2 = (1-t)*(1+t) := by ring
  have hleft : profileAux t-phiSlope t = -Real.log ((1+t)/2) := by
    dsimp [profileAux, phiSlope]
    rw [hg, Real.log_mul hm ha, Real.log_div ha (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hright : profileAux t+phiSlope t = -Real.log p := by
    dsimp [profileAux, phiSlope, p]
    rw [hg, Real.log_mul hm ha, Real.log_div hm (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hpp : 1-p=(1+t)/2 := by dsimp [p]; ring
  have hid : profileAux t^2-phiSlope t^2 = Real.log p*Real.log (1-p) := by
    calc
      _ = (profileAux t-phiSlope t)*(profileAux t+phiSlope t) := by ring
      _ = _ := by rw [hleft, hright, ← hpp]; ring
  rw [hid]
  exact sub_neg.mpr hprod

end
end CK.Profile
