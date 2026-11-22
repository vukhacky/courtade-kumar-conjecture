module

public import CK.Profile.EntropyCurvature
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Monotonicity of the elasticity used in the squared-profile concavity
and profile-ratio comparisons. The parameter is t=tanh(v), so the proof
works entirely on (0,1) and keeps every denominator positive. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

def entropyHyperbolicSlope (t : ℝ) : ℝ :=
  t*Real.log 2+(1-t)*Real.log (1-t)/2-(1+t)*Real.log (1+t)/2

theorem entropyHyperbolicSlope_eq {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    entropyHyperbolicSlope t = t*profileAux t-phiSlope t := by
  have hm : 1-t ≠ 0 := by linarith [ht.2]
  have hp : 1+t ≠ 0 := by linarith [ht.1]
  unfold entropyHyperbolicSlope profileAux phiSlope
  rw [show 1-t^2=(1-t)*(1+t) by ring, Real.log_mul hm hp]
  ring

theorem continuous_entropyHyperbolicSlope : Continuous entropyHyperbolicSlope := by
  exact ((continuous_id.mul continuous_const).add
    ((Real.continuous_mul_log.comp (continuous_const.sub continuous_id)).div_const 2)).sub
    ((Real.continuous_mul_log.comp (continuous_const.add continuous_id)).div_const 2)

theorem hasDerivAt_entropyHyperbolicSlope {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt entropyHyperbolicSlope (profileAux t-1) t := by
  have heq : entropyHyperbolicSlope =ᶠ[nhds t] fun s => s*profileAux s-phiSlope s := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact entropyHyperbolicSlope_eq hs
  have h := ((hasDerivAt_id t).mul (hasDerivAt_profileAux ht)).sub (hasDerivAt_phiSlope ht)
  have hh : HasDerivAt (fun s => s*profileAux s-phiSlope s) (profileAux t-1) t := by
    apply h.congr_deriv
    dsimp only [id_eq]
    field_simp [ne_of_gt (gap_pos ht)]
    ring
  exact hh.congr_of_eventuallyEq heq

theorem entropyHyperbolicSlope_convex :
    ConvexOn ℝ (Icc (0 : ℝ) 1) entropyHyperbolicSlope := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun t => profileAux t-1)
    (f'' := fun t => t/(1-t^2)) (convex_Icc 0 1)
    continuous_entropyHyperbolicSlope.continuousOn
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact (hasDerivAt_entropyHyperbolicSlope ⟨by linarith [ht'.1], ht'.2⟩).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact ((hasDerivAt_profileAux ⟨by linarith [ht'.1], ht'.2⟩).sub_const 1).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact div_nonneg ht'.1.le (gap_pos ⟨by linarith [ht'.1], ht'.2⟩).le

theorem entropyHyperbolicSlope_nonpos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    entropyHyperbolicSlope t ≤ 0 := by
  have h := entropyHyperbolicSlope_convex.2
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
    (show 0 ≤ 1-t by linarith [ht.2]) ht.1 (show (1-t)+t=1 by ring)
  have h0 : entropyHyperbolicSlope 0=0 := by norm_num [entropyHyperbolicSlope]
  have h1 : entropyHyperbolicSlope 1=0 := by norm_num [entropyHyperbolicSlope]
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, h0, h1, add_zero] using h

def logScaledSlope (t : ℝ) : ℝ :=
  1/phiSlope t-1/t+entropyHyperbolicSlope t/meanEntropy t

def elasticity (t : ℝ) : ℝ := 1-phiSlope t*logScaledSlope t

def scaledProfile (t : ℝ) : ℝ := phiSlope t*meanEntropy t/t

theorem phiSlope_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < phiSlope t := by
  rw [phiSlope_eq_artanh ⟨by linarith [ht.1], ht.2⟩]
  exact Real.artanh_pos ht

theorem logScaledSlope_nonpos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    logScaledSlope t ≤ 0 := by
  have hrec := one_div_le_one_div_of_le ht.1 (le_phiSlope ht.1.le ht.2)
  have hH := meanEntropy_pos ⟨by linarith [ht.1], ht.2⟩
  have hA := div_nonpos_of_nonpos_of_nonneg
    (entropyHyperbolicSlope_nonpos ⟨ht.1.le, ht.2.le⟩) hH.le
  unfold logScaledSlope
  linarith

theorem hasDerivAt_logScaledSlope {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt logScaledSlope
      (-1/((1-t^2)*phiSlope t^2)+1/t^2+
        (profileAux t^2-phiSlope t^2-meanEntropy t)/meanEntropy t^2) t := by
  have hd : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hg := ne_of_gt (gap_pos hd)
  have hv := ne_of_gt (phiSlope_pos ht)
  have hH := ne_of_gt (meanEntropy_pos hd)
  have ht0 := ne_of_gt ht.1
  have h := (((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_phiSlope hd) hv).sub
    ((hasDerivAt_const t (1 : ℝ)).div (hasDerivAt_id t) ht0)).add
    ((hasDerivAt_entropyHyperbolicSlope hd).div (hasDerivAt_meanEntropy hd) hH)
  apply h.congr_deriv
  dsimp only [id_eq]
  rw [entropyHyperbolicSlope_eq hd]
  have hL : profileAux t=meanEntropy t+t*phiSlope t := (meanEntropy_add_slope hd).symm
  rw [hL]
  field_simp [hg, hv, hH, ht0]
  ring

theorem logScaledSlope_derivative_neg {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    -1/((1-t^2)*phiSlope t^2)+1/t^2+
        (profileAux t^2-phiSlope t^2-meanEntropy t)/meanEntropy t^2 < 0 := by
  have hd : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have hg := gap_pos hd
  have hv := phiSlope_pos ht
  have hH := meanEntropy_pos hd
  have hvbound : phiSlope t ≤ t/Real.sqrt (1-t^2) := by
    rw [phiSlope_eq_artanh hd, ← Real.sinh_artanh hd]
    exact Real.self_le_sinh_iff.mpr (Real.artanh_nonneg ht.1.le)
  have hmul := (le_div_iff₀ (Real.sqrt_pos.mpr hg)).mp hvbound
  have hs := mul_self_le_mul_self (mul_nonneg hv.le (Real.sqrt_nonneg _)) hmul
  have hsq : (1-t^2)*phiSlope t^2 ≤ t^2 := by
    have hh : (phiSlope t * Real.sqrt (1-t^2))^2 ≤ t^2 := by simpa only [pow_two] using hs
    rw [mul_pow, Real.sq_sqrt hg.le] at hh
    nlinarith only [hh]
  have hrec := one_div_le_one_div_of_le (mul_pos hg (sq_pos_of_pos hv)) hsq
  have hcurv := div_neg_of_neg_of_pos (profile_curvature_negative ht) (sq_pos_of_pos hH)
  simp only [neg_div] at *
  linarith only [hrec, hcurv]

theorem elasticity_eq {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    elasticity t = phiSlope t*(1-t^2)*profileAux t/(t*meanEntropy t) := by
  have hd : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  unfold elasticity logScaledSlope
  rw [entropyHyperbolicSlope_eq hd,
    show profileAux t=meanEntropy t+t*phiSlope t from (meanEntropy_add_slope hd).symm]
  field_simp [ne_of_gt (phiSlope_pos ht), ne_of_gt (meanEntropy_pos hd), ne_of_gt ht.1]
  ring

theorem elasticity_ge_one {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 1 ≤ elasticity t := by
  have h := mul_nonpos_of_nonneg_of_nonpos (phiSlope_pos ht).le (logScaledSlope_nonpos ht)
  unfold elasticity
  linarith

theorem hasDerivAt_elasticity {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt elasticity
      (-logScaledSlope t/(1-t^2)-phiSlope t*
        (-1/((1-t^2)*phiSlope t^2)+1/t^2+
          (profileAux t^2-phiSlope t^2-meanEntropy t)/meanEntropy t^2)) t := by
  have h := (((hasDerivAt_phiSlope ⟨by linarith [ht.1], ht.2⟩).mul
    (hasDerivAt_logScaledSlope ht)).const_sub 1)
  apply h.congr_deriv
  ring

theorem elasticity_strictMono : StrictMonoOn elasticity (Ioo (0 : ℝ) 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ioo 0 1)
    (fun t ht => (hasDerivAt_elasticity ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hasDerivAt_elasticity (by simpa using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    have ha := div_nonneg (neg_nonneg.mpr (logScaledSlope_nonpos ht'))
      (gap_pos ⟨by linarith [ht'.1], ht'.2⟩).le
    have hb := mul_neg_of_pos_of_neg (phiSlope_pos ht') (logScaledSlope_derivative_neg ht')
    linarith only [ha, hb]

theorem scaledProfile_pos {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) : 0 < scaledProfile t :=
  div_pos (mul_pos (phiSlope_pos ht) (meanEntropy_pos ⟨by linarith [ht.1], ht.2⟩)) ht.1

theorem hasDerivAt_scaledProfile {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt scaledProfile (scaledProfile t*logScaledSlope t/(1-t^2)) t := by
  have hd : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have h := ((hasDerivAt_phiSlope hd).mul (hasDerivAt_meanEntropy hd)).div
    (hasDerivAt_id t) (ne_of_gt ht.1)
  apply h.congr_deriv
  dsimp only [id_eq, Pi.mul_apply, scaledProfile, logScaledSlope]
  rw [entropyHyperbolicSlope_eq hd,
    show profileAux t=meanEntropy t+t*phiSlope t from (meanEntropy_add_slope hd).symm]
  field_simp [ne_of_gt (phiSlope_pos ht), ne_of_gt (meanEntropy_pos hd),
    ne_of_gt (gap_pos hd), ne_of_gt ht.1]
  ring

theorem scaledProfile_antitone : AntitoneOn scaledProfile (Ioo (0 : ℝ) 1) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioo 0 1)
    (fun t ht => (hasDerivAt_scaledProfile ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hasDerivAt_scaledProfile (by simpa using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (scaledProfile_pos ht').le (logScaledSlope_nonpos ht'))
      (gap_pos ⟨by linarith [ht'.1], ht'.2⟩).le

end
end CK.Profile
