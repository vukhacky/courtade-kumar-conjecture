module

public import CK.Profile.Elasticity
public import CK.Profile.Convex
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Concavity of x ↦ B_e(sqrt x), including x=0. The inverse derivative
is justified from the proved root equation and continuity. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem profilePoint_div_left {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    profilePoint e q = profilePoint (e/q) 1 := by
  have hs := profilePoint_spec he hq
  apply profilePoint_unique (div_pos he hq) (by norm_num) hs.1
  have h := hs.2
  field_simp [ne_of_gt hq]
  simpa only [one_mul, mul_comm, mul_left_comm, mul_assoc] using h

theorem continuousAt_profilePoint_right {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    ContinuousAt (profilePoint e) q := by
  have hc := (continuousAt_profilePoint (div_pos he hq) (by norm_num : (0 : ℝ) < 1)).comp
    (continuousAt_const.div continuousAt_id (ne_of_gt hq))
  have heq : profilePoint e =ᶠ[nhds q] fun r => profilePoint (e/r) 1 := by
    filter_upwards [Ioi_mem_nhds hq] with r hr
    exact profilePoint_div_left he hr
  exact hc.congr heq.symm

theorem profilePoint_mono_right {e : ℝ} (he : 0 < e) :
    MonotoneOn (profilePoint e) (Ioi (0 : ℝ)) := by
  intro q hq r hr hqr
  have hs := profilePoint_spec he hq
  have ht := profilePoint_spec he hr
  by_contra h
  have hlt : profilePoint e r < profilePoint e q := lt_of_not_ge h
  have hH := strictAntiOn_meanEntropy ⟨ht.1.1.le, ht.1.2.le⟩
    ⟨hs.1.1.le, hs.1.2.le⟩ hlt
  have h1 := mul_lt_mul_of_pos_left hH hq
  have h2 := mul_le_mul_of_nonneg_right hqr
    (meanEntropy_pos ⟨by linarith [ht.1.1], ht.1.2⟩).le
  have h3 := mul_lt_mul_of_pos_left hlt he
  linarith only [hs.2, ht.2, h1, h2, h3]

theorem hasDerivAt_profileParameter {e t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => e*s/meanEntropy s)
      (e*profileAux t/meanEntropy t^2) t := by
  have hd : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have h := ((hasDerivAt_id t).const_mul e).div (hasDerivAt_meanEntropy hd)
    (ne_of_gt (meanEntropy_pos hd))
  apply h.congr_deriv
  dsimp only [id_eq]
  rw [show profileAux t=meanEntropy t+t*phiSlope t from (meanEntropy_add_slope hd).symm]
  ring

theorem hasDerivAt_profilePoint_right {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    HasDerivAt (profilePoint e)
      (meanEntropy (profilePoint e q)^2/(e*profileAux (profilePoint e q))) q := by
  have hs := profilePoint_spec he hq
  have hd : profilePoint e q ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1.1], hs.1.2⟩
  have hH := ne_of_gt (meanEntropy_pos hd)
  have hL := ne_of_gt (profileAux_pos hd)
  have heq : ∀ᶠ r in nhds q, e*profilePoint e r/meanEntropy (profilePoint e r)=r := by
    filter_upwards [Ioi_mem_nhds hq] with r hr
    have ht := profilePoint_spec he hr
    rw [ht.2]
    exact mul_div_cancel_right₀ r
      (ne_of_gt (meanEntropy_pos ⟨by linarith [ht.1.1], ht.1.2⟩))
  have h := HasDerivAt.of_local_left_inverse (continuousAt_profilePoint_right he hq)
    (hasDerivAt_profileParameter hs.1)
    (ne_of_gt (div_pos (mul_pos he (profileAux_pos hd)) (sq_pos_of_pos (meanEntropy_pos hd)))) heq
  apply h.congr_deriv
  field_simp [hH, hL, ne_of_gt he]

theorem hasDerivAt_profile_right {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    HasDerivAt (profile e)
      (phiSlope (profilePoint e q)*(1+1/elasticity (profilePoint e q))) q := by
  have hs := profilePoint_spec he hq
  have hd : profilePoint e q ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1.1], hs.1.2⟩
  have hH := ne_of_gt (meanEntropy_pos hd)
  have hL := ne_of_gt (profileAux_pos hd)
  have hv := ne_of_gt (phiSlope_pos hs.1)
  have hg := ne_of_gt (gap_pos hd)
  have ht0 := ne_of_gt hs.1.1
  have hqeq : q=e*profilePoint e q/meanEntropy (profilePoint e q) := by
    rw [hs.2]
    exact (mul_div_cancel_right₀ q hH).symm
  have hh := (hasDerivAt_id q).mul
    ((hasDerivAt_phiSlope hd).comp q (hasDerivAt_profilePoint_right he hq))
  have heq : profile e =ᶠ[nhds q] fun r => r*phiSlope (profilePoint e r) := by
    filter_upwards [Ioi_mem_nhds hq] with r hr
    have hdom := (profilePoint_spec he hr).1
    unfold profile
    rw [phiSlope_eq_artanh ⟨by linarith [hdom.1], hdom.2⟩]
  apply (hh.congr_of_eventuallyEq heq).congr_deriv
  dsimp only [id_eq, Function.comp_def]
  rw [elasticity_eq hs.1]
  generalize htp : profilePoint e q = t at *
  rw [hqeq]
  field_simp [hH, hL, hv, hg, ht0, ne_of_gt he]

theorem continuous_profile_signed {e : ℝ} (he : 0 < e) :
    Continuous (fun q => profile e |q|) := by
  have hc : ConvexOn ℝ (univ : Set ℝ) (fun q => profile e |q|) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have h := profile_signed_convex_combination (q₁ := x) (q₂ := y) he he ha hb hab
    have heq : a*e+b*e=e := by rw [← add_mul, hab, one_mul]
    simpa only [smul_eq_mul, heq] using h
  exact continuousOn_univ.mp (hc.continuousOn isOpen_univ)

theorem continuous_profile_sqrt {e : ℝ} (he : 0 < e) :
    Continuous (fun x => profile e (Real.sqrt x)) := by
  have h := (continuous_profile_signed he).comp Real.continuous_sqrt
  simpa only [Function.comp_def, abs_of_nonneg (Real.sqrt_nonneg _)] using h

def squaredProfileSlope (e x : ℝ) : ℝ :=
  scaledProfile (profilePoint e (Real.sqrt x))/(2*e)*
    (1+1/elasticity (profilePoint e (Real.sqrt x)))

theorem hasDerivAt_profile_sqrt {e x : ℝ} (he : 0 < e) (hx : 0 < x) :
    HasDerivAt (fun y => profile e (Real.sqrt y)) (squaredProfileSlope e x) x := by
  have hq := Real.sqrt_pos.mpr hx
  have hs := profilePoint_spec he hq
  have hH := ne_of_gt (meanEntropy_pos ⟨by linarith [hs.1.1], hs.1.2⟩)
  have hq0 := ne_of_gt hq
  have ht0 := ne_of_gt hs.1.1
  have hqeq : Real.sqrt x=e*profilePoint e (Real.sqrt x)/meanEntropy (profilePoint e (Real.sqrt x)) := by
    rw [hs.2]
    exact (mul_div_cancel_right₀ _ hH).symm
  have h := (hasDerivAt_profile_right he hq).comp x ((hasDerivAt_id x).sqrt (ne_of_gt hx))
  apply h.congr_deriv
  unfold squaredProfileSlope scaledProfile
  dsimp only [id_eq]
  generalize htp : profilePoint e (Real.sqrt x) = t at *
  rw [hqeq]
  field_simp [hH, ht0, ne_of_gt he]

theorem squaredProfileSlope_antitone {e : ℝ} (he : 0 < e) :
    AntitoneOn (squaredProfileSlope e) (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hxq := Real.sqrt_pos.mpr hx
  have hyq := Real.sqrt_pos.mpr hy
  have hs := (profilePoint_spec he hxq).1
  have ht := (profilePoint_spec he hyq).1
  have hst := profilePoint_mono_right he hxq hyq (Real.sqrt_le_sqrt hxy)
  have hV := scaledProfile_antitone hs ht hst
  have hK := elasticity_strictMono.monotoneOn hs ht hst
  have hKx : 0 < elasticity (profilePoint e (Real.sqrt x)) := by
    linarith [elasticity_ge_one hs]
  have hKy : 0 < elasticity (profilePoint e (Real.sqrt y)) := by
    linarith [elasticity_ge_one ht]
  have hrec := one_div_le_one_div_of_le hKx hK
  unfold squaredProfileSlope
  exact mul_le_mul
    (div_le_div_of_nonneg_right hV (by positivity))
    (by linarith only [hrec])
    (by positivity)
    (div_nonneg (scaledProfile_pos hs).le (by positivity))

/-- Source `u963:scalar`, in the non-strict form sufficient for profile
packing. Zero is included by a proved continuous extension. -/
theorem concaveOn_profile_sqrt {e : ℝ} (he : 0 < e) :
    ConcaveOn ℝ (Ici (0 : ℝ)) (fun x => profile e (Real.sqrt x)) := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    (continuous_profile_sqrt he).continuousOn
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    exact (hasDerivAt_profile_sqrt he hx').differentiableAt.differentiableWithinAt
  · intro x hx y hy hxy
    have hx' : 0 < x := by simpa only [interior_Ici, mem_Ioi] using hx
    have hy' : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
    rw [(hasDerivAt_profile_sqrt he hx').deriv, (hasDerivAt_profile_sqrt he hy').deriv]
    exact squaredProfileSlope_antitone he hx' hy' hxy

end
end CK.Profile
