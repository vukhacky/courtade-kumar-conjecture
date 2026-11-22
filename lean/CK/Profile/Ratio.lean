module

public import CK.Profile.Squared

/-! Ratios of fixed profiles decrease with the entropy variable.
This is the analytic input for propagating a certified clock to larger
correlations while keeping the coefficient envelope fixed. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem hasDerivAt_entropy_ratio {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s => meanEntropy s/s) (-profileAux t/t^2) t := by
  have hd : t ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
  have h := (hasDerivAt_meanEntropy hd).div (hasDerivAt_id t) (ne_of_gt ht.1)
  apply h.congr_deriv
  dsimp only [id_eq]
  rw [show profileAux t=meanEntropy t+t*phiSlope t from (meanEntropy_add_slope hd).symm]
  ring

theorem entropy_ratio_strictAnti :
    StrictAntiOn (fun t => meanEntropy t/t) (Ioo (0 : ℝ) 1) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioo 0 1)
    (fun t ht => (hasDerivAt_entropy_ratio ht).continuousAt.continuousWithinAt)
  · intro t ht
    exact (hasDerivAt_entropy_ratio (by simpa using ht)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa using ht
    exact div_neg_of_neg_of_pos
      (neg_neg_of_pos (profileAux_pos ⟨by linarith [ht'.1], ht'.2⟩)) (sq_pos_of_pos ht'.1)

theorem hasDerivAt_profilePoint_left {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    HasDerivAt (fun d => profilePoint d q)
      (-profilePoint e q^2/(q*profileAux (profilePoint e q))) e := by
  have hs := profilePoint_spec he hq
  have hd : profilePoint e q ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1.1], hs.1.2⟩
  have hder := (hasDerivAt_entropy_ratio hs.1).const_mul q
  have heq : ∀ᶠ d in nhds e, q*(meanEntropy (profilePoint d q)/profilePoint d q)=d := by
    filter_upwards [Ioi_mem_nhds he] with d hd
    have ht := profilePoint_spec hd hq
    rw [← mul_div_assoc, ← ht.2]
    exact mul_div_cancel_right₀ d (ne_of_gt ht.1.1)
  have hne : q*(-profileAux (profilePoint e q)/profilePoint e q^2) ≠ 0 :=
    mul_ne_zero (ne_of_gt hq) (div_ne_zero (neg_ne_zero.mpr (ne_of_gt (profileAux_pos hd)))
      (ne_of_gt (sq_pos_of_pos hs.1.1)))
  have h := HasDerivAt.of_local_left_inverse (continuousAt_profilePoint he hq) hder hne heq
  apply h.congr_deriv
  field_simp [ne_of_gt hq, ne_of_gt (profileAux_pos hd), ne_of_gt hs.1.1]

theorem hasDerivAt_profile_left {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    HasDerivAt (fun d => profile d q) (-tangentFactor (profilePoint e q)) e := by
  have hs := profilePoint_spec he hq
  have hd : profilePoint e q ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1.1], hs.1.2⟩
  have h := ((hasDerivAt_phiSlope hd).comp e (hasDerivAt_profilePoint_left he hq)).const_mul q
  have heq : (fun d => profile d q) =ᶠ[nhds e] fun d => q*phiSlope (profilePoint d q) := by
    filter_upwards [Ioi_mem_nhds he] with d hd
    have ht := (profilePoint_spec hd hq).1
    unfold profile
    rw [phiSlope_eq_artanh ⟨by linarith [ht.1], ht.2⟩]
  apply (h.congr_of_eventuallyEq heq).congr_deriv
  unfold tangentFactor
  field_simp [ne_of_gt hq, ne_of_gt (profileAux_pos hd), ne_of_gt (gap_pos hd)]

theorem profile_sensitivity_identity {e q : ℝ} (he : 0 < e) (hq : 0 < q) :
    tangentFactor (profilePoint e q) =
      profile e q/(e*elasticity (profilePoint e q)) := by
  have hs := profilePoint_spec he hq
  have hd : profilePoint e q ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1.1], hs.1.2⟩
  rw [elasticity_eq hs.1, profile, ← phiSlope_eq_artanh hd]
  unfold tangentFactor
  generalize htp : profilePoint e q=t at *
  have hH := ne_of_gt (meanEntropy_pos hd)
  have hL := ne_of_gt (profileAux_pos hd)
  have hg := ne_of_gt (gap_pos hd)
  have hv := ne_of_gt (phiSlope_pos hs.1)
  field_simp [hH, hL, hg, hv, ne_of_gt he, ne_of_gt hs.1.1]
  nlinarith only [hs.2]

theorem profile_ratio_antitone {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    AntitoneOn (fun e => profile e a/profile e 1) (Ioi (0 : ℝ)) := by
  have hder (e : ℝ) (he : 0 < e) : HasDerivAt
      (fun d => profile d a/profile d 1)
      ((-tangentFactor (profilePoint e a)*profile e 1+
        profile e a*tangentFactor (profilePoint e 1))/(profile e 1)^2) e := by
    have h := (hasDerivAt_profile_left he ha).div
      (hasDerivAt_profile_left he (by norm_num : (0 : ℝ) < 1))
      (ne_of_gt (profile_pos he (by norm_num : (0 : ℝ) < 1)))
    apply h.congr_deriv
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioi 0)
    (fun e he => (hder e he).continuousAt.continuousWithinAt)
  · intro e he
    exact (hder e (by simpa using he)).hasDerivWithinAt
  · intro e he
    have he' : 0 < e := by simpa using he
    have hs := (profilePoint_spec he' ha).1
    have ht := (profilePoint_spec he' (by norm_num : (0 : ℝ) < 1)).1
    have hst := profilePoint_mono_right he' ha (by norm_num : (0 : ℝ) < 1) ha1
    have hK := elasticity_strictMono.monotoneOn hs ht hst
    have hKa : 0 < elasticity (profilePoint e a) := by linarith [elasticity_ge_one hs]
    have hK1 : 0 < elasticity (profilePoint e 1) := by linarith [elasticity_ge_one ht]
    have hrec := one_div_le_one_div_of_le (mul_pos he' hKa)
      (mul_le_mul_of_nonneg_left hK he'.le)
    have hm := mul_le_mul_of_nonneg_left hrec
      (mul_pos (profile_pos he' ha) (profile_pos he' (by norm_num : (0 : ℝ) < 1))).le
    apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    rw [profile_sensitivity_identity he' ha,
      profile_sensitivity_identity he' (by norm_num : (0 : ℝ) < 1)]
    simp only [div_eq_mul_inv, one_mul] at hm ⊢
    nlinarith only [hm]

end
end CK.Profile
