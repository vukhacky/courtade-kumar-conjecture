module

public import CK.High.Majorants

/-! The explicit inverse estimate from the STOC compact-range argument.
Every estimate is proved on the full indicated real interval. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem profileHeight_log_heightF {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    Real.log a+Real.log (heightF (profileHeight (Real.tanh u) a))=Real.log (heightF u) := by
  have hr := tanh_mem_Ioo_positive hu
  have hv := profileHeight_pos hr ha
  have hid : a=heightF u/heightF (profileHeight (Real.tanh u) a) := by
    rw [←profileCoefficient_tanh_eq hu hv,profileCoefficient_profileHeight hr ha]
  have hl := congrArg Real.log hid
  rw [Real.log_div (heightF_pos hu).ne' (heightF_pos hv).ne'] at hl
  linarith only [hl]

theorem profileHeight_lt_height {u a : ℝ} (hu : 0 < u) (ha : a ∈ Ioo (0 : ℝ) 1) :
    profileHeight (Real.tanh u) a < u := by
  have hr := tanh_mem_Ioo_positive hu
  have h := (profileHeight_strictMono hr) ha.1.le (show (0 : ℝ) ≤ 1 by norm_num) ha.2
  rw [profileHeight_one hr,Real.artanh_tanh] at h
  exact h

theorem log_heightF_add_height_strictAnti :
    StrictAntiOn (fun v => Real.log (heightF v)+v) (Ioi (0 : ℝ)) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (f' := fun v => -heightDecayRate v+1) (convex_Ioi _)
  · intro v hv
    exact ((hasDerivAt_log_heightF hv).add (hasDerivAt_id v)).continuousAt.continuousWithinAt
  · intro v hv
    exact ((hasDerivAt_log_heightF (by simpa using hv)).add (hasDerivAt_id v)).hasDerivWithinAt
  · intro v hv
    linarith only [heightDecayRate_gt_one (show 0 < v by simpa using hv)]

theorem profileHeight_inverse_coarse {u a : ℝ} (hu : 0 < u) (ha : a ∈ Ioo (0 : ℝ) 1) :
    u+Real.log a < profileHeight (Real.tanh u) a := by
  have hw := profileHeight_pos (tanh_mem_Ioo_positive hu) ha.1
  have hwu := profileHeight_lt_height hu ha
  have hm := log_heightF_add_height_strictAnti hw hu hwu
  have hl := profileHeight_log_heightF hu ha.1
  linarith only [hm,hl]

theorem log_heightF_upper_rate_strictMono {u : ℝ} (hu : (2 : ℝ) ≤ u) :
    StrictMonoOn (fun v => Real.log (heightF v)+(2-1/(2*u+1))*v) (Icc (2 : ℝ) u) := by
  have hd (v : ℝ) (hv : (2 : ℝ) ≤ v) :
      HasDerivAt (fun v => Real.log (heightF v)+(2-1/(2*u+1))*v)
        (-heightDecayRate v+(2-1/(2*u+1))) v := by
    have hv0 : 0 < v := by linarith
    have h := (hasDerivAt_log_heightF hv0).add
      ((hasDerivAt_id v).const_mul (2-1/(2*u+1)))
    apply h.congr_deriv
    simp
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (f' := fun v => -heightDecayRate v+(2-1/(2*u+1))) (convex_Icc _ _)
  · intro v hv
    exact (hd v hv.1).continuousAt.continuousWithinAt
  · intro v hv
    have hm : v ∈ Ioo (2 : ℝ) u := by simpa using hv
    exact (hd v hm.1.le).hasDerivWithinAt
  · intro v hv
    have hm : v ∈ Ioo (2 : ℝ) u := by simpa using hv
    have hb := (heightDecayRate_bounds hm.1.le).2
    have hrec : 1/(2*u+1) ≤ 1/(2*v+1) :=
      one_div_le_one_div_of_le (by linarith only [hm.1] : 0 < 2*v+1) (by linarith only [hm.2])
    linarith only [hb,hrec]

def explicitInverseHeight (u a : ℝ) : ℝ := u+(2*u+1)*Real.log a/(4*u+1)

theorem explicitInverseHeight_le {u a : ℝ} (hu : (2 : ℝ) < u)
    (ha : a ∈ Ioc (0 : ℝ) 1) : explicitInverseHeight u a ≤ u := by
  unfold explicitInverseHeight
  have hl : Real.log a ≤ 0 := Real.log_nonpos ha.1.le ha.2
  have hn := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ 2*u+1) hl)
    (by linarith : 0 ≤ 4*u+1)
  linarith only [hn]

theorem explicitInverseHeight_lower {u a : ℝ} (hu : (2 : ℝ) < u)
    (ha : a ∈ Ioc (0 : ℝ) 1) (haexp : Real.exp (2-u) ≤ a) :
    (2 : ℝ) ≤ profileHeight (Real.tanh u) a ∧
      profileHeight (Real.tanh u) a ≤ explicitInverseHeight u a := by
  have hu0 : 0 < u := by linarith
  by_cases ha1 : a=1
  · subst a
    rw [profileHeight_one (tanh_mem_Ioo_positive hu0),Real.artanh_tanh]
    simp only [explicitInverseHeight,Real.log_one,mul_zero,zero_div,add_zero]
    exact ⟨hu.le,le_rfl⟩
  have ha' : a ∈ Ioo (0 : ℝ) 1 := ⟨ha.1,lt_of_le_of_ne ha.2 ha1⟩
  have hcoarse := profileHeight_inverse_coarse hu0 ha'
  have hlog : 2-u ≤ Real.log a := by
    have h := Real.log_le_log (Real.exp_pos (2-u)) haexp
    rwa [Real.log_exp] at h
  have hw : (2 : ℝ) < profileHeight (Real.tanh u) a := by linarith only [hcoarse,hlog]
  have hwu := profileHeight_lt_height hu0 ha'
  have hm := log_heightF_upper_rate_strictMono hu.le
    ⟨hw.le,hwu.le⟩ ⟨hu.le,le_rfl⟩ hwu
  have hl := profileHeight_log_heightF hu0 ha.1
  have hrate : 2-1/(2*u+1)=(4*u+1)/(2*u+1) := by field_simp; ring
  dsimp only at hm
  rw [hrate] at hm
  have hd : 0 < 2*u+1 := by linarith
  have hm' := mul_lt_mul_of_pos_right hm hd
  have hmclean : Real.log (heightF (profileHeight (Real.tanh u) a))*(2*u+1)+
      (4*u+1)*profileHeight (Real.tanh u) a <
      Real.log (heightF u)*(2*u+1)+(4*u+1)*u := by
    convert hm' using 1 <;> field_simp <;> ring
  have hmain : (4*u+1)*profileHeight (Real.tanh u) a <
      (4*u+1)*u+(2*u+1)*Real.log a := by
    rw [←hl] at hmclean
    nlinarith only [hmclean]
  refine ⟨hw.le,?_⟩
  unfold explicitInverseHeight
  apply (mul_le_mul_iff_right₀ (by linarith : 0 < 4*u+1)).mp
  have he : (u+(2*u+1)*Real.log a/(4*u+1))*(4*u+1)=
      (4*u+1)*u+(2*u+1)*Real.log a := by field_simp
  nlinarith only [he,hmain]

def normalizedScaledHeightF (v : ℝ) : ℝ := scaledHeightF v/(2*v+1)

theorem normalizedScaledHeightF_antitone :
    AntitoneOn normalizedScaledHeightF (Ici (2 : ℝ)) := by
  have hd (v : ℝ) (hv : (2 : ℝ) ≤ v) :
      HasDerivAt normalizedScaledHeightF
        ((scaledHeightFSlope v*(2*v+1)-2*scaledHeightF v)/(2*v+1)^2) v := by
    have h := (hasDerivAt_scaledHeightF (show 0 < v by linarith)).div
      (((hasDerivAt_id v).const_mul 2).add_const 1) (by linarith : 2*v+1 ≠ 0)
    apply h.congr_deriv
    dsimp
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun v => (scaledHeightFSlope v*(2*v+1)-2*scaledHeightF v)/(2*v+1)^2)
    (convex_Ici _)
  · intro v hv
    exact (hd v hv).continuousAt.continuousWithinAt
  · intro v hv
    have h : (2 : ℝ) < v := by simpa using hv
    exact (hd v h.le).hasDerivWithinAt
  · intro v hv
    have hv2 : (2 : ℝ) < v := by simpa using hv
    have h := (scaledHeightF_logSlope_bounds hv2.le).2
    have hn := (div_lt_iff₀ (scaledHeightF_pos (by linarith : 0 < v))).mp h
    apply div_nonpos_of_nonpos_of_nonneg
    · linarith only [hn]
    · positivity

theorem heightF_ratio_scaled_formula {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    heightF u/heightF v = Real.exp (-2*(u-v))*scaledHeightF u/scaledHeightF v := by
  rw [show -2*(u-v)=2*v-2*u by ring,Real.exp_sub]
  unfold scaledHeightF
  field_simp

theorem heightF_ratio_exp_upper {u v : ℝ} (hv : (2 : ℝ) ≤ v) (hvu : v ≤ u) :
    heightF u/heightF v ≤ Real.exp (-2*(u-v))*(2*u+1)/(2*v+1) := by
  have hv0 : 0 < v := by linarith
  have hu0 : 0 < u := hv0.trans_le hvu
  have h := normalizedScaledHeightF_antitone hv (hv.trans hvu) hvu
  unfold normalizedScaledHeightF at h
  have hc := (div_le_div_iff₀ (show 0 < 2*u+1 by linarith) (show 0 < 2*v+1 by linarith)).mp h
  have hr : scaledHeightF u/scaledHeightF v ≤ (2*u+1)/(2*v+1) := by
    apply (div_le_div_iff₀ (scaledHeightF_pos hv0) (show 0 < 2*v+1 by linarith)).mpr
    nlinarith only [hc]
  rw [heightF_ratio_scaled_formula hu0 hv0]
  have hm := mul_le_mul_of_nonneg_left hr (Real.exp_pos (-2*(u-v))).le
  simpa only [mul_div_assoc] using hm

theorem explicit_profile_inverse {u a : ℝ} (hu : (2 : ℝ) < u)
    (ha : a ∈ Ioc (0 : ℝ) 1) (haexp : Real.exp (2-u) ≤ a) :
    profileHeight (Real.tanh u) a ≤ explicitInverseHeight u a ∧
      explicitInverseHeight u a ≤ u ∧
      heightF u/heightF (explicitInverseHeight u a) ≤
        Real.exp (-2*(u-explicitInverseHeight u a))*(2*u+1)/(2*explicitInverseHeight u a+1) := by
  have hl := explicitInverseHeight_lower hu ha haexp
  have hh := explicitInverseHeight_le hu ha
  exact ⟨hl.2,hh,heightF_ratio_exp_upper (hl.1.trans hl.2) hh⟩

end
end CK
