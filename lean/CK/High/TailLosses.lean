module

public import CK.High.TailNumerator

/-! Uniform multiplier corrections in the analytic tail. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem shiftedMultiplier_drop_identity {γ t a : ℝ}
    (h1 : γ+t ≠ 0) (h2 : γ+t-a ≠ 0) :
    shiftedMultiplier γ t-shiftedMultiplier γ (t-a)=γ^2*a/((γ+t)*(γ+t-a)) := by
  unfold shiftedMultiplier
  have h2' : γ+(t-a) ≠ 0 := by simpa only [add_sub_assoc] using h2
  field_simp
  <;> ring

theorem shiftedMultiplier_drop_bounds {γ t a : ℝ}
    (ha : 0 < a) (hag : a < γ) (ht : 0 < t) :
    0 < shiftedMultiplier γ t-shiftedMultiplier γ (t-a) ∧
      shiftedMultiplier γ t-shiftedMultiplier γ (t-a) < γ*a/(γ-a) := by
  have hγ : 0 < γ := ha.trans hag
  have hga : 0 < γ-a := sub_pos.mpr hag
  have h1 : 0 < γ+t := by linarith
  have h2 : 0 < γ+t-a := by linarith
  rw [shiftedMultiplier_drop_identity h1.ne' h2.ne']
  constructor
  · exact div_pos (mul_pos (sq_pos_of_pos hγ) ha) (mul_pos h1 h2)
  · have hden : γ*(γ-a) < (γ+t)*(γ+t-a) := by
      have h := mul_pos ht (show 0 < 2*γ+t-a by linarith)
      nlinarith only [h]
    have h := div_lt_div_of_pos_left (mul_pos (sq_pos_of_pos hγ) ha)
      (mul_pos hγ hga) hden
    have he : γ^2*a/(γ*(γ-a))=γ*a/(γ-a) := by field_simp
    rwa [he] at h

theorem shiftedMultiplier_two_gt_one {γ : ℝ} (hγ : (2 : ℝ) < γ) :
    1 < shiftedMultiplier γ 2 := by
  unfold shiftedMultiplier
  exact (lt_div_iff₀ (by linarith : 0 < γ+2)).mpr (by linarith)

theorem shiftedMultiplier_step_lt_one {γ : ℝ} (hγ : 0 < γ) :
    shiftedMultiplier γ 2-shiftedMultiplier γ 1 < 1 := by
  have he : shiftedMultiplier γ 2-shiftedMultiplier γ 1=γ^2/((γ+1)*(γ+2)) := by
    unfold shiftedMultiplier
    field_simp
    <;> ring
  rw [he]
  exact (div_lt_one (mul_pos (by linarith) (by linarith))).mpr (by nlinarith only [hγ])

theorem spectralDelta_difference_bound {γ t ρ : ℝ}
    (hγ : 0 < γ) (ht : (2 : ℝ) ≤ t) (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    spectralDeltaOne γ t ρ-spectralDeltaTwo γ t ρ ≤
      shiftedMultiplier γ 2-shiftedMultiplier γ 1+(1-ρ^2)*shiftedMultiplier γ t := by
  have hr : 0 ≤ 1-ρ^2 := by nlinarith only [hρ.1,hρ.2]
  have h12 := shiftedMultiplier_monotone (γ := γ) (s := 1) (by linarith) (by norm_num : (1 : ℝ) ≤ 2)
  have h2 := shiftedMultiplier_nonneg hγ (by norm_num : (0 : ℝ) ≤ 2)
  have htk := shiftedMultiplier_nonneg hγ (show 0 ≤ t by linarith)
  have ha := mul_nonneg hr (sub_nonneg.mpr h12)
  have hb := mul_nonneg htk (sq_nonneg (1-ρ^2))
  have hc := mul_nonneg (mul_nonneg h2 (sq_nonneg ρ)) hr
  unfold spectralDeltaOne spectralDeltaTwo
  nlinarith only [ha,hb,hc]

theorem tail_delta_two_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u) < u/2 := by
  have ht := (tail_parameter_domains hu).1
  have ht0 : 0 < tailT u := by linarith
  have hγt := tailGamma_gt_ten_t hu
  have hγ : (2 : ℝ) < tailGamma u := by linarith
  have htwo := shiftedMultiplier_two_gt_one hγ
  have hkt := (shiftedMultiplier_source_bounds (by linarith : 0 < tailGamma u) ht0).2.1
  have hdiff : 0 ≤ shiftedMultiplier (tailGamma u) (tailT u)-shiftedMultiplier (tailGamma u) 2 :=
    sub_nonneg.mpr (shiftedMultiplier_monotone (by linarith) ht)
  have hr := tail_tanh_mem hu
  have hr4 : Real.tanh u^4 ≤ 1 := pow_le_one₀ hr.1.le hr.2.le
  have hm := mul_le_mul_of_nonneg_left hr4 hdiff
  unfold spectralDeltaTwo
  unfold tailT at ht hkt hm ⊢
  nlinarith only [hm,hkt,htwo]

theorem tail_delta_difference_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    spectralDeltaOne (tailGamma u) (tailT u) (Real.tanh u)-
      spectralDeltaTwo (tailGamma u) (tailT u) (Real.tanh u) < 2 := by
  have ht := (tail_parameter_domains hu).1
  have ht0 : 0 < tailT u := by linarith
  have hγ : 0 < tailGamma u := by unfold tailGamma; positivity
  have hr := tail_tanh_mem hu
  have hr2 : 0 ≤ 1-Real.tanh u^2 := by nlinarith only [hr.1,hr.2]
  have hD := spectralDelta_difference_bound hγ ht ⟨hr.1.le,hr.2.le⟩
  have hstep := shiftedMultiplier_step_lt_one hγ
  have hkt := (shiftedMultiplier_source_bounds hγ ht0).2.1
  have hmul := mul_le_mul_of_nonneg_left hkt.le hr2
  have hsmall := mul_lt_mul_of_pos_right (tanh_square_tail_bound u) ht0
  have herror := tail_error_decay hu
  have hpos : 0 ≤ (u+2)^2*Real.exp (-u) := by positivity
  nlinarith only [hD,hstep,hmul,hsmall,herror,hpos]

theorem tail_outside_multiplier_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    spectralDeltaOutside (tailGamma u) (tailT u) (Real.tanh u) <
      Real.exp u/(2*(Real.exp 1-2)) := by
  let a := Real.exp (2*tailT u-3)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : 0 < tailT u := by unfold tailT; linarith
  have he : a=Real.exp u/(2*Real.exp 1) := by
    dsimp [a]
    rw [tailT,show 2*(u/2+1)-3=u-1 by ring,Real.exp_sub]
    ring
  have haγ : a < tailGamma u := by
    rw [he,tailGamma]
    apply (div_lt_div_iff₀ (mul_pos (by norm_num) (Real.exp_pos 1)) (by norm_num : (0 : ℝ) < 4)).mpr
    have h := mul_pos (Real.exp_pos u) (sub_pos.mpr Real.exp_one_gt_two)
    nlinarith only [h]
  have hdrop := shiftedMultiplier_drop_bounds ha haγ ht
  have hid : tailGamma u*a/(tailGamma u-a)=Real.exp u/(2*(Real.exp 1-2)) := by
    have hd : tailGamma u-a ≠ 0 := (sub_pos.mpr haγ).ne'
    apply (div_eq_div_iff hd (mul_ne_zero (by norm_num) (sub_pos.mpr Real.exp_one_gt_two).ne')).mpr
    rw [he,tailGamma]
    field_simp
    <;> ring
  rw [hid] at hdrop
  have hr := tail_tanh_mem hu
  have hr2 : Real.tanh u^2 ≤ 1 := by nlinarith only [hr.1,hr.2]
  have hm := mul_le_mul_of_nonneg_left hr2 hdrop.1.le
  change (shiftedMultiplier (tailGamma u) (tailT u)-shiftedMultiplier (tailGamma u) (tailT u-a))*Real.tanh u^2 < _
  nlinarith only [hm,hdrop.2]

end
end CK
