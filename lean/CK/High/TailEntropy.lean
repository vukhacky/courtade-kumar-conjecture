module

public import CK.High.TailBasics

/-! Exact entropy and mean-transfer estimates on the infinite tail. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem tail_tanh_mem {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    Real.tanh u ∈ Ioo (0 : ℝ) 1 := by
  have hlog : Real.log 9 ≤ u := by linarith [log_nine_bounds.2]
  have hd := exp_neg_mem_small_delta hlog
  have hp := localNoiseProbability_bounds hd
  have hs : Real.exp (-u)^2 ≤ (1/9 : ℝ)^2 := pow_le_pow_left₀ hd.1.le hd.2 2
  refine ⟨?_,Real.tanh_lt_one u⟩
  rw [tanh_eq_localNoiseProbability]
  nlinarith only [hp.2.1,hs]

theorem tanh_square_exp_identity (u : ℝ) :
    1-Real.tanh u^2=4*Real.exp (-u)^2/(1+Real.exp (-u)^2)^2 := by
  rw [tanh_eq_localNoiseProbability,localNoiseProbability]
  field_simp
  <;> ring

theorem tanh_square_tail_bound (u : ℝ) :
    1-Real.tanh u^2 < 4*Real.exp (-u)^2 := by
  rw [tanh_square_exp_identity]
  have he2 : 0 < Real.exp (-u)^2 := sq_pos_of_pos (Real.exp_pos _)
  have hden : (1 : ℝ) < (1+Real.exp (-u)^2)^2 := by nlinarith only [he2,sq_nonneg (Real.exp (-u)^2)]
  apply (div_lt_iff₀ (show 0 < (1+Real.exp (-u)^2)^2 by positivity)).mpr
  nlinarith only [mul_pos (by positivity : 0 < 4*Real.exp (-u)^2) (sub_pos.mpr hden)]

theorem signEntropy_tanh_upper {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    signEntropy (Real.tanh u) ≤ (2*u+1)*Real.exp (-u)^2 := by
  have hlog : Real.log 9 ≤ u := by linarith [log_nine_bounds.2]
  have hd := exp_neg_mem_small_delta hlog
  have hb := binEntropy_localNoiseProbability_upper hd
  rw [Real.log_exp,neg_neg] at hb
  have hid : signEntropy (Real.tanh u)=Real.binEntropy (localNoiseProbability (Real.exp (-u))) := by
    rw [signEntropy,tanh_eq_localNoiseProbability]
    congr 1
    ring
  rw [hid]
  apply hb.trans
  unfold localNoiseProbability
  have hden : 0 < 1+Real.exp (-u)^2 := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  have he : (Real.exp (-u)^2/(1+Real.exp (-u)^2)*(2*u+Real.exp (-u)^2+1))*(1+Real.exp (-u)^2)=
      Real.exp (-u)^2*(2*u+Real.exp (-u)^2+1) := by field_simp
  rw [he]
  have hp := mul_nonneg (show 0 ≤ u by linarith) (pow_nonneg (Real.exp_pos (-u)).le 4)
  nlinarith only [hp]

theorem entropyRemainder_le_signEntropy {r : ℝ} (hr : r ∈ Icc (-1 : ℝ) 1) :
    entropyRemainder r ≤ signEntropy r := by
  have h0 : 0 ≤ 1+r := by linarith [hr.1]
  have h1 : 0 ≤ 1-r := by linarith [hr.2]
  have hprod := mul_nonneg h0 h1
  have hs : r^2 ≤ 1 := by nlinarith only [hprod]
  have hm := mul_le_mul_of_nonneg_right hs (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [signEntropy_eq_log_two_sub_phi,entropyRemainder]
  linarith only [hm]

theorem tail_entropy_penalty_le {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    tailGamma u*Certificate.arcsineSharpConstant*entropyRemainder (Real.tanh u) ≤
      (3/7)*(2*u+1)*Real.exp (-u) := by
  have hr := tail_tanh_mem hu
  have hr' : Real.tanh u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [hr.1],hr.2.le⟩
  have hΨ := (entropyRemainder_le_signEntropy hr').trans (signEntropy_tanh_upper hu)
  have hC := mul_le_mul_of_nonneg_right Certificate.arcsineSharpConstant_bounds.2.le
    (entropyRemainder_nonneg hr')
  have hH := mul_le_mul_of_nonneg_left hΨ (by norm_num : (0 : ℝ) ≤ 12/7)
  have hγ : 0 ≤ tailGamma u := by unfold tailGamma; positivity
  have hmul := mul_le_mul_of_nonneg_left (hC.trans hH) hγ
  have hid : tailGamma u*((12/7)*((2*u+1)*Real.exp (-u)^2)) =
      (3/7)*(2*u+1)*Real.exp (-u) := by
    unfold tailGamma
    have he : Real.exp u*Real.exp (-u)=1 := by rw [← Real.exp_add]; simp
    nlinarith only [congrArg (fun x : ℝ => (3/7)*(2*u+1)*Real.exp (-u)*x) he]
  rw [hid] at hmul
  nlinarith only [hmul]

theorem tail_entropy_penalty_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    tailGamma u*Certificate.arcsineSharpConstant*entropyRemainder (Real.tanh u) < 1/300 :=
  (tail_entropy_penalty_le hu).trans_lt (tail_entropy_error hu)

end
end CK
