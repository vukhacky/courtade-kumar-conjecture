module

public import CK.High.TailEntropy

/-! The spectral numerator and the mean-transfer condition for every
`u ≥ 8`, with the exact source choices of `t` and `γ`. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem shiftedMultiplier_source_identity {γ t : ℝ} (hden : γ+t ≠ 0) :
    shiftedMultiplier γ t=t-t^2/(γ+t) := by
  unfold shiftedMultiplier
  field_simp
  <;> ring

theorem shiftedMultiplier_source_bounds {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t) :
    0 < shiftedMultiplier γ t ∧ shiftedMultiplier γ t < t ∧
      t-t^2/γ < shiftedMultiplier γ t := by
  have hden : 0 < γ+t := by linarith
  constructor
  · exact div_pos (mul_pos hγ ht) hden
  rw [shiftedMultiplier_source_identity hden.ne']
  constructor
  · exact sub_lt_self _ (div_pos (sq_pos_of_pos ht) hden)
  · have h := div_lt_div_of_pos_left (sq_pos_of_pos ht) hγ (show γ < γ+t by linarith)
    linarith only [h]

theorem tail_multiplier_error_identity (u : ℝ) :
    tailT u^2/tailGamma u=(u+2)^2*Real.exp (-u) := by
  unfold tailT tailGamma
  rw [Real.exp_neg]
  field_simp
  <;> ring

theorem tail_multiplier_lower {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    u/2+9/10 < shiftedMultiplier (tailGamma u) (tailT u)*Real.tanh u^2 := by
  have ht : 0 < tailT u := by unfold tailT; linarith
  have hγ : 0 < tailGamma u := by unfold tailGamma; positivity
  have hk := shiftedMultiplier_source_bounds hγ ht
  have hr := tail_tanh_mem hu
  have hr2 : Real.tanh u^2 ≤ 1 := by nlinarith only [hr.1,hr.2]
  have hsmall := mul_le_mul_of_nonneg_right hr2 (sub_nonneg.mpr hk.2.1.le)
  have hrho := mul_lt_mul_of_pos_left (tanh_square_tail_bound u) ht
  have herror := tail_error_decay hu
  have he := tail_multiplier_error_identity u
  unfold tailT at ht he herror hrho
  change 0 < u/2+1 at ht
  dsimp [tailT] at hk hsmall ⊢
  nlinarith only [hk.2.2,hsmall,hrho,herror,he]

theorem tail_shiftedMultiplier_le_gamma {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    shiftedMultiplier (tailGamma u) (tailT u) ≤ tailGamma u/11 := by
  have hγ : 0 < tailGamma u := by unfold tailGamma; positivity
  have ht : 0 < tailT u := by unfold tailT; linarith
  have hγt := tailGamma_gt_ten_t hu
  unfold shiftedMultiplier
  apply (div_le_iff₀ (show 0 < tailGamma u+tailT u by positivity)).mpr
  have h := mul_le_mul_of_nonneg_left hγt.le hγ.le
  nlinarith only [h]

theorem tail_mean_transfer_pos {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    0 < meanTransferCoefficient
      ((Real.pi^2/4)*shiftedMultiplier (tailGamma u) (tailT u))
      (tailGamma u*Certificate.arcsineSharpConstant) (Real.tanh u) := by
  have hr := tail_tanh_mem hu
  have hr2 : Real.tanh u^2 ≤ 1 := by nlinarith only [hr.1,hr.2]
  have hr2c : 0 ≤ 1-Real.tanh u^2 := sub_nonneg.mpr hr2
  have hε := tail_epsilon_bounds hu
  have hε2 : Real.exp (-u)^2 ≤ (1/2500 : ℝ)^2 := pow_le_pow_left₀ hε.1.le hε.2.le 2
  have hlog : Real.log 2 ≤ 1 := by linarith [Certificate.log_two_coarse_bounds.2]
  have hbracket : 1/2-4*Real.exp (-u)^2 ≤ 1/2-(1-Real.tanh u^2)*Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hlog hr2c
    nlinarith only [h,tanh_square_tail_bound u]
  have hbracket0 : 0 ≤ 1/2-(1-Real.tanh u^2)*Real.log 2 := by linarith only [hbracket,hε2]
  have hγ : 0 < tailGamma u := by unfold tailGamma; positivity
  have hC : 1 ≤ Certificate.arcsineSharpConstant := by linarith [Certificate.arcsineSharpConstant_bounds.1]
  have hc := mul_le_mul_of_nonneg_right hC hbracket0
  have hcγ := mul_le_mul_of_nonneg_left hc hγ.le
  have hbγ := mul_le_mul_of_nonneg_left hbracket hγ.le
  have ht : 0 ≤ tailT u := by unfold tailT; linarith
  have hk0 := shiftedMultiplier_nonneg hγ ht
  have hk1 := tail_shiftedMultiplier_le_gamma hu
  have hkr := mul_le_mul_of_nonneg_left hr2 hk0
  have hCpi := mul_le_mul_of_nonneg_right pi_square_quarter_bounds.2.le
    (mul_nonneg hk0 (sq_nonneg (Real.tanh u)))
  have hsmall : 0 < tailGamma u*(1/2-4*Real.exp (-u)^2-5/22) :=
    mul_pos hγ (by nlinarith only [hε2])
  unfold meanTransferCoefficient
  nlinarith only [hcγ,hbγ,hkr,hk1,hCpi,hsmall]

theorem tail_numerator_lower {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (6/5)*u+2 < spectralNumerator (tailGamma u) (tailT u) (Real.tanh u) := by
  have hk := tail_multiplier_lower hu
  have hk0 : 0 ≤ shiftedMultiplier (tailGamma u) (tailT u)*Real.tanh u^2 := by linarith only [hk,hu]
  have hmul := mul_le_mul_of_nonneg_right pi_square_quarter_bounds.1.le hk0
  have hΨ := tail_entropy_penalty_lt hu
  unfold spectralNumerator
  nlinarith only [hk,hmul,hΨ]

theorem tail_numerator_div_lower {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    6/5+2/u < spectralNumerator (tailGamma u) (tailT u) (Real.tanh u)/u := by
  have hu0 : 0 < u := by linarith
  apply (lt_div_iff₀ hu0).mpr
  have he : (6/5+2/u)*u=(6/5)*u+2 := by field_simp
  rw [he]
  exact tail_numerator_lower hu

end
end CK
