module

public import CK.High.TailInverse
public import CK.High.TailLosses

/-! The discarded-coordinate scalar gate on the entire infinite tail. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def tailBetaUpper (u : ℝ) : ℝ := (1001/8000)*(2*u+1)*Real.exp (7-2*u)

theorem tail_heightF_upper {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    heightF u ≤ (1001/1000)*(2*u+1)*Real.exp (-2*u) := by
  have hu0 : 0 < u := by linarith
  have he := tail_epsilon_bounds hu
  have hq : heightExpParameter u < (1/2500 : ℝ)^2 := by
    unfold heightExpParameter
    rw [exp_neg_twice]
    nlinarith only [he.1,he.2]
  have hqd := heightExpParameter_bounds hu0
  have hratio : (1+heightExpParameter u)/(1-heightExpParameter u) ≤ (1001/1000 : ℝ) := by
    apply (div_le_iff₀ (by linarith [hqd.2] : 0 < 1-heightExpParameter u)).mpr
    linarith only [hq]
  have hb := (scaledHeightF_bounds hu0).2.trans
    (mul_le_mul_of_nonneg_right hratio (by linarith : 0 ≤ 2*u+1))
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos (-2*u)).le
  have hid : Real.exp (2*u)*Real.exp (-2*u)=1 := by rw [←Real.exp_add]; ring_nf; simp
  unfold scaledHeightF at hm
  nlinarith only [hm, congrArg (fun x : ℝ => heightF u*x) hid]

theorem heightF_seven_halves_lower :
    8*Real.exp (-7 : ℝ) ≤ heightF (7/2) := by
  have h := (scaledHeightF_bounds (by norm_num : (0 : ℝ) < 7/2)).1
  norm_num [scaledHeightF] at h
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-7 : ℝ)).le
  have hid : Real.exp (7 : ℝ)*Real.exp (-7)=1 := by rw [←Real.exp_add]; norm_num
  nlinarith only [hm, congrArg (fun x : ℝ => heightF (7/2)*x) hid]

theorem tail_beta_upper {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    profileCoefficient (Real.tanh u) (7/2) ≤ tailBetaUpper u := by
  have hr := tail_tanh_mem hu
  have hv := tanh_mem_Ioo_positive (by norm_num : (0 : ℝ) < 7/2)
  have hroot : profileCoefficient (Real.tanh u) (7/2)*heightF (7/2)=heightF u := by
    unfold profileCoefficient heightF
    change (signEntropy (Real.tanh u)*Real.tanh (7/2)/
      (Real.tanh u*signEntropy (Real.tanh (7/2))))*
      (signEntropy (Real.tanh (7/2))/Real.tanh (7/2))=
      signEntropy (Real.tanh u)/Real.tanh u
    have hH : 0 < signEntropy (Real.tanh (7/2)) :=
      Profile.meanEntropy_pos ⟨by linarith [hv.1],hv.2⟩
    field_simp [hr.1.ne',hv.1.ne',hH.ne']
  have hb := profileCoefficient_pos hr (by norm_num : (0 : ℝ) < 7/2)
  have hmul := mul_le_mul_of_nonneg_left heightF_seven_halves_lower hb.le
  have hh := tail_heightF_upper hu
  have hid : tailBetaUpper u*(8*Real.exp (-7))=
      (1001/1000)*(2*u+1)*Real.exp (-2*u) := by
    unfold tailBetaUpper
    have he : Real.exp (7-2*u)*Real.exp (-7)=Real.exp (-2*u) := by
      rw [←Real.exp_add]
      congr 1
      ring
    nlinarith only [congrArg (fun x : ℝ => (1001/1000)*(2*u+1)*x) he]
  apply (mul_le_mul_iff_left₀ (show 0 < 8*Real.exp (-7 : ℝ) by positivity)).mp
  rw [hid]
  nlinarith only [hmul,hroot,hh]

theorem tail_beta_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    profileCoefficient (Real.tanh u) (7/2) < 1/200 := by
  have he : Real.exp (7-2*u) ≤ Real.exp (-u) := Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left he (show 0 ≤ (1001/8000)*(2*u+1) by positivity)
  have hl := tail_linear_exp_le hu
  have hb := tail_beta_upper hu
  unfold tailBetaUpper at hb
  nlinarith only [hb,hmul,hl,exp_neg_eight_lt]

theorem tail_quadratic_exp_decay {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    u*(2*u+1)*Real.exp (7-u) ≤ 136*Real.exp (-1) := by
  have hd (s : ℝ) : HasDerivAt (fun s => s*(2*s+1)*Real.exp (7-s))
      ((-2*s^2+3*s+1)*Real.exp (7-s)) s := by
    have h := ((hasDerivAt_id s).mul (((hasDerivAt_id s).const_mul 2).add_const 1)).mul
      (((hasDerivAt_id s).const_sub 7).exp)
    apply h.congr_deriv
    dsimp
    ring
  have hanti : AntitoneOn (fun s => s*(2*s+1)*Real.exp (7-s)) (Ici (8 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun s => (-2*s^2+3*s+1)*Real.exp (7-s)) (convex_Ici _)
    · intro s _
      exact (hd s).continuousAt.continuousWithinAt
    · intro s _
      exact (hd s).hasDerivWithinAt
    · intro s hs
      have hs' : (8 : ℝ) < s := by simpa using hs
      exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith only [hs',sq_nonneg (s-8)]) (Real.exp_pos _).le
  have h := hanti (by simp : (8 : ℝ) ∈ Ici 8) hu hu
  norm_num at h
  exact h

theorem tail_tau_upper {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    spectralTau (tailGamma u) (tailT u) (Real.tanh u) (7/2) <
      (1001/1000)*(2*u+1)*Real.exp (7-u)/(56*(Real.exp 1-2)) := by
  have hb := tail_beta_upper hu
  have hb0 := profileCoefficient_pos (tail_tanh_mem hu) (by norm_num : (0 : ℝ) < 7/2)
  have hd := tail_outside_multiplier_lt hu
  have hupp0 : 0 < Real.exp u/(2*(Real.exp 1-2)) := by
    exact div_pos (Real.exp_pos _) (mul_pos (by norm_num) (sub_pos.mpr Real.exp_one_gt_two))
  have hm := mul_lt_mul_of_pos_right hd hb0
  have hm2 := mul_le_mul_of_nonneg_left hb hupp0.le
  have hi : (Real.exp u/(2*(Real.exp 1-2)))*tailBetaUpper u/(7/2)=
      (1001/1000)*(2*u+1)*Real.exp (7-u)/(56*(Real.exp 1-2)) := by
    have he : Real.exp u*Real.exp (7-2*u)=Real.exp (7-u) := by
      rw [←Real.exp_add]
      congr 1
      ring
    unfold tailBetaUpper
    field_simp [(sub_pos.mpr Real.exp_one_gt_two).ne']
    nlinarith only [he]
  rw [←hi]
  unfold spectralTau
  exact div_lt_div_of_pos_right (hm.trans_le hm2) (by norm_num)

theorem tail_u_tau_lt {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    u*spectralTau (tailGamma u) (tailT u) (Real.tanh u) (7/2) < 13/10 := by
  have hu0 : 0 < u := by linarith
  have ht := mul_lt_mul_of_pos_left (tail_tau_upper hu) hu0
  have hdec := tail_quadratic_exp_decay hu
  have hden : 0 < 56*(Real.exp 1-2) := by linarith [Real.exp_one_gt_two]
  have hdec' := mul_le_mul_of_nonneg_left hdec (show 0 ≤ (1001/1000)/(56*(Real.exp 1-2)) by positivity)
  have he : Real.exp (-1 : ℝ) < 10/27 := by
    rw [Real.exp_neg]
    have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 27/10) exp_one_gt_twentyseven_tenths
    convert h using 1 <;> norm_num
  have hnum : (1001/1000)*136*Real.exp (-1)/(56*(Real.exp 1-2)) < 13/10 := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [he,exp_one_gt_twentyseven_tenths]
  have hmul : u*((1001/1000)*(2*u+1)*Real.exp (7-u)/(56*(Real.exp 1-2))) ≤
      (1001/1000)*136*Real.exp (-1)/(56*(Real.exp 1-2)) := by
    convert hdec' using 1 <;> ring
  exact ht.trans_le hmul |>.trans hnum

theorem tail_discarded_gate {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    u*(Real.tanh u+(Real.pi^2/4)*spectralTau (tailGamma u) (tailT u) (Real.tanh u) (7/2)) <
      spectralNumerator (tailGamma u) (tailT u) (Real.tanh u) := by
  have hu0 : 0 ≤ u := by linarith
  have hτ := spectralTau_nonneg (tail_parameter_domains hu).2 (tail_tanh_mem hu)
    (by norm_num : (0 : ℝ) < 7/2)
  have hπ := mul_le_mul_of_nonneg_right pi_square_quarter_bounds.2.le
    (mul_nonneg hu0 hτ)
  have hr := mul_le_mul_of_nonneg_left (Real.tanh_lt_one u).le hu0
  have htail := tail_u_tau_lt hu
  have hN := tail_numerator_lower hu
  nlinarith only [hπ,hr,htail,hN,hu]

end
end CK
