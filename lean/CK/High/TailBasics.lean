module

public import CK.High.SpectralCost
public import CK.High.ExponentialLocal
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! Uniform elementary estimates for the analytic tail `u ≥ 8`.
Every decay estimate is proved on the whole half-line. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def tailT (u : ℝ) : ℝ := u/2+1
def tailGamma (u : ℝ) : ℝ := Real.exp u/4
def tailAlpha (u : ℝ) : ℝ := 1-3*Real.exp (-u)

theorem pi_square_quarter_bounds :
    (12/5 : ℝ) < Real.pi^2/4 ∧ Real.pi^2/4 < 5/2 := by
  constructor <;> nlinarith only [Real.pi_gt_d2,Real.pi_lt_d2,Real.pi_pos]

theorem exp_one_gt_twentyseven_tenths : (27/10 : ℝ) < Real.exp 1 := by
  linarith only [Real.exp_one_gt_d9]

theorem exp_neg_eight_lt : Real.exp (-8 : ℝ) < 1/2500 := by
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 27/10)
    exp_one_gt_twentyseven_tenths.le 8
  have he : Real.exp (1 : ℝ)^8=Real.exp 8 := by
    rw [← Real.exp_natCast_mul]
    norm_num
  rw [he] at hpow
  have hlarge : (2500 : ℝ) < Real.exp 8 := by norm_num at hpow; linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2500) hlarge

theorem tail_epsilon_bounds {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    0 < Real.exp (-u) ∧ Real.exp (-u) < 1/2500 :=
  ⟨Real.exp_pos _,(Real.exp_le_exp.mpr (by linarith : -u ≤ -8)).trans_lt exp_neg_eight_lt⟩

theorem exp_neg_twice (u : ℝ) : Real.exp (-2*u)=Real.exp (-u)^2 := by
  rw [show -2*u=(-u)+(-u) by ring,Real.exp_add]
  ring

theorem shifted_exp_neg_antitone (c : ℝ) :
    AntitoneOn (fun u : ℝ => (u+c)*Real.exp (-u)) (Ici (1-c)) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => (u+c)*Real.exp (-u))
      ((1-(u+c))*Real.exp (-u)) u := by
    have h := ((hasDerivAt_id u).add_const c).mul ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_id u).neg)
    apply h.congr_deriv
    dsimp
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun u => (1-(u+c))*Real.exp (-u)) (convex_Ici _)
  · intro u _
    exact (hd u).continuousAt.continuousWithinAt
  · intro u _
    exact (hd u).hasDerivWithinAt
  · intro u hu
    have hu' : 1-c < u := by simpa using hu
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le

theorem shifted_square_exp_neg_antitone (c : ℝ) :
    AntitoneOn (fun u : ℝ => (u+c)^2*Real.exp (-u)) (Ici (2-c)) := by
  have hd (u : ℝ) : HasDerivAt (fun u : ℝ => (u+c)^2*Real.exp (-u))
      ((u+c)*(2-(u+c))*Real.exp (-u)) u := by
    have h := (((hasDerivAt_id u).add_const c).pow 2).mul
      ((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_id u).neg)
    apply h.congr_deriv
    dsimp
    ring
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun u => (u+c)*(2-(u+c))*Real.exp (-u)) (convex_Ici _)
  · intro u _
    exact (hd u).continuousAt.continuousWithinAt
  · intro u _
    exact (hd u).hasDerivWithinAt
  · intro u hu
    have hu' : 2-c < u := by simpa using hu
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) (Real.exp_pos _).le

theorem tail_linear_exp_le {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (2*u+1)*Real.exp (-u) ≤ 17*Real.exp (-8) := by
  have h := shifted_exp_neg_antitone (1/2) (by norm_num : (8 : ℝ) ∈ Ici (1-1/2))
    (show u ∈ Ici (1-1/2) by change (1-(1/2 : ℝ)) ≤ u; linarith) hu
  nlinarith only [h]

theorem tail_shifted_exp_le {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (u+2)*Real.exp (-u) ≤ 10*Real.exp (-8) := by
  have h := shifted_exp_neg_antitone 2 (by norm_num : (8 : ℝ) ∈ Ici (1-2))
    (show u ∈ Ici (1-2) by change (1-2 : ℝ) ≤ u; linarith) hu
  norm_num at h
  exact h

theorem tail_error_decay {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (u+2)^2*Real.exp (-u)+4*tailT u*Real.exp (-u)^2 < 1/10 := by
  have h1 := shifted_square_exp_neg_antitone 2 (by norm_num : (8 : ℝ) ∈ Ici (2-2))
    (show u ∈ Ici (2-2) by change (2-2 : ℝ) ≤ u; linarith) hu
  have h2 := shifted_exp_neg_antitone 4 (by norm_num : (16 : ℝ) ∈ Ici (1-4))
    (show 2*u ∈ Ici (1-4) by change (1-4 : ℝ) ≤ 2*u; linarith) (by linarith : (16 : ℝ) ≤ 2*u)
  norm_num at h1 h2
  rw [show -(2*u)=-2*u by ring,exp_neg_twice] at h2
  have h16 : Real.exp (-16 : ℝ)=Real.exp (-8)^2 := by
    convert exp_neg_twice 8 using 1 <;> norm_num
  rw [h16] at h2
  have he := exp_neg_eight_lt
  have he0 := (Real.exp_pos (-8 : ℝ)).le
  have he2 : Real.exp (-8 : ℝ)^2 ≤ (1/2500 : ℝ)^2 := pow_le_pow_left₀ he0 he.le 2
  unfold tailT
  nlinarith only [h1,h2,he,he2]

theorem tail_entropy_error {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (3/7)*(2*u+1)*Real.exp (-u) < 1/300 := by
  have h := tail_linear_exp_le hu
  nlinarith only [h,exp_neg_eight_lt]

theorem tailGamma_gt_ten_t {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    10*tailT u < tailGamma u := by
  have h := tail_shifted_exp_le hu
  have he := exp_neg_eight_lt
  have hsmall : 4*(10*tailT u)*Real.exp (-u) < 1 := by
    unfold tailT
    nlinarith only [h,he]
  have hid : Real.exp u*Real.exp (-u)=1 := by rw [←Real.exp_add]; simp
  unfold tailGamma
  apply (mul_lt_mul_iff_left₀ (Real.exp_pos (-u))).mp
  nlinarith only [hsmall,hid]

theorem tail_parameter_domains {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (2 : ℝ) ≤ tailT u ∧
      max 0 (Real.exp (2*tailT u-3)/2-tailT u) < tailGamma u := by
  have ht : (2 : ℝ) ≤ tailT u := by unfold tailT; linarith
  have hg : 0 < tailGamma u := by unfold tailGamma; positivity
  have he : Real.exp (2*tailT u-3)=Real.exp u/Real.exp 1 := by
    rw [tailT,show 2*(u/2+1)-3=u-1 by ring,Real.exp_sub]
  have hexp : Real.exp (2*tailT u-3)/2 < tailGamma u := by
    rw [he,tailGamma]
    have h1 := Real.exp_one_gt_two
    have hm := mul_pos (Real.exp_pos u) (sub_pos.mpr h1)
    rw [div_div]
    apply (div_lt_div_iff₀ (mul_pos (Real.exp_pos 1) (by norm_num)) (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith only [hm]
  exact ⟨ht,max_lt hg (by linarith)⟩

end
end CK
