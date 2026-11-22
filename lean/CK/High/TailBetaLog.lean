module

public import CK.High.TailDiscarded

/-! The logarithmic discarded-height estimate, uniformly in `u ≥ 8`. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem exp_half_lt_seven_fourths : Real.exp (1/2 : ℝ) < 7/4 := by
  have he : Real.exp (1/2 : ℝ)^2=Real.exp 1 := by
    rw [pow_two,←Real.exp_add]
    norm_num
  nlinarith only [he,Real.exp_one_lt_three,Real.exp_pos (1/2 : ℝ)]

theorem tail_beta_log_decay {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (2*u+1)*Real.exp ((9-u)/2) ≤ 17*Real.exp (1/2) := by
  have hd (s : ℝ) : HasDerivAt (fun s => (2*s+1)*Real.exp ((9-s)/2))
      ((3/2-s)*Real.exp ((9-s)/2)) s := by
    have h := (((hasDerivAt_id s).const_mul 2).add_const 1).mul
      ((((hasDerivAt_id s).const_sub 9).div_const 2).exp)
    apply h.congr_deriv
    dsimp
    ring
  have hanti : AntitoneOn (fun s => (2*s+1)*Real.exp ((9-s)/2)) (Ici (8 : ℝ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun s => (3/2-s)*Real.exp ((9-s)/2)) (convex_Ici _)
    · intro s _
      exact (hd s).continuousAt.continuousWithinAt
    · intro s _
      exact (hd s).hasDerivWithinAt
    · intro s hs
      have hs' : (8 : ℝ) < s := by simpa using hs
      exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.exp_pos _).le
  have h := hanti (by simp : (8 : ℝ) ∈ Ici 8) hu hu
  norm_num at h
  exact h

theorem tail_beta_log_lower {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    (3*u-5)/2 < Real.log (4/profileCoefficient (Real.tanh u) (7/2)) := by
  have hb := tail_beta_upper hu
  have hb0 := profileCoefficient_pos (tail_tanh_mem hu) (by norm_num : (0 : ℝ) < 7/2)
  have hm := mul_le_mul_of_nonneg_right hb (Real.exp_pos ((3*u-5)/2)).le
  have he : tailBetaUpper u*Real.exp ((3*u-5)/2)=
      (1001/8000)*(2*u+1)*Real.exp ((9-u)/2) := by
    unfold tailBetaUpper
    have hid : Real.exp (7-2*u)*Real.exp ((3*u-5)/2)=Real.exp ((9-u)/2) := by
      rw [←Real.exp_add]
      congr 1
      ring
    nlinarith only [congrArg (fun x : ℝ => (1001/8000)*(2*u+1)*x) hid]
  rw [he] at hm
  have hs : profileCoefficient (Real.tanh u) (7/2)*Real.exp ((3*u-5)/2) < 4 := by
    nlinarith only [hm,tail_beta_log_decay hu,exp_half_lt_seven_fourths]
  have hs' : Real.exp ((3*u-5)/2) < 4/profileCoefficient (Real.tanh u) (7/2) :=
    (lt_div_iff₀ hb0).mpr (by nlinarith only [hs])
  have hlog := Real.log_lt_log (Real.exp_pos _) hs'
  rwa [Real.log_exp] at hlog

end
end CK
