module

public import CK.High.TailBasics
public import CK.High.EdgeHyperbolic

/-! The strict arcsine improvement in the analytic tail. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

theorem arcsineRemainderSlope_le_one {v : ℝ} (hv : 0 < v) :
    arcsineRemainderSlope v ≤ 1 := by
  have hs : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have ha0 := arctanRatio_nonneg hs.le
  have ha1 := arctanRatio_lt_one hs
  unfold arcsineRemainderSlope
  nlinarith only [ha0,ha1]

theorem arcsineEnergy_monotone :
    MonotoneOn (fun v : ℝ => v-arcsineRemainder v) (Ici (0 : ℝ)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (f' := fun v => 1-arcsineRemainderSlope v) (convex_Ici _)
  · exact continuousOn_id.sub continuousOn_arcsineRemainder
  · intro v hv
    have hv0 : 0 < v := by simpa using hv
    exact ((hasDerivAt_id v).sub (hasDerivAt_arcsineRemainder hv0)).hasDerivWithinAt
  · intro v hv
    exact sub_nonneg.mpr (arcsineRemainderSlope_le_one (by simpa using hv))

theorem inv_cosh_eq_exp_ratio (u : ℝ) :
    1/Real.cosh u=2*Real.exp (-u)/(1+Real.exp (-u)^2) := by
  rw [Real.cosh_eq,Real.exp_neg]
  field_simp
  <;> ring

theorem arcsin_tanh_exp_identity (u : ℝ) :
    Real.arcsin (Real.tanh u)=Real.pi/2-2*Real.arctan (Real.exp (-u)) := by
  let F : ℝ → ℝ := fun v => Real.arctan (Real.sinh v)+2*Real.arctan (Real.exp (-v))
  have hd (v : ℝ) : HasDerivAt F 0 v := by
    have h := (hasDerivAt_arctan_sinh v).add
      (((Real.hasDerivAt_arctan (Real.exp (-v))).comp v
        ((Real.hasDerivAt_exp (-v)).comp v (hasDerivAt_id v).neg)).const_mul 2)
    apply h.congr_deriv
    rw [inv_cosh_eq_exp_ratio]
    ring
  have hc := is_const_of_deriv_eq_zero (fun v => (hd v).differentiableAt)
    (fun v => (hd v).deriv) u 0
  simp only [F,neg_zero,Real.sinh_zero,Real.arctan_zero,Real.exp_zero,
    Real.arctan_one,zero_add] at hc
  rw [arcsin_tanh_eq_arctan_sinh]
  linarith only [hc]

theorem arcsin_tanh_square_tail {u : ℝ} (hu : (8 : ℝ) ≤ u) :
    Real.arcsin (Real.tanh u)^2 < Real.pi^2/4-4*Real.exp (-u) := by
  let e := Real.exp (-u)
  let A := Real.arctan e
  have he := tail_epsilon_bounds hu
  change 0 < e ∧ e < 1/2500 at he
  have he0 : 0 < e := he.1
  have he2 : e^2 ≤ (1/2500 : ℝ)^2 := pow_le_pow_left₀ he.1.le he.2.le 2
  have hA0 : 0 < A := Real.arctan_pos.mpr he0
  have hAu : A ≤ e := arctan_le_self_nonneg he0.le
  have hAl := self_div_one_add_sq_lt_arctan he0
  have hAl' : e < A*(1+e^2) := (div_lt_iff₀ (show 0 < 1+e^2 by positivity)).mp hAl
  have hfac : 4*(1+e^2) < 2*Real.pi-4*A := by
    nlinarith only [hAu,he2,he.2,Real.pi_gt_three]
  have hm := mul_lt_mul_of_pos_left hfac hA0
  rw [arcsin_tanh_exp_identity]
  change (Real.pi/2-2*A)^2 < Real.pi^2/4-4*e
  nlinarith only [hm,hAl']

/-- The strict numerator improvement used in both tail majorants. -/
theorem tail_arcsine_loss {u v : ℝ} (hu : (8 : ℝ) ≤ u) (hv : 0 < v) (hvu : v ≤ u) :
    Real.tanh u*(v-arcsineRemainder v) < Real.pi^2/4-4*Real.exp (-u) := by
  have hu0 : 0 < u := hv.trans_le hvu
  have hρ : 0 < Real.tanh u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hu0) (Real.cosh_pos u)
  have h := mul_le_mul_of_nonneg_left
    (arcsineEnergy_monotone hv.le hu0.le hvu) hρ.le
  have he : Real.tanh u*(u-arcsineRemainder u)=Real.arcsin (Real.tanh u)^2 := by
    unfold arcsineRemainder
    field_simp [hρ.ne']
    ring
  rw [he] at h
  exact h.trans_lt (arcsin_tanh_square_tail hu)

end
end CK
