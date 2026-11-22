module

public import CK.High.Remainder

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def arctanEnergyRatio (s : ℝ) : ℝ := (1+s^2)*(Real.arctan s/s)^2

theorem hasDerivAt_arctanEnergyRatio {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt arctanEnergyRatio (2*Real.arctan s*(s-Real.arctan s)/s^3) s := by
  have h := ((hasDerivAt_pow 2 s).const_add 1).mul ((hasDerivAt_arctanRatio hs).pow 2)
  apply h.congr_deriv
  unfold arctanRatio
  norm_num
  field_simp
  ring

theorem arctanEnergyRatio_strictMono : StrictMonoOn arctanEnergyRatio (Ioi (0 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos
    (f' := fun s => 2*Real.arctan s*(s-Real.arctan s)/s^3) (convex_Ioi _)
  · intro s hs
    exact (hasDerivAt_arctanEnergyRatio (ne_of_gt hs)).continuousAt.continuousWithinAt
  · intro s hs
    have hp : 0 < s := by simpa using hs
    exact (hasDerivAt_arctanEnergyRatio hp.ne').hasDerivWithinAt
  · intro s hs
    have hp : 0 < s := by simpa using hs
    exact div_pos (mul_pos (mul_pos (by norm_num) (Real.arctan_pos.mpr hp))
      (sub_pos.mpr (arctan_lt_self_pos hp))) (pow_pos hp 3)

/-- The angle/edge-size estimate after hyperbolic parametrization. -/
theorem arctan_hyperbolic_refund (a : ℝ) {b : ℝ} (hb : 0 < b) :
    (Real.sinh b*Real.cosh b/(Real.cosh a^2+Real.sinh b^2))*arcsineRemainder b ≤
      (Real.sinh b*Real.cosh b/(Real.cosh a^2+Real.sinh b^2))*b-
        Real.arctan (Real.sinh b/Real.cosh a)^2 := by
  have hs : 0 < Real.sinh b := Real.sinh_pos_iff.mpr hb
  have hc : 0 < Real.cosh a := Real.cosh_pos a
  have hc1 : 1 ≤ Real.cosh a := Real.one_le_cosh a
  have hcb := Real.cosh_pos b
  have hD : 0 < Real.cosh a^2+Real.sinh b^2 := by positivity
  have hq : 0 < Real.sinh b/Real.cosh a := div_pos hs hc
  have hqle : Real.sinh b/Real.cosh a ≤ Real.sinh b := by
    apply (div_le_iff₀ hc).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hc1 hs.le]
  have hmono := arctanEnergyRatio_strictMono.monotoneOn hq hs hqle
  have ht : 0 < Real.tanh b := by rw [Real.tanh_eq_sinh_div_cosh]; exact div_pos hs hcb
  have hm := mul_le_mul_of_nonneg_left hmono ht.le
  have hleft : Real.tanh b*arctanEnergyRatio (Real.sinh b/Real.cosh a) =
      Real.arctan (Real.sinh b/Real.cosh a)^2/
        (Real.sinh b*Real.cosh b/(Real.cosh a^2+Real.sinh b^2)) := by
    unfold arctanEnergyRatio
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  have hright : Real.tanh b*arctanEnergyRatio (Real.sinh b) = b-arcsineRemainder b := by
    rw [arcsineRemainder_eq,Real.tanh_eq_sinh_div_cosh]
    unfold arctanEnergyRatio
    field_simp
    nlinarith only [congrArg (fun z : ℝ => z*Real.arctan (Real.sinh b)^2) (Real.cosh_sq b)]
  rw [hleft,hright] at hm
  have hd : 0 < Real.sinh b*Real.cosh b/(Real.cosh a^2+Real.sinh b^2) :=
    div_pos (mul_pos hs hcb) hD
  have h := (div_le_iff₀ hd).mp hm
  nlinarith only [h]

end
end CK
