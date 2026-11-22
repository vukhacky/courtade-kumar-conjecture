module

public import CK.High.Remainder

/-! Exact hyperbolic edge coordinates. The angle identity is proved by
equal derivatives and its value at zero; there are no inverse-angle
branch assumptions or numerical approximations. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem cosh_edge_product (a b : ℝ) :
    Real.cosh (a+b)*Real.cosh (a-b)=Real.cosh a^2+Real.sinh b^2 := by
  rw [Real.cosh_add,Real.cosh_sub]
  nlinarith only [Real.cosh_sq a,Real.cosh_sq b,
    mul_self_nonneg (Real.sinh a*Real.sinh b)]

theorem tanh_edge_half_difference (a b : ℝ) :
    (Real.tanh (a+b)-Real.tanh (a-b))/2 =
      Real.sinh b*Real.cosh b/(Real.cosh a^2+Real.sinh b^2) := by
  have hp := Real.cosh_pos (a+b)
  have hm := Real.cosh_pos (a-b)
  have hD : 0 < Real.cosh a^2+Real.sinh b^2 := by positivity
  rw [←cosh_edge_product,Real.tanh_eq_sinh_div_cosh,Real.tanh_eq_sinh_div_cosh]
  field_simp
  rw [Real.sinh_add,Real.sinh_sub,Real.cosh_add,Real.cosh_sub]
  nlinarith only [congrArg (fun z : ℝ => z*(Real.sinh b*Real.cosh b)) (Real.cosh_sq a)]

theorem hasDerivAt_arctan_sinh (v : ℝ) :
    HasDerivAt (fun x => Real.arctan (Real.sinh x)) (1/Real.cosh v) v := by
  apply ((Real.hasDerivAt_arctan (Real.sinh v)).comp v (Real.hasDerivAt_sinh v)).congr_deriv
  rw [←Real.cosh_sq']
  field_simp

theorem arcsin_tanh_edge_half_difference (a b : ℝ) :
    (Real.arcsin (Real.tanh (a+b))-Real.arcsin (Real.tanh (a-b)))/2 =
      Real.arctan (Real.sinh b/Real.cosh a) := by
  let F : ℝ → ℝ := fun t =>
    (Real.arctan (Real.sinh (a+t))-Real.arctan (Real.sinh (a-t)))/2
  let G : ℝ → ℝ := fun t => Real.arctan (Real.sinh t/Real.cosh a)
  let D : ℝ → ℝ := fun t => Real.cosh a*Real.cosh t/(Real.cosh a^2+Real.sinh t^2)
  have hF (t : ℝ) : HasDerivAt F (D t) t := by
    have h := (((hasDerivAt_arctan_sinh (a+t)).comp t ((hasDerivAt_id t).const_add a)).sub
      ((hasDerivAt_arctan_sinh (a-t)).comp t ((hasDerivAt_id t).const_sub a))).div_const 2
    apply h.congr_deriv
    dsimp [D]
    rw [←cosh_edge_product]
    field_simp
    rw [Real.cosh_add,Real.cosh_sub]
    ring
  have hG (t : ℝ) : HasDerivAt G (D t) t := by
    have h := (Real.hasDerivAt_arctan (Real.sinh t/Real.cosh a)).comp t
      ((Real.hasDerivAt_sinh t).div_const (Real.cosh a))
    apply h.congr_deriv
    dsimp [D]
    field_simp
  have hsub (t : ℝ) : HasDerivAt (fun t => F t-G t) 0 t := by
    convert (hF t).sub (hG t) using 1 <;> simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hsub t).differentiableAt)
    (fun t => (hsub t).deriv) b 0
  simp only [F,G,add_zero,sub_zero,sub_self,zero_div,Real.sinh_zero,Real.arctan_zero,
    sub_zero] at hc
  rw [arcsin_tanh_eq_arctan_sinh,arcsin_tanh_eq_arctan_sinh]
  linarith only [hc]

end
end CK
