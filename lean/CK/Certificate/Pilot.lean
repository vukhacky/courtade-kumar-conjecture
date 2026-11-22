module

public import Mathlib.Tactic

/-! Exact arithmetic for eight endpoints of the moment polynomial from manuscript equation `eq:local-moment-polynomial`. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

/-- The explicit local moment polynomial, with `rho` itself as argument. -/
def localMomentQ (ρ a b : ℝ) : ℝ :=
  (17/12 : ℝ) * (ρ^2 * (a+b)-1) - ρ^2*b/5 + 9/13 -
    (ρ^2*(a^2+b^2)+ρ^4*b^2)/2 -
    (ρ^4*(a^4+b^4+6*a^2*b^2)+6*ρ^6*b^2*(a^2+b^2)+ρ^8*b^4)/5 - 1/198

/-- Eight real-number endpoint evaluations by kernel arithmetic. -/
theorem localMoment_eight_endpoints :
    (1/1000 : ℝ) < localMomentQ (39/40) (2/3) (2/25) ∧
    (1/1000 : ℝ) < localMomentQ (49/50) (2/3) (2/25) ∧
    (1/1000 : ℝ) < localMomentQ (39/40) (2/3) (1/3) ∧
    (1/1000 : ℝ) < localMomentQ (49/50) (2/3) (1/3) ∧
    (1/1000 : ℝ) < localMomentQ (39/40) (76043/100000) (23957/100000) ∧
    (1/1000 : ℝ) < localMomentQ (49/50) (76043/100000) (23957/100000) ∧
    (1/1000 : ℝ) < localMomentQ (39/40) (76043/100000) (27871/700000) ∧
    (1/1000 : ℝ) < localMomentQ (49/50) (76043/100000) (27871/700000) := by
  norm_num [localMomentQ]

/-- Exact scalar used after the central-energy Taylor estimate. -/
theorem centralEnergy_scalar_identity :
    (-649553/336000000 : ℝ) + (3532483/42000000 : ℝ)^2/5 =
      (-4572330104711/8820000000000000 : ℝ) := by norm_num

theorem centralEnergy_scalar_negative :
    (-649553/336000000 : ℝ) + (3532483/42000000 : ℝ)^2/5 < 0 := by
  rw [centralEnergy_scalar_identity]
  norm_num

end
end CK.Certificate
