module

public import CK.Certificate.ClockPilotLogs

/-! Exact scalar local-entropy threshold from the STOC low-correlation
branch. All four logarithms are bounded by checked rational certificates. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

theorem local_threshold_069 : (0 : ℝ) <
    (1 - (457/500 : ℝ)^2) * Real.binEntropy ((1 - (457/500 : ℝ) * (69/100)) / 2) -
    (1 - (457/500 : ℝ)^2 * (69/100)) * Real.binEntropy ((1 - (457/500 : ℝ)) / 2) := by
  have hll := P03.log_local_left_inv_bounds.1
  have hlr := P03.log_local_right_inv_bounds.1
  have hrl := P03.log_rho_left_inv_bounds.2
  have hrr := P03.log_rho_right_inv_bounds.2
  rw [binEntropy_eq_log_inv, binEntropy_eq_log_inv]
  norm_num
  linarith

end
end CK.Certificate
