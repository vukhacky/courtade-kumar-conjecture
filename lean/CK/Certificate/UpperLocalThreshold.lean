module

public import CK.Certificate.AndRationalLogs

/-! Exact scalar gate M_(49/50)(76043/100000)>0 used next to the
P01 moment polygon in the upper-middle band. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

theorem local_threshold_upper_middle : (0 : ℝ) <
    (1-(49/50 : ℝ)^2)*Real.binEntropy ((1-(49/50 : ℝ)*(76043/100000))/2) -
    (1-(49/50 : ℝ)^2*(76043/100000))*Real.binEntropy ((1-(49/50 : ℝ))/2) := by
  have hll := AndLogs.log_upper_local_left_inv_bounds.1
  have hlr := AndLogs.log_upper_local_right_inv_bounds.1
  have hrl := AndLogs.log_hundred_bounds.2
  have hrr := AndLogs.log_hundred_ratio_bounds.2
  rw [binEntropy_eq_log_inv, binEntropy_eq_log_inv]
  norm_num
  linarith

end
end CK.Certificate
