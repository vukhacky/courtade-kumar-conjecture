module

public import CK.Certificate.ClockPilotLogs

/-! Generated rational logs for STOC lem:and-rational. Untrusted producer;
Lean applies the proved logarithm remainder bound and checks rational arithmetic. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CK.Certificate.AndLogs
noncomputable section

theorem log_hundred_bounds :
    (46051701859880907/10000000000000000 : ℝ) ≤ Real.log (100 : ℝ) ∧
      Real.log (100 : ℝ) ≤ (2878231366242559/625000000000000 : ℝ) := by
  have hr : (892574205256839/2000000000000000 : ℝ) ≤ Real.log (25/16 : ℝ) ∧
      Real.log (25/16 : ℝ) ≤ (1115717756571049/2500000000000000 : ℝ) := by
    convert logCertificate_sound (q := 25/16)
      (lower := 892574205256839/2000000000000000) (upper := 1115717756571049/2500000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (100 : ℝ) =
      6 * Real.log 2 + Real.log (25/16 : ℝ) := by
    rw [show (100 : ℝ) = 2 ^ 6 * (25/16) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_hundred_ratio_bounds :
    (50251679267507/5000000000000000 : ℝ) ≤ Real.log (100/99 : ℝ) ∧
      Real.log (100/99 : ℝ) ≤ (20100671707003/2000000000000000 : ℝ) := by
  have hr : (50251679267507/5000000000000000 : ℝ) ≤ Real.log (100/99 : ℝ) ∧
      Real.log (100/99 : ℝ) ≤ (20100671707003/2000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 100/99)
      (lower := 50251679267507/5000000000000000) (upper := 20100671707003/2000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (100/99 : ℝ) =
      0 * Real.log 2 + Real.log (100/99 : ℝ) := by
    rw [show (100/99 : ℝ) = 2 ^ 0 * (100/99) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_eighty_bounds :
    (43820266346738809/10000000000000000 : ℝ) ≤ Real.log (80 : ℝ) ∧
      Real.log (80 : ℝ) ≤ (21910133173369423/5000000000000000 : ℝ) := by
  have hr : (2231435513142097/10000000000000000 : ℝ) ≤ Real.log (5/4 : ℝ) ∧
      Real.log (5/4 : ℝ) ≤ (1115717756571049/5000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 5/4)
      (lower := 2231435513142097/10000000000000000) (upper := 1115717756571049/5000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (80 : ℝ) =
      6 * Real.log 2 + Real.log (5/4 : ℝ) := by
    rw [show (80 : ℝ) = 2 ^ 6 * (5/4) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_eighty_ratio_bounds :
    (125787822068601/10000000000000000 : ℝ) ≤ Real.log (80/79 : ℝ) ∧
      Real.log (80/79 : ℝ) ≤ (62893911034301/5000000000000000 : ℝ) := by
  have hr : (125787822068601/10000000000000000 : ℝ) ≤ Real.log (80/79 : ℝ) ∧
      Real.log (80/79 : ℝ) ≤ (62893911034301/5000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 80/79)
      (lower := 125787822068601/10000000000000000) (upper := 62893911034301/5000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (80/79 : ℝ) =
      0 * Real.log 2 + Real.log (80/79 : ℝ) := by
    rw [show (80/79 : ℝ) = 2 ^ 0 * (80/79) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_upper_local_left_inv_bounds :
    (20605075268123467/10000000000000000 : ℝ) ≤ Real.log (10000000/1273893 : ℝ) ∧
      Real.log (10000000/1273893 : ℝ) ≤ (10302537634061741/5000000000000000 : ℝ) := by
  have hr : (6742131656924563/10000000000000000 : ℝ) ≤ Real.log (2500000/1273893 : ℝ) ∧
      Real.log (2500000/1273893 : ℝ) ≤ (3371065828462283/5000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 2500000/1273893)
      (lower := 6742131656924563/10000000000000000) (upper := 3371065828462283/5000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (10000000/1273893 : ℝ) =
      2 * Real.log 2 + Real.log (2500000/1273893 : ℝ) := by
    rw [show (10000000/1273893 : ℝ) = 2 ^ 2 * (2500000/1273893) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_upper_local_right_inv_bounds :
    (1362657561629031/10000000000000000 : ℝ) ≤ Real.log (10000000/8726107 : ℝ) ∧
      Real.log (10000000/8726107 : ℝ) ≤ (170332195203629/1250000000000000 : ℝ) := by
  have hr : (1362657561629031/10000000000000000 : ℝ) ≤ Real.log (10000000/8726107 : ℝ) ∧
      Real.log (10000000/8726107 : ℝ) ≤ (170332195203629/1250000000000000 : ℝ) := by
    convert logCertificate_sound (q := 10000000/8726107)
      (lower := 1362657561629031/10000000000000000) (upper := 170332195203629/1250000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (10000000/8726107 : ℝ) =
      0 * Real.log 2 + Real.log (10000000/8726107 : ℝ) := by
    rw [show (10000000/8726107 : ℝ) = 2 ^ 0 * (10000000/8726107) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

end
end CK.Certificate.AndLogs
