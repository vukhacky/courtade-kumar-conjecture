module

public import CK.Certificate.ClockPilotLogs

/-! Generated rational logs for STOC scalar tangent energy gates. Untrusted producer;
Lean applies the proved logarithm remainder bound and checks rational arithmetic. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CK.Certificate.EnergyLogs
noncomputable section

theorem log_low_left_bounds :
    (11874435023747253/10000000000000000 : ℝ) ≤ Real.log (200/61 : ℝ) ∧
      Real.log (200/61 : ℝ) ≤ (593721751187363/500000000000000 : ℝ) := by
  have hr : (4942963218147801/10000000000000000 : ℝ) ≤ Real.log (100/61 : ℝ) ∧
      Real.log (100/61 : ℝ) ≤ (2471481609073901/5000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 100/61)
      (lower := 4942963218147801/10000000000000000) (upper := 2471481609073901/5000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (200/61 : ℝ) =
      1 * Real.log 2 + Real.log (100/61 : ℝ) := by
    rw [show (200/61 : ℝ) = 2 ^ 1 * (100/61) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_low_right_bounds :
    (3638434334173449/10000000000000000 : ℝ) ≤ Real.log (200/139 : ℝ) ∧
      Real.log (200/139 : ℝ) ≤ (72768686683469/200000000000000 : ℝ) := by
  have hr : (3638434334173449/10000000000000000 : ℝ) ≤ Real.log (200/139 : ℝ) ∧
      Real.log (200/139 : ℝ) ≤ (72768686683469/200000000000000 : ℝ) := by
    convert logCertificate_sound (q := 200/139)
      (lower := 3638434334173449/10000000000000000) (upper := 72768686683469/200000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (200/139 : ℝ) =
      0 * Real.log 2 + Real.log (200/139 : ℝ) := by
    rw [show (200/139 : ℝ) = 2 ^ 0 * (200/139) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_central_left_bounds :
    (556691617866847/312500000000000 : ℝ) ≤ Real.log (2500/421 : ℝ) ∧
      Real.log (2500/421 : ℝ) ≤ (17814131771739117/10000000000000000 : ℝ) := by
  have hr : (19755940802701/50000000000000 : ℝ) ≤ Real.log (625/421 : ℝ) ∧
      Real.log (625/421 : ℝ) ≤ (3951188160540201/10000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 625/421)
      (lower := 19755940802701/50000000000000) (upper := 3951188160540201/10000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (2500/421 : ℝ) =
      2 * Real.log 2 + Real.log (625/421 : ℝ) := by
    rw [show (2500/421 : ℝ) = 2 ^ 2 * (625/421) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

theorem log_central_right_bounds :
    (1844037229982791/10000000000000000 : ℝ) ≤ Real.log (2500/2079 : ℝ) ∧
      Real.log (2500/2079 : ℝ) ≤ (230504653747849/1250000000000000 : ℝ) := by
  have hr : (1844037229982791/10000000000000000 : ℝ) ≤ Real.log (2500/2079 : ℝ) ∧
      Real.log (2500/2079 : ℝ) ≤ (230504653747849/1250000000000000 : ℝ) := by
    convert logCertificate_sound (q := 2500/2079)
      (lower := 1844037229982791/10000000000000000) (upper := 230504653747849/1250000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (2500/2079 : ℝ) =
      0 * Real.log 2 + Real.log (2500/2079 : ℝ) := by
    rw [show (2500/2079 : ℝ) = 2 ^ 0 * (2500/2079) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [P03.log_two_bounds.1, P03.log_two_bounds.2, hr.1, hr.2]

end
end CK.Certificate.EnergyLogs
