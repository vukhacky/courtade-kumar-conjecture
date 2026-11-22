module

public import CK.Certificate.LogBounds

/-! Generated exact rational certificates for the first STOC supporting-line clock.
The producer is untrusted. Every real-log bound below applies the proved
`logCertificate_sound` theorem to kernel-checked rational arithmetic. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace CK.Certificate.P03
noncomputable section

theorem log_two_bounds :
    (1732867951399863/2500000000000000 : ℝ) ≤ Real.log (2 : ℝ) ∧
      Real.log (2 : ℝ) ≤ (3465735902799729/5000000000000000 : ℝ) := by
  convert logCertificate_sound (q := 2)
    (lower := 1732867951399863/2500000000000000) (upper := 3465735902799729/5000000000000000) (n := 16)
    (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
    using 1 <;> norm_num

theorem log_support_ratio_bounds :
    (1766979591046329/625000000000000 : ℝ) ≤ Real.log (1062991783453097/62908123389527 : ℝ) ∧
      Real.log (1062991783453097/62908123389527 : ℝ) ≤ (28271673456741289/10000000000000000 : ℝ) := by
  have hr : (17055819823233/312500000000000 : ℝ) ≤ Real.log (1062991783453097/1006529974232432 : ℝ) ∧
      Real.log (1062991783453097/1006529974232432 : ℝ) ≤ (545786234343457/10000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 1062991783453097/1006529974232432)
      (lower := 17055819823233/312500000000000) (upper := 545786234343457/10000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (1062991783453097/62908123389527 : ℝ) =
      4 * Real.log 2 + Real.log (1062991783453097/1006529974232432 : ℝ) := by
    rw [show (1062991783453097/62908123389527 : ℝ) = 2 ^ 4 * (1062991783453097/1006529974232432) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, hr.1, hr.2]

theorem log_support_gap_inv_bounds :
    (1944829389042311/1250000000000000 : ℝ) ≤ Real.log (316912650057057350374175801344/66870818275520791240065515119 : ℝ) ∧
      Real.log (316912650057057350374175801344/66870818275520791240065515119 : ℝ) ≤ (15558635112338501/10000000000000000 : ℝ) := by
  have hr : (13247589852653/78125000000000 : ℝ) ≤ Real.log (79228162514264337593543950336/66870818275520791240065515119 : ℝ) ∧
      Real.log (79228162514264337593543950336/66870818275520791240065515119 : ℝ) ≤ (339138300227917/2000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 79228162514264337593543950336/66870818275520791240065515119)
      (lower := 13247589852653/78125000000000) (upper := 339138300227917/2000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (316912650057057350374175801344/66870818275520791240065515119 : ℝ) =
      2 * Real.log 2 + Real.log (79228162514264337593543950336/66870818275520791240065515119 : ℝ) := by
    rw [show (316912650057057350374175801344/66870818275520791240065515119 : ℝ) = 2 ^ 2 * (79228162514264337593543950336/66870818275520791240065515119) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, hr.1, hr.2]

theorem log_support_left_inv_bounds :
    (450728532658427/156250000000000 : ℝ) ≤ Real.log (1125899906842624/62908123389527 : ℝ) ∧
      Real.log (1125899906842624/62908123389527 : ℝ) ≤ (28846626090139353/10000000000000000 : ℝ) := by
  have hr : (14009235846769/125000000000000 : ℝ) ≤ Real.log (70368744177664/62908123389527 : ℝ) ∧
      Real.log (70368744177664/62908123389527 : ℝ) ≤ (1120738867741521/10000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 70368744177664/62908123389527)
      (lower := 14009235846769/125000000000000) (upper := 1120738867741521/10000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (1125899906842624/62908123389527 : ℝ) =
      4 * Real.log 2 + Real.log (70368744177664/62908123389527 : ℝ) := by
    rw [show (1125899906842624/62908123389527 : ℝ) = 2 ^ 4 * (70368744177664/62908123389527) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, hr.1, hr.2]

theorem log_support_right_inv_bounds :
    (35934539587379/625000000000000 : ℝ) ≤ Real.log (1125899906842624/1062991783453097 : ℝ) ∧
      Real.log (1125899906842624/1062991783453097 : ℝ) ≤ (114990526679613/2000000000000000 : ℝ) := by
  convert logCertificate_sound (q := 1125899906842624/1062991783453097)
    (lower := 35934539587379/625000000000000) (upper := 114990526679613/2000000000000000) (n := 16)
    (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
    using 1 <;> norm_num

theorem log_rho_left_inv_bounds :
    (31465551632885741/10000000000000000 : ℝ) ≤ Real.log (1000/43 : ℝ) ∧
      Real.log (1000/43 : ℝ) ≤ (15732775816442883/5000000000000000 : ℝ) := by
  have hr : (3739664410487933/10000000000000000 : ℝ) ≤ Real.log (125/86 : ℝ) ∧
      Real.log (125/86 : ℝ) ≤ (1869832205243967/5000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 125/86)
      (lower := 3739664410487933/10000000000000000) (upper := 1869832205243967/5000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (1000/43 : ℝ) =
      4 * Real.log 2 + Real.log (125/86 : ℝ) := by
    rw [show (1000/43 : ℝ) = 2 ^ 4 * (125/86) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, hr.1, hr.2]

theorem log_rho_right_inv_bounds :
    (439518875291827/10000000000000000 : ℝ) ≤ Real.log (1000/957 : ℝ) ∧
      Real.log (1000/957 : ℝ) ≤ (109879718822957/2500000000000000 : ℝ) := by
  convert logCertificate_sound (q := 1000/957)
    (lower := 439518875291827/10000000000000000) (upper := 109879718822957/2500000000000000) (n := 16)
    (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
    using 1 <;> norm_num

theorem log_rho_inv_bounds :
    (89924707527987/1000000000000000 : ℝ) ≤ Real.log (500/457 : ℝ) ∧
      Real.log (500/457 : ℝ) ≤ (899247075279871/10000000000000000 : ℝ) := by
  convert logCertificate_sound (q := 500/457)
    (lower := 89924707527987/1000000000000000) (upper := 899247075279871/10000000000000000) (n := 16)
    (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
    using 1 <;> norm_num

theorem log_affine_upper_bounds :
    (12308588145380909/10000000000000000 : ℝ) ≤ Real.log (3424169/1000000 : ℝ) ∧
      Real.log (3424169/1000000 : ℝ) ≤ (3077147036345229/2500000000000000 : ℝ) := by
  have hr : (5377116339781457/10000000000000000 : ℝ) ≤ Real.log (3424169/2000000 : ℝ) ∧
      Real.log (3424169/2000000 : ℝ) ≤ (2688558169890729/5000000000000000 : ℝ) := by
    convert logCertificate_sound (q := 3424169/2000000)
      (lower := 5377116339781457/10000000000000000) (upper := 2688558169890729/5000000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (3424169/1000000 : ℝ) =
      1 * Real.log 2 + Real.log (3424169/2000000 : ℝ) := by
    rw [show (3424169/1000000 : ℝ) = 2 ^ 1 * (3424169/2000000) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, hr.1, hr.2]

theorem log_endpoint_lower_bounds :
    (2153659323946793/5000000000000000 : ℝ) ≤ Real.log (1538383/1000000 : ℝ) ∧
      Real.log (1538383/1000000 : ℝ) ≤ (4307318647893587/10000000000000000 : ℝ) := by
  convert logCertificate_sound (q := 1538383/1000000)
    (lower := 2153659323946793/5000000000000000) (upper := 4307318647893587/10000000000000000) (n := 16)
    (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
    using 1 <;> norm_num

theorem log_local_left_inv_bounds :
    (3378369661048711/2000000000000000 : ℝ) ≤ Real.log (100000/18467 : ℝ) ∧
      Real.log (100000/18467 : ℝ) ≤ (1055740519077723/625000000000000 : ℝ) := by
  have hr : (3028904694044651/10000000000000000 : ℝ) ≤ Real.log (25000/18467 : ℝ) ∧
      Real.log (25000/18467 : ℝ) ≤ (757226173511163/2500000000000000 : ℝ) := by
    convert logCertificate_sound (q := 25000/18467)
      (lower := 3028904694044651/10000000000000000) (upper := 757226173511163/2500000000000000) (n := 16)
      (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
      using 1 <;> norm_num
  have heq : Real.log (100000/18467 : ℝ) =
      2 * Real.log 2 + Real.log (25000/18467 : ℝ) := by
    rw [show (100000/18467 : ℝ) = 2 ^ 2 * (25000/18467) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [heq]
  constructor <;> linarith [log_two_bounds.1, log_two_bounds.2, hr.1, hr.2]

theorem log_local_right_inv_bounds :
    (2041623397189269/10000000000000000 : ℝ) ≤ Real.log (100000/81533 : ℝ) ∧
      Real.log (100000/81533 : ℝ) ≤ (204162339718927/1000000000000000 : ℝ) := by
  convert logCertificate_sound (q := 100000/81533)
    (lower := 2041623397189269/10000000000000000) (upper := 204162339718927/1000000000000000) (n := 16)
    (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ])
    using 1 <;> norm_num

end
end CK.Certificate.P03
