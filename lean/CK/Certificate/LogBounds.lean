module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Tactic

/-! Exact finite certificates for logarithms. Rational certificate producers
are untrusted: `logCertificate_sound` is the semantic consumer. The analytic
remainder is the proved atanh-series estimate in mathlib, not a numerical
oracle. All logarithms used in the consumer have positive arguments. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace CK.Certificate
noncomputable section

def logSeries (q : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range n, ((q - 1) / (q + 1)) ^ (2 * i + 1) / (2 * i + 1)

def logRemainder (q : ℚ) (n : ℕ) : ℚ :=
  2 * ((q - 1) / (q + 1)) ^ (2 * n + 1) / (1 - ((q - 1) / (q + 1)) ^ 2)

/-- A finite, exact rational check; no evaluation of a real logarithm. -/
def logCertificate (q lower upper : ℚ) (n : ℕ) : Prop :=
  1 ≤ q ∧ lower ≤ logSeries q n ∧ logSeries q n + logRemainder q n ≤ upper

def checkLogCertificate (q lower upper : ℚ) (n : ℕ) : Bool :=
  decide (1 ≤ q ∧ lower ≤ logSeries q n ∧ logSeries q n + logRemainder q n ≤ upper)

theorem logSeries_cast (q : ℚ) (n : ℕ) :
    (logSeries q n : ℝ) =
      2 * ∑ i ∈ Finset.range n,
        (((q : ℝ) - 1) / ((q : ℝ) + 1)) ^ (2 * i + 1) / (2 * i + 1) := by
  simp [logSeries]

theorem logRemainder_cast (q : ℚ) (n : ℕ) :
    (logRemainder q n : ℝ) =
      2 * (((q : ℝ) - 1) / ((q : ℝ) + 1)) ^ (2 * n + 1) /
        (1 - (((q : ℝ) - 1) / ((q : ℝ) + 1)) ^ 2) := by
  simp [logRemainder]

/-- Soundness for every rational input accepted by `logCertificate`. -/
theorem logCertificate_sound {q lower upper : ℚ} {n : ℕ}
    (h : logCertificate q lower upper n) :
    (lower : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (upper : ℝ) := by
  rcases h with ⟨hq, hlo, hhi⟩
  have hq' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqp : 0 < (q : ℝ) + 1 := by linarith
  have hz0 : 0 ≤ ((q : ℝ) - 1) / ((q : ℝ) + 1) :=
    div_nonneg (by linarith) hqp.le
  have hz1 : ((q : ℝ) - 1) / ((q : ℝ) + 1) < 1 := by
    apply (div_lt_iff₀ hqp).2
    linarith
  have hid : (1 + ((q : ℝ) - 1) / ((q : ℝ) + 1)) /
      (1 - ((q : ℝ) - 1) / ((q : ℝ) + 1)) = (q : ℝ) := by
    field_simp
    ring
  have hl := Real.sum_range_le_log_div hz0 hz1 n
  have hu := Real.log_div_le_sum_range_add hz0 hz1 n
  rw [hid] at hl hu
  have hlo' : (lower : ℝ) ≤ (logSeries q n : ℝ) := by exact_mod_cast hlo
  have hhi' : (logSeries q n : ℝ) + (logRemainder q n : ℝ) ≤ (upper : ℝ) := by
    exact_mod_cast hhi
  rw [logSeries_cast] at hlo' hhi'
  rw [logRemainder_cast] at hhi'
  rw [mul_div_assoc] at hhi'
  constructor <;> linarith

theorem checkLogCertificate_sound {q lower upper : ℚ} {n : ℕ}
    (h : checkLogCertificate q lower upper n = true) :
    (lower : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (upper : ℝ) := by
  apply logCertificate_sound
  unfold logCertificate
  exact of_decide_eq_true h

theorem binEntropy_eq_log_inv (p : ℝ) :
    Real.binEntropy p = p * Real.log p⁻¹ + (1 - p) * Real.log (1 - p)⁻¹ := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Real.negMulLog_def, Real.log_inv]
  ring

theorem log_two_coarse_bounds :
    (693 / 1000 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ (347 / 500 : ℝ) := by
  convert logCertificate_sound (q := 2) (lower := 693/1000) (upper := 347/500) (n := 4)
    (by norm_num [logCertificate, logSeries, logRemainder, Finset.sum_range_succ]) using 1 <;>
    norm_num

/-- The exact scalar cutoff required by the STOC large-mean branch.
This is an entropy bound, not an assumed contraction theorem. -/
theorem largeMean_entropy_bound : Real.binEntropy (39 / 200 : ℝ) ≤ 1 / 2 := by
  have h50 : Real.log (50 / 39 : ℝ) ≤ 249 / 1000 := by
    have h := (logCertificate_sound (q := 50/39) (lower := 0) (upper := 249/1000)
      (n := 4) (by norm_num [logCertificate, logSeries, logRemainder,
        Finset.sum_range_succ])).2
    norm_num at h ⊢
    exact h
  have h200 : Real.log (200 / 161 : ℝ) ≤ 109 / 500 := by
    have h := (logCertificate_sound (q := 200/161) (lower := 0) (upper := 109/500)
      (n := 4) (by norm_num [logCertificate, logSeries, logRemainder,
        Finset.sum_range_succ])).2
    norm_num at h ⊢
    exact h
  have hrewrite : Real.log (200 / 39 : ℝ) = 2 * Real.log 2 + Real.log (50 / 39 : ℝ) := by
    rw [show (200 / 39 : ℝ) = 2 ^ 2 * (50 / 39) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [binEntropy_eq_log_inv]
  norm_num
  rw [hrewrite]
  linarith [log_two_coarse_bounds.2]

theorem largeMean_entropy_bound_mean_form :
    Real.binEntropy ((1 - (61 / 100 : ℝ)) / 2) ≤ 1 / 2 := by
  convert largeMean_entropy_bound using 1
  norm_num

end
end CK.Certificate
