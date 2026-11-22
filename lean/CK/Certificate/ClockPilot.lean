module

public import CK.Certificate.ClockPilotLogs

/-! The first supporting-line clock certificate from the manuscript. The affine denominator has a positive lower bound throughout the integration interval. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate.P03
noncomputable section

def rho : ℝ := 457 / 500
def support : ℝ := 500041830031785 / 562949953421312
def weight : ℝ := 353357479 / 83800000
def profileQ : ℝ := 2 / 5
def endpointY : ℝ := 9702616433 / 50000000000
def signEntropy (t : ℝ) : ℝ := Real.binEntropy ((1 - t) / 2)
def supportHeight : ℝ := Real.log ((1 + support) / (1 - support)) / 2
def tangentFactor : ℝ := support ^ 2 /
  ((1 - support ^ 2) * (Real.log 2 - Real.log (1 - support ^ 2) / 2))
def affineConstant : ℝ := weight * profileQ *
  (supportHeight + tangentFactor * signEntropy support / support)
def affineSlope : ℝ := 1 - weight * tangentFactor
def affineDenominator (e : ℝ) : ℝ := affineConstant + affineSlope * e
def clockUpper : ℝ :=
  (Real.log (affineDenominator endpointY) - Real.log affineConstant) / affineSlope

theorem input_domains :
    0 < rho ∧ rho < 1 ∧ 0 < support ∧ support < 1 ∧
      0 < weight ∧ 0 < profileQ ∧ 0 < endpointY := by
  norm_num [rho, support, weight, profileQ, endpointY]

theorem tangentFactor_eq_positiveLogs :
    tangentFactor = support ^ 2 /
      ((1 - support ^ 2) * (Real.log 2 + Real.log (1 - support ^ 2)⁻¹ / 2)) := by
  simp only [tangentFactor, Real.log_inv]
  ring

theorem supportHeight_bounds :
    (141358367 / 100000000 : ℝ) ≤ supportHeight ∧
      supportHeight ≤ (141358368 / 100000000 : ℝ) := by
  have h := log_support_ratio_bounds
  norm_num [supportHeight, support] at *
  constructor <;> linarith [h.1, h.2]

theorem supportEntropy_bounds :
    (215459387 / 1000000000 : ℝ) ≤ signEntropy support ∧
      signEntropy support ≤ (215459388 / 1000000000 : ℝ) := by
  have hl := log_support_left_inv_bounds
  have hr := log_support_right_inv_bounds
  rw [signEntropy, binEntropy_eq_log_inv]
  norm_num [support] at *
  constructor <;> linarith [hl.1, hl.2, hr.1, hr.2]

theorem tangentFactor_bounds :
    (254179228 / 100000000 : ℝ) ≤ tangentFactor ∧
      tangentFactor ≤ (254179229 / 100000000 : ℝ) := by
  have h2 := log_two_bounds
  have hg := log_support_gap_inv_bounds
  have hp : 0 < (1 - support ^ 2) *
      (Real.log 2 + Real.log (1 - support ^ 2)⁻¹ / 2) := by
    norm_num [support]
    linarith [h2.1, hg.1]
  rw [tangentFactor_eq_positiveLogs]
  constructor
  · apply (le_div_iff₀ hp).2
    norm_num [support]
    linarith [h2.2, hg.2]
  · apply (div_le_iff₀ hp).2
    norm_num [support]
    linarith [h2.1, hg.1]

theorem affineConstant_bounds :
    (3424168 / 1000000 : ℝ) ≤ affineConstant ∧
      affineConstant ≤ (3424169 / 1000000 : ℝ) := by
  have hz := supportHeight_bounds
  have hk := tangentFactor_bounds
  have hh := supportEntropy_bounds
  have hk0 : 0 ≤ tangentFactor := by linarith [hk.1]
  have hh0 : 0 ≤ signEntropy support := by linarith [hh.1]
  have hlo := mul_le_mul hk.1 hh.1 (by norm_num : (0 : ℝ) ≤ 215459387 / 1000000000) hk0
  have hhi := mul_le_mul hk.2 hh.2 hh0 (by norm_num : (0 : ℝ) ≤ 254179229 / 100000000)
  norm_num [support] at hlo hhi
  norm_num [affineConstant, weight, profileQ, support] at ⊢
  constructor <;> linarith [hz.1, hz.2, hlo, hhi]

theorem affineSlope_bounds :
    (-9717916 / 1000000 : ℝ) ≤ affineSlope ∧
      affineSlope ≤ (-9717915 / 1000000 : ℝ) := by
  have hk := tangentFactor_bounds
  norm_num [affineSlope, weight]
  constructor <;> linarith [hk.1, hk.2]

theorem affineEndpoint_bounds :
    (1538383 / 1000000 : ℝ) ≤ affineDenominator endpointY ∧
      affineDenominator endpointY ≤ (1538385 / 1000000 : ℝ) := by
  have ha := affineConstant_bounds
  have hb := affineSlope_bounds
  norm_num [affineDenominator, endpointY]
  constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

theorem affineConstant_pos : 0 < affineConstant := by
  linarith [affineConstant_bounds.1]

theorem affineSlope_neg : affineSlope < 0 := by
  linarith [affineSlope_bounds.2]

theorem affineEndpoint_pos : 0 < affineDenominator endpointY := by
  linarith [affineEndpoint_bounds.1]

/-- Rational logarithm enclosures give a strict upper bound for the exact entropy ratio. -/
theorem endpointY_entropy_margin :
    signEntropy rho / rho + (9 / 1000000000000 : ℝ) < endpointY := by
  have hl := log_rho_left_inv_bounds.2
  have hr := log_rho_right_inv_bounds.2
  rw [signEntropy, binEntropy_eq_log_inv]
  norm_num [rho, endpointY]
  linarith

theorem clockUpper_lt : clockUpper < (33 / 400 : ℝ) := by
  have ha : Real.log affineConstant ≤ (3077147036345229 / 2500000000000000 : ℝ) :=
    (Real.log_le_log affineConstant_pos affineConstant_bounds.2).trans log_affine_upper_bounds.2
  have hd : (2153659323946793 / 5000000000000000 : ℝ) ≤
      Real.log (affineDenominator endpointY) :=
    log_endpoint_lower_bounds.1.trans
      (Real.log_le_log (by norm_num) affineEndpoint_bounds.1)
  rw [clockUpper, div_lt_iff_of_neg affineSlope_neg]
  linarith [affineSlope_bounds.2]

theorem clock_margin : clockUpper + (7 / 1000 : ℝ) < Real.log (1 / rho) := by
  have hr := log_rho_inv_bounds.1
  norm_num [rho]
  linarith [clockUpper_lt]

end
end CK.Certificate.P03
