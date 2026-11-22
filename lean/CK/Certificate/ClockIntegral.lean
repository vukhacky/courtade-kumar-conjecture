module

public import CK.Certificate.ClockPilot
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Exact affine integration for the supporting-line certificate. Positivity
is proved on the whole interval and integrability precedes use of the integral.
The profile-to-affine comparison is a separate analytic statement. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped Interval
namespace CK.Certificate
noncomputable section

theorem affine_pos_of_endpoints {a b A B : ℝ} (_hab : a ≤ b)
    (ha : 0 < A + B * a) (hb : 0 < A + B * b) :
    ∀ x ∈ Set.Icc a b, 0 < A + B * x := by
  intro x hx
  by_cases hB : 0 ≤ B
  · have h := mul_le_mul_of_nonneg_left hx.1 hB
    linarith
  · have h := mul_le_mul_of_nonpos_left hx.2 (le_of_lt (lt_of_not_ge hB))
    linarith

theorem intervalIntegrable_affine_reciprocal {a b A B : ℝ} (hab : a ≤ b)
    (ha : 0 < A + B * a) (hb : 0 < A + B * b) :
    IntervalIntegrable (fun x => 1 / (A + B * x)) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply continuousOn_const.div
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  intro x hx
  exact (affine_pos_of_endpoints hab ha hb x hx).ne'

theorem integral_affine_reciprocal {a b A B : ℝ}
    (ha : 0 < A + B * a) (hb : 0 < A + B * b) (hB : B ≠ 0) :
    (∫ x in a..b, 1 / (A + B * x)) =
      (Real.log (A + B * b) - Real.log (A + B * a)) / B := by
  calc
    (∫ x in a..b, 1 / (A + B * x)) =
        B⁻¹ * ∫ y in (A + B * a)..(A + B * b), 1 / y := by
      simpa using intervalIntegral.integral_comp_add_mul (fun y : ℝ => 1 / y) hB A
    _ = B⁻¹ * Real.log ((A + B * b) / (A + B * a)) := by
      rw [integral_one_div_of_pos ha hb]
    _ = (Real.log (A + B * b) - Real.log (A + B * a)) / B := by
      rw [Real.log_div hb.ne' ha.ne']
      ring

theorem integral_affine_reciprocal_zero_slope {a b A : ℝ} :
    (∫ _x in a..b, 1 / A) = (b - a) / A := by
  simp [div_eq_mul_inv]

/-- A denominator may be defined arbitrarily at zero. Continuity and a
positive affine lower bound on `(0,Y]` suffice for integrability, and the
integral comparison does not use the totalized value of `1 / 0`. -/
theorem reciprocal_integral_le_affine {Y A B : ℝ} (hY : 0 < Y)
    (ha : 0 < A) (hb : 0 < A + B * Y) (d : ℝ → ℝ)
    (hd : ContinuousOn d (Set.Ioc 0 Y))
    (hbound : ∀ e ∈ Set.Ioc 0 Y, A + B * e ≤ d e) :
    IntervalIntegrable (fun e => 1 / d e) volume 0 Y ∧
      (∫ e in (0 : ℝ)..Y, 1 / d e) ≤ ∫ e in (0 : ℝ)..Y, 1 / (A + B * e) := by
  have hapos : ∀ e ∈ Set.Icc 0 Y, 0 < A + B * e :=
    affine_pos_of_endpoints hY.le (by simpa using ha) hb
  have hdpos : ∀ e ∈ Set.Ioc 0 Y, 0 < d e := by
    intro e he
    exact (hapos e ⟨he.1.le, he.2⟩).trans_le (hbound e he)
  have hi : IntervalIntegrable (fun e => 1 / (A + B * e)) volume 0 Y :=
    intervalIntegrable_affine_reciprocal hY.le (by simpa using ha) hb
  have hmeas : AEStronglyMeasurable (fun e => 1 / d e) (volume.restrict (Ι (0 : ℝ) Y)) := by
    rw [Set.uIoc_of_le hY.le]
    exact (continuousOn_const.div hd (fun e he => (hdpos e he).ne')).aestronglyMeasurable
      measurableSet_Ioc
  have hirecip : IntervalIntegrable (fun e => 1 / d e) volume 0 Y := by
    apply hi.mono_fun' hmeas
    rw [Set.uIoc_of_le hY.le]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with e he
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hdpos e he))]
    exact one_div_le_one_div_of_le (hapos e ⟨he.1.le, he.2⟩) (hbound e he)
  refine ⟨hirecip, ?_⟩
  apply intervalIntegral.integral_mono_on_of_le_Ioo hY.le hirecip hi
  intro e he
  exact one_div_le_one_div_of_le (hapos e ⟨he.1.le, he.2.le⟩)
    (hbound e ⟨he.1, he.2.le⟩)

/-- The finite integral is also the proper right-hand improper-integral
limit. No limiting value of the integrand at zero is required. -/
theorem tendsto_integral_from_right {Y : ℝ} (hY : 0 < Y) {f : ℝ → ℝ}
    (hi : IntervalIntegrable f volume 0 Y) :
    Filter.Tendsto (fun ε => ∫ e in ε..Y, f e)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ e in (0 : ℝ)..Y, f e)) := by
  have hcont : ContinuousOn (fun ε => ∫ e in ε..Y, f e) (Set.Icc 0 Y) := by
    simpa only [Set.uIcc_of_le hY.le] using
      (intervalIntegral.continuousOn_primitive_interval_left
        ((intervalIntegrable_iff' (f := f) (μ := volume) (a := (0 : ℝ)) (b := Y)).mp hi))
  have hzero := hcont 0 ⟨le_rfl, hY.le⟩
  change Filter.Tendsto (fun ε => ∫ e in ε..Y, f e)
    (nhdsWithin 0 (Set.Icc 0 Y)) (nhds (∫ e in (0 : ℝ)..Y, f e)) at hzero
  rw [nhdsWithin_Icc_eq_nhdsGE hY] at hzero
  exact hzero.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

namespace P03

theorem affineDenominator_pos_on :
    ∀ e ∈ Set.Icc 0 endpointY, 0 < affineDenominator e := by
  exact affine_pos_of_endpoints input_domains.2.2.2.2.2.2.le
    (by simpa using affineConstant_pos) affineEndpoint_pos

theorem affineReciprocal_integrable :
    IntervalIntegrable (fun e => 1 / affineDenominator e) volume 0 endpointY := by
  exact intervalIntegrable_affine_reciprocal input_domains.2.2.2.2.2.2.le
    (by simpa using affineConstant_pos) affineEndpoint_pos

theorem affineReciprocal_integral :
    (∫ e in (0 : ℝ)..endpointY, 1 / affineDenominator e) = clockUpper := by
  simpa [clockUpper, affineDenominator] using
    (integral_affine_reciprocal (a := 0) (b := endpointY)
      (A := affineConstant) (B := affineSlope)
      (by simpa using affineConstant_pos) affineEndpoint_pos affineSlope_neg.ne)

/-- Certified affine-integral inequality on the closed P03 domain. A supporting-line bound relates the affine denominator to the entropy profile. -/
theorem affineClock_certified :
    signEntropy rho / rho < endpointY ∧
    (∀ e ∈ Set.Icc 0 endpointY, 0 < affineDenominator e) ∧
    IntervalIntegrable (fun e => 1 / affineDenominator e) volume 0 endpointY ∧
    (∫ e in (0 : ℝ)..endpointY, 1 / affineDenominator e) + (7 / 1000 : ℝ) <
      Real.log (1 / rho) := by
  refine ⟨?_, affineDenominator_pos_on, affineReciprocal_integrable, ?_⟩
  · linarith [endpointY_entropy_margin]
  · rw [affineReciprocal_integral]
    exact clock_margin

/-- Integral comparison for any continuous profile satisfying the certified supporting-line bound. -/
theorem profileClock_of_tangent (P : ℝ → ℝ)
    (hcont : ContinuousOn P (Set.Ioc 0 endpointY))
    (hline : ∀ e ∈ Set.Ioc 0 endpointY,
      profileQ * supportHeight +
        (profileQ * signEntropy support / support - e) * tangentFactor ≤ P e) :
    IntervalIntegrable (fun e => 1 / (e + weight * P e)) volume 0 endpointY ∧
    (∫ e in (0 : ℝ)..endpointY, 1 / (e + weight * P e)) + (7 / 1000 : ℝ) <
      Real.log (1 / rho) := by
  have hbound : ∀ e ∈ Set.Ioc 0 endpointY,
      affineConstant + affineSlope * e ≤ e + weight * P e := by
    intro e he
    have h := mul_le_mul_of_nonneg_left (hline e he) input_domains.2.2.2.2.1.le
    have heq : affineConstant + affineSlope * e = e + weight *
        (profileQ * supportHeight + (profileQ * signEntropy support / support - e) * tangentFactor) := by
      dsimp [affineConstant, affineSlope]
      ring
    rw [heq]
    linarith only [h]
  obtain ⟨hi, hle⟩ := reciprocal_integral_le_affine input_domains.2.2.2.2.2.2
    affineConstant_pos affineEndpoint_pos (fun e => e + weight * P e)
    (continuousOn_id.add (continuousOn_const.mul hcont)) hbound
  refine ⟨hi, ?_⟩
  change (∫ e in (0 : ℝ)..endpointY, 1 / (e + weight * P e)) ≤
    (∫ e in (0 : ℝ)..endpointY, 1 / affineDenominator e) at hle
  rw [affineReciprocal_integral] at hle
  linarith [clock_margin]

end P03
end
end CK.Certificate
