module

public import CK.Certificate.ClockIntegral
public import CK.Certificate.RationalInterval
public import CK.Profile.Weighted

/-! Analytic consumer for finitely many rational supporting-line panels.
Every panel controls the entire interval. The denominator may be arbitrary
at its left endpoint; all integral uses are preceded by integrability. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators Interval
namespace CK.Certificate
noncomputable section

theorem tangentFactor_positiveLogs (t : ℝ) :
    CK.Profile.tangentFactor t = t^2 / ((1-t^2) *
      (Real.log 2 + Real.log ((1-t^2)⁻¹)/2)) := by
  unfold CK.Profile.tangentFactor CK.Profile.profileAux
  rw [Real.log_inv]
  ring

theorem reciprocal_integral_le_affine_panel {a b A B : ℝ} (hab : a ≤ b)
    (ha : 0 < A+B*a) (hb : 0 < A+B*b) (d : ℝ → ℝ)
    (hd : ContinuousOn d (Set.Ioc a b))
    (hbound : ∀ e ∈ Set.Ioc a b, A+B*e ≤ d e) :
    IntervalIntegrable (fun e => 1/d e) volume a b ∧
      (∫ e in a..b, 1/d e) ≤ ∫ e in a..b, 1/(A+B*e) := by
  have hapos : ∀ e ∈ Set.Icc a b, 0 < A+B*e := affine_pos_of_endpoints hab ha hb
  have hdpos : ∀ e ∈ Set.Ioc a b, 0 < d e := by
    intro e he
    exact (hapos e ⟨he.1.le, he.2⟩).trans_le (hbound e he)
  have hi : IntervalIntegrable (fun e => 1/(A+B*e)) volume a b :=
    intervalIntegrable_affine_reciprocal hab ha hb
  have hmeas : AEStronglyMeasurable (fun e => 1/d e) (volume.restrict (Ι a b)) := by
    rw [Set.uIoc_of_le hab]
    exact (continuousOn_const.div hd (fun e he => (hdpos e he).ne')).aestronglyMeasurable measurableSet_Ioc
  have hirecip : IntervalIntegrable (fun e => 1/d e) volume a b := by
    apply hi.mono_fun' hmeas
    rw [Set.uIoc_of_le hab]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with e he
    rw [Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (hdpos e he))]
    exact one_div_le_one_div_of_le (hapos e ⟨he.1.le, he.2⟩) (hbound e he)
  refine ⟨hirecip, ?_⟩
  apply intervalIntegral.integral_mono_on_of_le_Ioo hab hirecip hi
  intro e he
  exact one_div_le_one_div_of_le (hapos e ⟨he.1.le, he.2.le⟩) (hbound e ⟨he.1, he.2.le⟩)

theorem continuousOn_profile_sum {ι : Type*} [Fintype ι]
    (w q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    ContinuousOn (fun e => ∑ i, w i*CK.Profile.profile e (q i)) (Set.Ioi (0 : ℝ)) := by
  apply continuousOn_finsetSum
  intro i _
  exact continuousOn_const.mul (CK.Profile.continuousOn_profile_of_nonneg (hq i))

/-- Rational coefficients below the true tangent coefficients remain
valid for every nonnegative entropy argument. -/
theorem profile_panel_affine_bound {ι : Type*} [Fintype ι]
    (w q t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 ≤ q i)
    (ht : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1) {A B : ℝ}
    (hA : A ≤ ∑ i, w i*q i*(Real.artanh (t i)+
      CK.Profile.meanEntropy (t i)/t i*CK.Profile.tangentFactor (t i)))
    (hB : B ≤ 1-∑ i, w i*CK.Profile.tangentFactor (t i)) {e : ℝ} (he : 0 < e) :
    A+B*e ≤ e+∑ i, w i*CK.Profile.profile e (q i) := by
  have h := CK.Profile.affine_lower_bound_profile_sum he w q t hw hq ht
  have hBe := mul_le_mul_of_nonneg_right hB he.le
  linarith only [h, hA, hBe]

/-- A rational affine panel, its positive endpoint checks, and one proved
logarithm bound suffice for the full actual-profile integral comparison. -/
theorem profile_panel_integral_bound {ι : Type*} [Fintype ι]
    (w q t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 ≤ q i)
    (ht : ∀ i, t i ∈ Set.Ioo (0 : ℝ) 1) {a b A B U : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) (hApos : 0 < A+B*a) (hBpos : 0 < A+B*b)
    (hBneg : B < 0)
    (hA : A ≤ ∑ i, w i*q i*(Real.artanh (t i)+
      CK.Profile.meanEntropy (t i)/t i*CK.Profile.tangentFactor (t i)))
    (hB : B ≤ 1-∑ i, w i*CK.Profile.tangentFactor (t i))
    (hlog : Real.log ((A+B*a)/(A+B*b)) ≤ (-B)*U) :
    IntervalIntegrable (fun e => 1/(e+∑ i, w i*CK.Profile.profile e (q i))) volume a b ∧
      (∫ e in a..b, 1/(e+∑ i, w i*CK.Profile.profile e (q i))) ≤ U := by
  obtain ⟨hi, hle⟩ := reciprocal_integral_le_affine_panel hab hApos hBpos
    (fun e => e+∑ i, w i*CK.Profile.profile e (q i))
    (continuousOn_id.add ((continuousOn_profile_sum w q hq).mono
      (fun _ he => lt_of_le_of_lt ha0 he.1)))
    (fun e he => profile_panel_affine_bound w q t hw hq ht hA hB (lt_of_le_of_lt ha0 he.1))
  refine ⟨hi, hle.trans ?_⟩
  rw [integral_affine_reciprocal hApos hBpos hBneg.ne]
  have hl : Real.log ((A+B*a)/(A+B*b)) =
      Real.log (A+B*a)-Real.log (A+B*b) := Real.log_div hApos.ne' hBpos.ne'
  rw [hl] at hlog
  apply (div_le_iff_of_neg hBneg).2
  linarith only [hlog]

end
end CK.Certificate
