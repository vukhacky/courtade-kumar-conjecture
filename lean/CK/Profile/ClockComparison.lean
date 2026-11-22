module

public import CK.Profile.ClockDynamics
public import CK.Basic.ShannonBridge

/-! From an upper bound for the integrated clock of the actual singleton profiles to an entropy bound. Each integral comes with an integrability proof. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace CK.Profile
noncomputable section

/-- A certified upper clock forces the actual conditional entropy past its
endpoint. Only the interval covered by the certificate is required. -/
theorem conditionalEntropy_gt_of_clock_envelope {n : ℕ} {ρ Y : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n)
    (hW : 0 < fourierWeight (lift f) 1) (hY : 0 < Y) (Q : ℝ → ℝ)
    (hQpos : ∀ e ∈ Ioo (0 : ℝ) Y, 0 < e+Q e)
    (hQle : ∀ e ∈ Ioo (0 : ℝ) Y, Q e ≤ singletonProfile f e)
    (hiQ : IntervalIntegrable (fun e => 1/(e+Q e)) volume 0 Y)
    (hclock : (∫ e in (0 : ℝ)..Y, 1/(e+Q e)) < -Real.log ρ) :
    ρ*Y < conditionalEntropy ρ f := by
  have hc := continuousOn_singletonProfile f
  have ha := singletonProfile_antitone f
  have hp := singletonProfile_pos f hW
  have hcmp : clock (singletonProfile f) Y ≤ ∫ e in (0 : ℝ)..Y, 1/(e+Q e) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hY.le
      (clock_integrable hc ha hp hY) hiQ
    intro e he
    exact one_div_le_one_div_of_le (hQpos e he) (by linarith only [hQle e he])
  have hactual := profile_clock_lower_bound hρ f hW
  have he := conditionalEntropy_pos hρ f (nonconstant_of_weight_pos f hW)
  have hy : Y < conditionalEntropy ρ f/ρ := by
    by_contra h
    have hmono := (strictMonoOn_clock hc ha hp).monotoneOn
      (show conditionalEntropy ρ f/ρ ∈ Ici (0 : ℝ) from (div_pos he hρ.1).le)
      hY.le (le_of_not_gt h)
    linarith only [hactual, hcmp, hclock, hmono]
  have h := (lt_div_iff₀ hρ.1).mp hy
  simpa only [mul_comm] using h

/-- Shannon mutual information bound from the profile envelope and its clock bound. -/
theorem mutualInformation_lt_phi_of_clock_envelope {n : ℕ} {ρ Y : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n)
    (hW : 0 < fourierWeight (lift f) 1) (hY : 0 < Y) (Q : ℝ → ℝ)
    (hend : meanEntropy ρ/ρ ≤ Y)
    (hQpos : ∀ e ∈ Ioo (0 : ℝ) Y, 0 < e+Q e)
    (hQle : ∀ e ∈ Ioo (0 : ℝ) Y, Q e ≤ singletonProfile f e)
    (hiQ : IntervalIntegrable (fun e => 1/(e+Q e)) volume 0 Y)
    (hclock : (∫ e in (0 : ℝ)..Y, 1/(e+Q e)) < -Real.log ρ) :
    mutualInformation ρ f < phi ρ := by
  have he := conditionalEntropy_gt_of_clock_envelope hρ f hW hY Q hQpos hQle hiQ hclock
  have hH : meanEntropy ρ ≤ ρ*Y := by
    have h := (div_le_iff₀ hρ.1).mp hend
    simpa only [mul_comm] using h
  rw [mutualInformation_eq_information ⟨hρ.1.le, hρ.2.le⟩,
    information_eq_initial_sub_conditional]
  have hm : Real.binEntropy ((1-mean f)/2) ≤ Real.log 2 := Real.binEntropy_le_log_two
  change Real.binEntropy ((1-mean f)/2)-conditionalEntropy ρ f < Real.log 2-meanEntropy ρ
  linarith only [he, hH, hm]

end
end CK.Profile
