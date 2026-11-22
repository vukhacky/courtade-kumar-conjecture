module

public import CK.Profile.Packing
public import CK.Profile.ClockPilot
public import CK.Profile.ClockComparison
public import CK.Profile.ClockPropagation

/-! The P03 Shannon mutual information bound in the stated Fourier coefficient region. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace CK
noncomputable section

/-- The P03 Fourier coefficient region in every dimension. -/
theorem mutualInformation_lt_phi_p03 {n : ℕ} (f : BooleanFunction n)
    (hcap : ∀ i : Fin n, |fourier (lift f) {i}| ≤ (2/5 : ℝ))
    (hW : (353357479/523750000 : ℝ) ≤ fourierWeight (lift f) 1) :
    mutualInformation (457/500) f < phi (457/500) := by
  have hWpos : 0 < fourierWeight (lift f) 1 := lt_of_lt_of_le (by norm_num) hW
  apply Profile.mutualInformation_lt_phi_of_clock_envelope
    (ρ := Certificate.P03.rho) (Y := Certificate.P03.endpointY)
    (by norm_num [Certificate.P03.rho]) f hWpos
    (by norm_num [Certificate.P03.endpointY])
    (fun e => Certificate.P03.weight*Profile.profile e Certificate.P03.profileQ)
    Profile.p03_endpoint_enclosure.le
  · intro e he
    have hp := Profile.profile_pos he.1
      (show (0 : ℝ) < Certificate.P03.profileQ by norm_num [Certificate.P03.profileQ])
    have hw : (0 : ℝ) < Certificate.P03.weight := by norm_num [Certificate.P03.weight]
    exact add_pos he.1 (mul_pos hw hp)
  · intro e he
    apply Profile.singletonProfile_ge_capped_envelope f he.1
      (show (0 : ℝ) < Certificate.P03.profileQ by norm_num [Certificate.P03.profileQ])
    · exact hcap
    · convert hW using 1 <;> norm_num [Certificate.P03.weight, Certificate.P03.profileQ]
  · exact Profile.p03_profileClock_certified.1
  · have h := Profile.p03_profileClock_certified.2
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
      (by norm_num [Certificate.P03.rho] : Certificate.P03.rho ≠ 0), Real.log_one] at h
    linarith

/-- The same Fourier cell is covered at every larger correlation, with
the endpoint rho=1 handled by the exact Shannon identity. -/
theorem mutualInformation_le_phi_p03_interval {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) 1) (f : BooleanFunction n)
    (hcap : ∀ i : Fin n, |fourier (lift f) {i}| ≤ (2/5 : ℝ))
    (hW : (353357479/523750000 : ℝ) ≤ fourierWeight (lift f) 1) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases h1 : ρ=1
  · subst ρ
    exact mutualInformation_one_le f
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hρ.1], lt_of_le_of_ne hρ.2 h1⟩
  let Q := fun e => Certificate.P03.weight*Profile.profile e Certificate.P03.profileQ
  have hw : (0 : ℝ) < Certificate.P03.weight := by norm_num [Certificate.P03.weight]
  have hq : (0 : ℝ) < Certificate.P03.profileQ := by norm_num [Certificate.P03.profileQ]
  have hc : ContinuousOn Q (Ioi (0 : ℝ)) :=
    continuousOn_const.mul (Profile.continuousOn_profile hq)
  have ha : AntitoneOn Q (Ioi (0 : ℝ)) := by
    intro e he d hd hed
    exact mul_le_mul_of_nonneg_left (Profile.profile_antitone hq he hd hed) hw.le
  have hp : ∀ e, 0 < e → 0 < Q e := fun e he => mul_pos hw (Profile.profile_pos he hq)
  have hr0 : Certificate.P03.rho ∈ Ioo (0 : ℝ) 1 := by norm_num [Certificate.P03.rho]
  have hH : 0 < Profile.meanEntropy Certificate.P03.rho/Certificate.P03.rho :=
    div_pos (Profile.meanEntropy_pos ⟨by linarith [hr0.1], hr0.2⟩) hr0.1
  have hY : 0 < Certificate.P03.endpointY := by norm_num [Certificate.P03.endpointY]
  have hsum : Profile.sumProfile (fun _ : Fin 1 => Certificate.P03.weight)
      (fun _ : Fin 1 => Certificate.P03.profileQ)=Q := by
    funext e
    simp [Profile.sumProfile, Q]
  have hbase : Profile.clock Q (Profile.meanEntropy Certificate.P03.rho/Certificate.P03.rho) ≤
      -Real.log Certificate.P03.rho := by
    have hm := (Profile.strictMonoOn_clock hc ha hp).monotoneOn hH.le hY.le
      Profile.p03_endpoint_enclosure.le
    have hh := Profile.p03_profileClock_certified.2
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hr0.1), Real.log_one] at hh
    change Profile.clock Q Certificate.P03.endpointY+(7/1000 : ℝ) < _ at hh
    linarith only [hm, hh]
  have hclock := Profile.fixed_profile_clock_propagates
    (fun _ : Fin 1 => Certificate.P03.weight) (fun _ : Fin 1 => Certificate.P03.profileQ)
    (fun _ => hw.le) (fun _ => by norm_num [Certificate.P03.profileQ])
    ⟨0, hw, hq⟩ hr0 ⟨hρ.1, hρ01.2⟩
    (by simpa only [hsum] using hbase)
  apply Profile.mutualInformation_le_phi_of_profile_clock hρ01 f
    (lt_of_lt_of_le (by norm_num) hW) Q hc ha hp
  · intro e he
    apply Profile.singletonProfile_ge_capped_envelope f he hq hcap
    convert hW using 1 <;> norm_num [Certificate.P03.weight, Certificate.P03.profileQ]
  · simpa only [hsum] using hclock

end
end CK
