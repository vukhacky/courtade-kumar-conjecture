module

public import CK.Profile.CappedClock
public import CK.Middle.ClockConsequences
public import CK.Middle.CubicBands

/-! The common small-singleton part of all five middle bands, with the
energy/clock alternatives fully discharged in actual Shannon semantics. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle
noncomputable section
open CK.Profile

theorem common_profile_band0 : CK.Certificate.ClockBatch.C00.profile =
    (fun e => (353357479/83800000 : ℝ)*CK.Profile.profile e (2/5)) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C00.profile,CK.Certificate.ClockBatch.C00.weights,CK.Certificate.ClockBatch.C00.parameters,CK.Certificate.ClockBatch.C00.v001,CK.Certificate.ClockBatch.C00.v000,Fin.sum_univ_succ]

theorem mutualInformation_le_phi_band0_small_singletons {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hcap : ∀ i, |fourier (lift f) {i}| ≤ (2/5 : ℝ)) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (353357479/523750000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band0 hρ f
    exact cubicWeight_le_of_parseval_cell (by linarith [hρ.1]) hρ.2 (by norm_num)
      f hW (by norm_num [cubicBeta])
  · have hclock := ClockConsequences.C00_propagated (ρ := ρ) ⟨hρ.1,by linarith [hρ.2]⟩
    rw [common_profile_band0] at hclock
    apply mutualInformation_le_phi_capped_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f (by norm_num : (0 : ℝ)<2/5) (by norm_num : (0 : ℝ)<353357479/83800000) hcap
    · norm_num
      exact (lt_of_not_ge hW).le
    · exact hclock

theorem common_profile_band1 : CK.Certificate.ClockBatch.C07.profile =
    (fun e => (1909002661/514550000 : ℝ)*CK.Profile.profile e (2/5)) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C07.profile,CK.Certificate.ClockBatch.C07.weights,CK.Certificate.ClockBatch.C07.parameters,CK.Certificate.ClockBatch.C07.v001,CK.Certificate.ClockBatch.C07.v000,Fin.sum_univ_succ]

theorem mutualInformation_le_phi_band1_small_singletons {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (19/20 : ℝ) (97/100)) (f : BooleanFunction n)
    (hcap : ∀ i, |fourier (lift f) {i}| ≤ (2/5 : ℝ)) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (1909002661/3215937500 : ℝ)
  · apply mutualInformation_le_phi_cubic_band1 hρ f
    exact cubicWeight_le_of_parseval_cell (by linarith [hρ.1]) hρ.2 (by norm_num)
      f hW (by norm_num [cubicBeta])
  · have hclock := ClockConsequences.C07_propagated (ρ := ρ) ⟨hρ.1,by linarith [hρ.2]⟩
    rw [common_profile_band1] at hclock
    apply mutualInformation_le_phi_capped_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f (by norm_num : (0 : ℝ)<2/5) (by norm_num : (0 : ℝ)<1909002661/514550000) hcap
    · norm_num
      exact (lt_of_not_ge hW).le
    · exact hclock

theorem common_profile_band2 : CK.Certificate.ClockBatch.C12.profile =
    (fun e => (29150089291/8202592000 : ℝ)*CK.Profile.profile e (2/5)) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C12.profile,CK.Certificate.ClockBatch.C12.weights,CK.Certificate.ClockBatch.C12.parameters,CK.Certificate.ClockBatch.C12.v001,CK.Certificate.ClockBatch.C12.v000,Fin.sum_univ_succ]

theorem mutualInformation_le_phi_band2_small_singletons {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (97/100 : ℝ) (487/500)) (f : BooleanFunction n)
    (hcap : ∀ i, |fourier (lift f) {i}| ≤ (2/5 : ℝ)) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (29150089291/51266200000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band2 hρ f
    exact cubicWeight_le_of_parseval_cell (by linarith [hρ.1]) hρ.2 (by norm_num)
      f hW (by norm_num [cubicBeta])
  · have hclock := ClockConsequences.C12_propagated (ρ := ρ) ⟨hρ.1,by linarith [hρ.2]⟩
    rw [common_profile_band2] at hclock
    apply mutualInformation_le_phi_capped_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f (by norm_num : (0 : ℝ)<2/5) (by norm_num : (0 : ℝ)<29150089291/8202592000) hcap
    · norm_num
      exact (lt_of_not_ge hW).le
    · exact hclock

theorem common_profile_band3 : CK.Certificate.ClockBatch.C16.profile =
    (fun e => (23011179967/6556000000 : ℝ)*CK.Profile.profile e (2/5)) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C16.profile,CK.Certificate.ClockBatch.C16.weights,CK.Certificate.ClockBatch.C16.parameters,CK.Certificate.ClockBatch.C16.v001,CK.Certificate.ClockBatch.C16.v000,Fin.sum_univ_succ]

theorem mutualInformation_le_phi_band3_small_singletons {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (487/500 : ℝ) (39/40)) (f : BooleanFunction n)
    (hcap : ∀ i, |fourier (lift f) {i}| ≤ (2/5 : ℝ)) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (23011179967/40975000000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band3 hρ f
    exact cubicWeight_le_of_parseval_cell (by linarith [hρ.1]) hρ.2 (by norm_num)
      f hW (by norm_num [cubicBeta])
  · have hclock := ClockConsequences.C16_propagated (ρ := ρ) ⟨hρ.1,by linarith [hρ.2]⟩
    rw [common_profile_band3] at hclock
    apply mutualInformation_le_phi_capped_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f (by norm_num : (0 : ℝ)<2/5) (by norm_num : (0 : ℝ)<23011179967/6556000000) hcap
    · norm_num
      exact (lt_of_not_ge hW).le
    · exact hclock

theorem common_profile_band4 : CK.Certificate.ClockBatch.C20.profile =
    (fun e => (5306792633/1631360000 : ℝ)*CK.Profile.profile e (2/5)) := by
  funext e
  norm_num [CK.Certificate.ClockBatch.C20.profile,CK.Certificate.ClockBatch.C20.weights,CK.Certificate.ClockBatch.C20.parameters,CK.Certificate.ClockBatch.C20.v001,CK.Certificate.ClockBatch.C20.v000,Fin.sum_univ_succ]

theorem mutualInformation_le_phi_band4_small_singletons {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hcap : ∀ i, |fourier (lift f) {i}| ≤ (2/5 : ℝ)) :
    mutualInformation ρ f ≤ phi ρ := by
  by_cases hW : fourierWeight (lift f) 1 ≤ (5306792633/10196000000 : ℝ)
  · apply mutualInformation_le_phi_cubic_band4 hρ f
    exact cubicWeight_le_of_parseval_cell (by linarith [hρ.1]) hρ.2 (by norm_num)
      f hW (by norm_num [cubicBeta])
  · have hclock := ClockConsequences.C20_propagated (ρ := ρ) ⟨hρ.1,by linarith [hρ.2]⟩
    rw [common_profile_band4] at hclock
    apply mutualInformation_le_phi_capped_clock
      (show ρ ∈ Ioo (0 : ℝ) 1 from ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
      f (by norm_num : (0 : ℝ)<2/5) (by norm_num : (0 : ℝ)<5306792633/1631360000) hcap
    · norm_num
      exact (lt_of_not_ge hW).le
    · exact hclock

end
end CK.Middle
