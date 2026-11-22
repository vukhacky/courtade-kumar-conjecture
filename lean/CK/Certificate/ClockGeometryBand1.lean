module
public import CK.Certificate.ClockGeometryBand1Data
public import CK.Middle.ClockConsequences

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set
open CK.Profile
namespace CK.Certificate.ClockGeometry.Band1
noncomputable section

theorem segment0_lower_profile {e : ℝ} (he : 0 < e) :
    CK.Certificate.ClockBatch.C07.profile e ≤ movingProfile 2 (-1) ((1909002661/3215937500)) (fun x => x) (a0^2) e := by
  rw [a0_profile]
  have h := small_chord_le_packed (e:=e) (c:=a0) (r:=(-1)*a0^2+((1909002661/3215937500))-(2:ℝ)*a0^2) (w:=(1909002661/514550000))
    he (by norm_num [a0]) 2 segment0_domain.2.2.2.2.2.1 (by norm_num [a0])
  simpa only [movingProfile,Real.sqrt_sq a0_nonneg,Nat.cast_ofNat] using h

theorem segment0_lower_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 2 (-1) ((1909002661/3215937500)) (fun x => x) (a0^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ.1
  have hy : 0 ≤ meanEntropy ρ/ρ :=
    (div_pos (meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩) hρpos).le
  refine le_trans (clock_le_clock_of_envelope
    (movingProfile_continuous 2 (-1) ((1909002661/3215937500)) (fun x => x) (a0^2))
    (movingProfile_antitone 2 (-1) ((1909002661/3215937500)) (fun x => x) (a0^2))
    (fun e he => movingProfile_pos 2 (-1) ((1909002661/3215937500)) (fun x => x) (by norm_num [a0]) he)
    CK.Certificate.ClockBatch.C07.profile_continuous
    (sumProfile_antitone CK.Certificate.ClockBatch.C07.weights CK.Certificate.ClockBatch.C07.parameters CK.Certificate.ClockBatch.C07.weights_nonneg CK.Certificate.ClockBatch.C07.parameters_nonneg)
    (fun e he => sumProfile_pos CK.Certificate.ClockBatch.C07.weights CK.Certificate.ClockBatch.C07.parameters CK.Certificate.ClockBatch.C07.weights_nonneg CK.Certificate.ClockBatch.C07.parameters_nonneg CK.Certificate.ClockBatch.C07.positive_term he)
    (fun e he => segment0_lower_profile he) hy) ?_
  exact CK.Middle.ClockConsequences.C07_propagated hρ

theorem segment0_upper_profile (e : ℝ) :
    movingProfile 2 (-1) ((1909002661/3215937500)) (fun x => x) (a1^2) e = CK.Certificate.ClockBatch.C08.profile e := by
  rw [a1_profile]
  simp only [movingProfile,Real.sqrt_sq a1_nonneg]
  have hc : 0 ≤ a1 := by linarith [a1_bounds.1,a1_bounds.2]
  have hr := segment0_upper_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment0_upper_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 2 (-1) ((1909002661/3215937500)) (fun x => x) (a1^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 2 (-1) ((1909002661/3215937500)) (fun x => x) (a1^2) = CK.Certificate.ClockBatch.C08.profile := funext segment0_upper_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C08_propagated hρ

theorem segment1_lower_profile (e : ℝ) :
    movingProfile 2 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a1^2) e = CK.Certificate.ClockBatch.C08.profile e := by
  rw [a1_profile]
  simp only [movingProfile,Real.sqrt_sq a1_nonneg]
  have hc : 0 ≤ a1 := by linarith [a1_bounds.1,a1_bounds.2]
  have hr := segment1_lower_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment1_lower_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 2 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a1^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 2 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a1^2) = CK.Certificate.ClockBatch.C08.profile := funext segment1_lower_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C08_propagated hρ

theorem segment1_upper_profile (e : ℝ) :
    movingProfile 2 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a2^2) e = CK.Certificate.ClockBatch.C09.profile e := by
  rw [a2_profile]
  simp only [movingProfile,Real.sqrt_sq a2_nonneg]
  have hc : 0 ≤ a2 := by linarith [a2_bounds.1,a2_bounds.2]
  have hr := segment1_upper_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment1_upper_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 2 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a2^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 2 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a2^2) = CK.Certificate.ClockBatch.C09.profile := funext segment1_upper_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C09_propagated hρ

theorem segment2_lower_profile (e : ℝ) :
    movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a2^2) e = CK.Certificate.ClockBatch.C09.profile e := by
  rw [a2_profile]
  simp only [movingProfile,Real.sqrt_sq a2_nonneg]
  have hc : 0 ≤ a2 := by linarith [a2_bounds.1,a2_bounds.2]
  have hr := segment2_lower_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals norm_num [Real.sqrt_sq hc,r2]
  all_goals ring

theorem segment2_lower_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a2^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a2^2) = CK.Certificate.ClockBatch.C09.profile := funext segment2_lower_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C09_propagated hρ

theorem segment2_upper_profile (e : ℝ) :
    movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a3^2) e = CK.Certificate.ClockBatch.C10.profile e := by
  rw [a3_profile]
  simp only [movingProfile,Real.sqrt_sq a3_nonneg]
  have hc : 0 ≤ a3 := by linarith [a3_bounds.1,a3_bounds.2]
  have hr := segment2_upper_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment2_upper_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a3^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) (fun x => x) (a3^2) = CK.Certificate.ClockBatch.C10.profile := funext segment2_upper_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C10_propagated hρ

theorem segment3_lower_profile (e : ℝ) :
    movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) highCap (a3^2) e = CK.Certificate.ClockBatch.C10.profile e := by
  rw [a3_profile]
  simp only [movingProfile,highCap,Real.sqrt_sq a3_nonneg]
  have hc : 0 ≤ (1-a3) := by linarith [a3_bounds.1,a3_bounds.2]
  have hr := segment3_lower_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals have hh : 1-a3=a3 := by norm_num [a3]
  all_goals rw [hh]
  all_goals ring

theorem segment3_lower_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) highCap (a3^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) highCap (a3^2) = CK.Certificate.ClockBatch.C10.profile := funext segment3_lower_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C10_propagated hρ

theorem segment3_upper_profile (e : ℝ) :
    movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) highCap (a4^2) e = CK.Certificate.ClockBatch.C11.profile e := by
  rw [a4_profile]
  simp only [movingProfile,highCap,Real.sqrt_sq a4_nonneg]
  have hc : 0 ≤ (1-a4) := by linarith [a4_bounds.1,a4_bounds.2]
  have hr := segment3_upper_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment3_upper_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((19/20):ℝ) 1) :
    clock (movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) highCap (a4^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-29991/39400)) ((3379158911/6156250000)) highCap (a4^2) = CK.Certificate.ClockBatch.C11.profile := funext segment3_upper_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C11_propagated hρ

end
end CK.Certificate.ClockGeometry.Band1
