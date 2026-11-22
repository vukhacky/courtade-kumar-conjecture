module
public import CK.Certificate.ClockGeometryBand4Data
public import CK.Middle.ClockConsequences

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set
open CK.Profile
namespace CK.Certificate.ClockGeometry.Band4
noncomputable section

theorem segment0_lower_profile {e : ℝ} (he : 0 < e) :
    CK.Certificate.ClockBatch.C20.profile e ≤ movingProfile 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a0^2) e := by
  rw [a0_profile]
  have h := small_chord_le_packed (e:=e) (c:=a0) (r:=((-7499/9900))*a0^2+((10108792633/19800000000))-(2:ℝ)*a0^2) (w:=(5306792633/1631360000))
    he (by norm_num [a0]) 2 segment0_domain.2.2.2.2.2.1 (by norm_num [a0])
  simpa only [movingProfile,Real.sqrt_sq a0_nonneg,Nat.cast_ofNat] using h

theorem segment0_lower_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((39/40):ℝ) 1) :
    clock (movingProfile 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a0^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hρpos : 0 < ρ := lt_of_lt_of_le (by norm_num) hρ.1
  have hy : 0 ≤ meanEntropy ρ/ρ :=
    (div_pos (meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩) hρpos).le
  refine le_trans (clock_le_clock_of_envelope
    (movingProfile_continuous 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a0^2))
    (movingProfile_antitone 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a0^2))
    (fun e he => movingProfile_pos 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (by norm_num [a0]) he)
    CK.Certificate.ClockBatch.C20.profile_continuous
    (sumProfile_antitone CK.Certificate.ClockBatch.C20.weights CK.Certificate.ClockBatch.C20.parameters CK.Certificate.ClockBatch.C20.weights_nonneg CK.Certificate.ClockBatch.C20.parameters_nonneg)
    (fun e he => sumProfile_pos CK.Certificate.ClockBatch.C20.weights CK.Certificate.ClockBatch.C20.parameters CK.Certificate.ClockBatch.C20.weights_nonneg CK.Certificate.ClockBatch.C20.parameters_nonneg CK.Certificate.ClockBatch.C20.positive_term he)
    (fun e he => segment0_lower_profile he) hy) ?_
  exact CK.Middle.ClockConsequences.C20_propagated hρ

theorem segment0_upper_profile (e : ℝ) :
    movingProfile 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a1^2) e = CK.Certificate.ClockBatch.C21.profile e := by
  rw [a1_profile]
  simp only [movingProfile,Real.sqrt_sq a1_nonneg]
  have hc : 0 ≤ a1 := by linarith [a1_bounds.1,a1_bounds.2]
  have hr := segment0_upper_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment0_upper_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((39/40):ℝ) 1) :
    clock (movingProfile 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a1^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 2 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a1^2) = CK.Certificate.ClockBatch.C21.profile := funext segment0_upper_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C21_propagated hρ

theorem segment1_lower_profile (e : ℝ) :
    movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a1^2) e = CK.Certificate.ClockBatch.C21.profile e := by
  rw [a1_profile]
  simp only [movingProfile,Real.sqrt_sq a1_nonneg]
  have hc : 0 ≤ a1 := by linarith [a1_bounds.1,a1_bounds.2]
  have hr := segment1_lower_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals norm_num [Real.sqrt_sq hc,r1]
  all_goals ring

theorem segment1_lower_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((39/40):ℝ) 1) :
    clock (movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a1^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a1^2) = CK.Certificate.ClockBatch.C21.profile := funext segment1_lower_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C21_propagated hρ

theorem segment1_upper_profile (e : ℝ) :
    movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a2^2) e = CK.Certificate.ClockBatch.C22.profile e := by
  rw [a2_profile]
  simp only [movingProfile,Real.sqrt_sq a2_nonneg]
  have hc : 0 ≤ a2 := by linarith [a2_bounds.1,a2_bounds.2]
  have hr := segment1_upper_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment1_upper_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((39/40):ℝ) 1) :
    clock (movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a2^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) (fun x => x) (a2^2) = CK.Certificate.ClockBatch.C22.profile := funext segment1_upper_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C22_propagated hρ

theorem segment2_lower_profile (e : ℝ) :
    movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) highCap (a2^2) e = CK.Certificate.ClockBatch.C22.profile e := by
  rw [a2_profile]
  simp only [movingProfile,highCap,Real.sqrt_sq a2_nonneg]
  have hc : 0 ≤ (1-a2) := by linarith [a2_bounds.1,a2_bounds.2]
  have hr := segment2_lower_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals have hh : 1-a2=a2 := by norm_num [a2]
  all_goals rw [hh]
  all_goals ring

theorem segment2_lower_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((39/40):ℝ) 1) :
    clock (movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) highCap (a2^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) highCap (a2^2) = CK.Certificate.ClockBatch.C22.profile := funext segment2_lower_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C22_propagated hρ

theorem segment2_upper_profile (e : ℝ) :
    movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) highCap (a3^2) e = CK.Certificate.ClockBatch.C23.profile e := by
  rw [a3_profile]
  simp only [movingProfile,highCap,Real.sqrt_sq a3_nonneg]
  have hc : 0 ≤ (1-a3) := by linarith [a3_bounds.1,a3_bounds.2]
  have hr := segment2_upper_residual
  try simp only [Real.sqrt_sq hc]
  norm_num only [Nat.cast_ofNat] at hr ⊢
  all_goals rw [hr]
  all_goals ring

theorem segment2_upper_clock {ρ : ℝ} (hρ : ρ ∈ Ico ((39/40):ℝ) 1) :
    clock (movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) highCap (a3^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hp : movingProfile 1 ((-7499/9900)) ((10108792633/19800000000)) highCap (a3^2) = CK.Certificate.ClockBatch.C23.profile := funext segment2_upper_profile
  rw [hp]
  exact CK.Middle.ClockConsequences.C23_propagated hρ

end
end CK.Certificate.ClockGeometry.Band4
