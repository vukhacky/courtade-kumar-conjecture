module

public import CK.Low.CentralEnergy
public import CK.Low.YuReduction
public import CK.Low.LocalIntervals

/-! The low-correlation Shannon inequality with its mean term, using kernel-checked interval and logarithm certificates. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

/-- CK for every Boolean function and every correlation in `[0,457/500]`.
This includes dimension zero, constants, unbalanced functions, and zero noise. -/
theorem information_le_phi_low_range {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (457/500)) (f : BooleanFunction n) :
    information ρ f ≤ phi ρ := by
  classical
  have hρ01 : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1,by linarith [hρ.2]⟩
  by_cases hm : (61/100 : ℝ) ≤ |mean f|
  · exact information_le_phi_of_large_mean hρ01 f hm
  by_cases hs : ∃ i, (69/100 : ℝ) ≤ |fourier (lift f) {i}|
  · obtain ⟨i,hi⟩ := hs
    exact information_le_phi_of_local_threshold hρ01 (by norm_num) f i hi
      (localDeficit_threshold_low_interval hρ)
  have hcap : fourierWeight (lift f) 1 + mean f^2 ≤ 193027/250000 := by
    apply (oddLift_firstLevel_lt_cap f ?_ ?_).le
    · linarith [lt_of_not_ge hm]
    · intro i
      exact (lt_of_not_ge (fun h => hs ⟨i,h⟩)).le
  by_cases hr : ρ ≤ (3/5 : ℝ)
  · exact information_le_phi_small_of_cap ⟨hρ.1,hr⟩ f hcap
  · exact (information_lt_phi_central_of_cap ⟨(lt_of_not_ge hr).le,hρ.2⟩ f hcap).le

/-- The low-correlation theorem in exact Shannon semantics. -/
theorem mutualInformation_le_phi_low_range {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (457/500)) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information ⟨hρ.1,by linarith [hρ.2]⟩]
  exact information_le_phi_low_range hρ f

/-- The low-correlation theorem with natural-log binary entropy expanded. -/
theorem mutualInformation_le_binaryEntropy_low_range {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (457/500)) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ Real.log 2 - Real.binEntropy ((1-ρ)/2) :=
  mutualInformation_le_phi_low_range hρ f

end
end CK
