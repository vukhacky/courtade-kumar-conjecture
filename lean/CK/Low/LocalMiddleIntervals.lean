module

public import CK.Low.LocalIntervals
public import CK.Certificate.LocalTaylorMiddle0
public import CK.Certificate.LocalTaylorMiddle1
public import CK.Certificate.LocalTaylorMiddle2
public import CK.Certificate.LocalTaylorMiddle3

/-! Four certified local thresholds in the STOC middle-range cover.
Each theorem includes every smaller correlation and every larger absolute
singleton coefficient, with the original mean retained. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem localDeficit_threshold_middle0_interval {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (19/20)) :
    0 ≤ localDeficit ρ (16749/25000) := by
  apply localDeficit_nonneg_of_taylor 64 20 (R := 19/20)
    (L := 3465735902799729/5000000000000000) (by norm_num) (by norm_num) (by norm_num)
    hρ Certificate.P03.log_two_bounds.2
  exact Certificate.LocalTaylorMiddle0.polynomial_nonneg
    ⟨sq_nonneg ρ, pow_le_pow_left₀ hρ.1 hρ.2 2⟩

theorem information_le_phi_middle0_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (19/20)) (f : BooleanFunction n) (i : Fin n)
    (hi : (16749/25000 : ℝ) ≤ |fourier (lift f) {i}|) :
    information ρ f ≤ phi ρ := by
  have hr : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1, by linarith [hρ.2]⟩
  exact information_le_phi_of_local_threshold hr (by norm_num) f i hi
    (localDeficit_threshold_middle0_interval hρ)

theorem mutualInformation_le_phi_middle0_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (19/20)) (f : BooleanFunction n) (i : Fin n)
    (hi : (16749/25000 : ℝ) ≤ |fourier (lift f) {i}|) :
    mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information_all]
  exact information_le_phi_middle0_large_singleton hρ f i hi

theorem localDeficit_threshold_middle1_interval {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (97/100)) :
    0 ≤ localDeficit ρ (14449/20000) := by
  apply localDeficit_nonneg_of_taylor 96 24 (R := 97/100)
    (L := 3465735902799729/5000000000000000) (by norm_num) (by norm_num) (by norm_num)
    hρ Certificate.P03.log_two_bounds.2
  exact Certificate.LocalTaylorMiddle1.polynomial_nonneg
    ⟨sq_nonneg ρ, pow_le_pow_left₀ hρ.1 hρ.2 2⟩

theorem information_le_phi_middle1_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (97/100)) (f : BooleanFunction n) (i : Fin n)
    (hi : (14449/20000 : ℝ) ≤ |fourier (lift f) {i}|) :
    information ρ f ≤ phi ρ := by
  have hr : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1, by linarith [hρ.2]⟩
  exact information_le_phi_of_local_threshold hr (by norm_num) f i hi
    (localDeficit_threshold_middle1_interval hρ)

theorem mutualInformation_le_phi_middle1_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (97/100)) (f : BooleanFunction n) (i : Fin n)
    (hi : (14449/20000 : ℝ) ≤ |fourier (lift f) {i}|) :
    mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information_all]
  exact information_le_phi_middle1_large_singleton hρ f i hi

theorem localDeficit_threshold_middle2_interval {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (487/500)) :
    0 ≤ localDeficit ρ (589/800) := by
  apply localDeficit_nonneg_of_taylor 128 24 (R := 487/500)
    (L := 3465735902799729/5000000000000000) (by norm_num) (by norm_num) (by norm_num)
    hρ Certificate.P03.log_two_bounds.2
  exact Certificate.LocalTaylorMiddle2.polynomial_nonneg
    ⟨sq_nonneg ρ, pow_le_pow_left₀ hρ.1 hρ.2 2⟩

theorem information_le_phi_middle2_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (487/500)) (f : BooleanFunction n) (i : Fin n)
    (hi : (589/800 : ℝ) ≤ |fourier (lift f) {i}|) :
    information ρ f ≤ phi ρ := by
  have hr : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1, by linarith [hρ.2]⟩
  exact information_le_phi_of_local_threshold hr (by norm_num) f i hi
    (localDeficit_threshold_middle2_interval hρ)

theorem mutualInformation_le_phi_middle2_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (487/500)) (f : BooleanFunction n) (i : Fin n)
    (hi : (589/800 : ℝ) ≤ |fourier (lift f) {i}|) :
    mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information_all]
  exact information_le_phi_middle2_large_singleton hρ f i hi

theorem localDeficit_threshold_middle3_interval {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (39/40)) :
    0 ≤ localDeficit ρ (18499/25000) := by
  apply localDeficit_nonneg_of_taylor 128 24 (R := 39/40)
    (L := 3465735902799729/5000000000000000) (by norm_num) (by norm_num) (by norm_num)
    hρ Certificate.P03.log_two_bounds.2
  exact Certificate.LocalTaylorMiddle3.polynomial_nonneg
    ⟨sq_nonneg ρ, pow_le_pow_left₀ hρ.1 hρ.2 2⟩

theorem information_le_phi_middle3_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (39/40)) (f : BooleanFunction n) (i : Fin n)
    (hi : (18499/25000 : ℝ) ≤ |fourier (lift f) {i}|) :
    information ρ f ≤ phi ρ := by
  have hr : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1, by linarith [hρ.2]⟩
  exact information_le_phi_of_local_threshold hr (by norm_num) f i hi
    (localDeficit_threshold_middle3_interval hρ)

theorem mutualInformation_le_phi_middle3_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (39/40)) (f : BooleanFunction n) (i : Fin n)
    (hi : (18499/25000 : ℝ) ≤ |fourier (lift f) {i}|) :
    mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information_all]
  exact information_le_phi_middle3_large_singleton hρ f i hi

end
end CK
