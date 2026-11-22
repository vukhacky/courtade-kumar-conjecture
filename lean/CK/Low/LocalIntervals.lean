module

public import CK.Low.LocalTaylor
public import CK.Certificate.LocalTaylorLow
public import CK.Certificate.LocalTaylorUpper
public import CK.Certificate.ClockPilotLogs
public import CK.Basic.ShannonBridge

/-! Two local entropy thresholds on whole intervals, proved by rational polynomial certificates and the analytic Taylor remainder theorem. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem localDeficit_threshold_low_interval {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (457/500)) :
    0 ≤ localDeficit ρ (69/100) := by
  apply localDeficit_nonneg_of_taylor 16 12 (R := 457/500)
    (L := 3465735902799729/5000000000000000) (by norm_num) (by norm_num) (by norm_num)
    hρ Certificate.P03.log_two_bounds.2
  exact Certificate.LocalTaylorLow.polynomial_nonneg
    ⟨sq_nonneg ρ, pow_le_pow_left₀ hρ.1 hρ.2 2⟩

theorem localDeficit_threshold_upper_interval {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (49/50)) :
    0 ≤ localDeficit ρ (76043/100000) := by
  apply localDeficit_nonneg_of_taylor 160 28 (R := 49/50)
    (L := 3465735902799729/5000000000000000) (by norm_num) (by norm_num) (by norm_num)
    hρ Certificate.P03.log_two_bounds.2
  exact Certificate.LocalTaylorUpper.polynomial_nonneg
    ⟨sq_nonneg ρ, pow_le_pow_left₀ hρ.1 hρ.2 2⟩

/-- All-dimensional CK for a large singleton throughout the low interval;
the original function's mean is retained. -/
theorem mutualInformation_le_phi_low_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (457/500)) (f : BooleanFunction n) (i : Fin n)
    (hi : (69/100 : ℝ) ≤ |fourier (lift f) {i}|) :
    mutualInformation ρ f ≤ phi ρ := by
  have hr : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1, by linarith [hρ.2]⟩
  rw [mutualInformation_eq_information hr]
  exact information_le_phi_of_local_threshold hr (by norm_num) f i hi
    (localDeficit_threshold_low_interval hρ)

/-- The upper-middle large-singleton branch, on the complete interval
from zero through `49/50`. -/
theorem mutualInformation_le_phi_upper_large_singleton {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (49/50)) (f : BooleanFunction n) (i : Fin n)
    (hi : (76043/100000 : ℝ) ≤ |fourier (lift f) {i}|) :
    mutualInformation ρ f ≤ phi ρ := by
  have hr : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨hρ.1, by linarith [hρ.2]⟩
  rw [mutualInformation_eq_information hr]
  exact information_le_phi_of_local_threshold hr (by norm_num) f i hi
    (localDeficit_threshold_upper_interval hρ)

end
end CK
