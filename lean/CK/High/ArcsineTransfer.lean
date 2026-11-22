module

public import CK.High.SignedOperator
public import CK.Certificate.ArcsineSharp

/-! Spectral transfer from arcsine coordinates with the exact sharp
approximation constant proved in the certificate consumer. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem spectralQuadratic_smul {n : ℕ} (weights : Finset (Fin n) → ℝ)
    (c : ℝ) (g : Cube n → ℝ) :
    spectralQuadratic weights (fun x => c*g x)=c^2*spectralQuadratic weights g := by
  unfold spectralQuadratic
  simp only [fourier_smul,mul_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

/-- Complete STOC Walsh transfer with the `γ C_* J` approximation cost.
All weights may be negative provided their displayed shift is positive. -/
theorem spectral_arcsine_transfer {n : ℕ} (weights : Finset (Fin n) → ℝ) {γ : ℝ}
    (hγ : 0 ≤ γ) (hshift : ∀ S, 0 < weights S+γ)
    (g : Cube n → ℝ) (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) :
    (Real.pi^2/4)*spectralQuadratic (fun S => shiftedMultiplier γ (weights S)) g -
      γ*Certificate.arcsineSharpConstant*entropyRemainderMean g ≤
        spectralQuadratic weights (fun x => Real.arcsin (g x)) := by
  have h := walsh_spectral_square_completion weights γ hshift
    (fun x => Real.arcsin (g x)) (fun x => (Real.pi/2)*g x)
  rw [spectralQuadratic_smul] at h
  have he := mul_le_mul_of_nonneg_left (Certificate.arcsine_error_average g hg) hγ
  unfold shiftedMultiplier
  nlinarith only [h,he]

end
end CK
