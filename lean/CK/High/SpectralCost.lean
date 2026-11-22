module

public import CK.High.CoordinateBudget
public import CK.High.Remainder
public import CK.High.ArcsineTransfer

/-! The exact scalar cost in the source uniform spectral gate. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

def spectralCost (γ t ρ a : ℝ) : ℝ :=
  (ρ*(profileHeight ρ a-arcsineRemainder (profileHeight ρ a)) +
    (Real.pi^2/4)*spectralDeltaTwo γ t ρ*influencePsi a/a +
    (Real.pi^2/4)*(spectralDeltaOne γ t ρ-spectralDeltaTwo γ t ρ)*a)/profileHeight ρ a

def spectralNumerator (γ t ρ : ℝ) : ℝ :=
  (Real.pi^2/4)*shiftedMultiplier γ t*ρ^2-
    γ*Certificate.arcsineSharpConstant*entropyRemainder ρ

theorem profileHeight_pos {ρ a : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (ha : 0 < a) :
    0 < profileHeight ρ a :=
  edgeHeight_pos (Profile.meanEntropy_pos ⟨by linarith [hρ.1],hρ.2⟩) (mul_pos hρ.1 ha)

theorem spectralCost_mul_height {γ t ρ a : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (ha : 0 < a) :
    spectralCost γ t ρ a*profileHeight ρ a =
      ρ*(profileHeight ρ a-arcsineRemainder (profileHeight ρ a)) +
        (Real.pi^2/4)*spectralDeltaTwo γ t ρ*influencePsi a/a +
        (Real.pi^2/4)*(spectralDeltaOne γ t ρ-spectralDeltaTwo γ t ρ)*a := by
  unfold spectralCost
  exact div_mul_cancel₀ _ (profileHeight_pos hρ ha).ne'

end
end CK
