module

public import CK.Statement
public import CK.Basic.BaseCases

/-! Closed canonical Shannon cases, proved independently of the complete
range assembly in `CK.Results.Main`. -/

@[expose] public section
set_option autoImplicit false
namespace CK

theorem ckAt_zero (n : ℕ) : CKAt n 0 := by
  intro f
  simp only [mutualInformation_zero, phi_zero, le_refl]

theorem ckAt_one (n : ℕ) : CKAt n 1 := mutualInformation_one_le

theorem ckAt_one_dimension {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : CKAt 1 ρ :=
  mutualInformation_one_dimension hρ

theorem dictatorAttainmentAt (n : ℕ) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    DictatorAttainmentAt n ρ := by
  intro f hf
  exact mutualInformation_signedDictator hρ hf

theorem equality_zero {n : ℕ} (f : BooleanFunction n) :
    mutualInformation 0 f = phi 0 := by
  simp only [mutualInformation_zero, phi_zero]

theorem equality_one {n : ℕ} (f : BooleanFunction n) :
    mutualInformation 1 f = phi 1 ↔ Balanced f :=
  mutualInformation_one_eq_iff_balanced f

end CK
