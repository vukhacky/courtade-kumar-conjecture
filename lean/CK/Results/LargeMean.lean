module

public import CK.Basic.ShannonBridge
public import CK.Low.Contraction

/-! The all-dimensional large-mean branch of CK, for genuine finite
Shannon mutual information. Entropy contraction and the scalar threshold
are proved in the imported project modules. -/

@[expose] public section
set_option autoImplicit false
namespace CK

theorem mutualInformation_le_phi_of_large_mean {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n)
    (hmean : (61 / 100 : ℝ) ≤ |mean f|) : mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information hρ]
  exact information_le_phi_of_large_mean hρ f hmean

end CK
