module

public import CK.Basic.ShannonBridge
public import CK.Basic.NoiseExtras

/-! Constants, signed dictators, endpoints, and every one-dimensional
Boolean function, for the actual finite Shannon mutual information. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem information_const (n : ℕ) (ρ : ℝ) (b : Bool) :
    information ρ (fun _ : Cube n => b) = 0 := by
  change (avg (fun x => phi (noise ρ (fun _ : Cube n => sign b) x))) -
    phi (avg (fun _ : Cube n => sign b)) = 0
  simp [noise_const]

theorem information_coordinate {n : ℕ} (ρ : ℝ) (i : Fin n) :
    information ρ (fun x : Cube n => x i) = phi ρ := by
  unfold information
  rw [mean_coordinate, phi_zero, sub_zero]
  have hp (x : Cube n) : phi (noise ρ (lift (fun y : Cube n => y i)) x) = phi ρ := by
    change phi (noise ρ (fun y : Cube n => sign (y i)) x) = phi ρ
    rw [noise_coordinate]
    cases hx : x i <;> simp [sign, phi_neg]
  simp_rw [hp]
  exact avg_const n _

theorem information_signedDictator {n : ℕ} (ρ : ℝ) {f : BooleanFunction n}
    (hf : IsSignedDictator f) : information ρ f = phi ρ := by
  rcases hf with ⟨i, hi | hi⟩
  · rw [show f = (fun x => x i) from funext hi]
    exact information_coordinate ρ i
  · rw [show f = (fun x => !(x i)) from funext hi, information_complement]
    exact information_coordinate ρ i

theorem mutualInformation_const (n : ℕ) (ρ : ℝ) (b : Bool) :
    mutualInformation ρ (fun _ : Cube n => b) = 0 := by
  rw [mutualInformation_eq_information_all, information_const]

theorem mutualInformation_signedDictator {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) {f : BooleanFunction n}
    (hf : IsSignedDictator f) : mutualInformation ρ f = phi ρ := by
  rw [mutualInformation_eq_information hρ]
  exact information_signedDictator ρ hf

theorem mutualInformation_zero {n : ℕ} (f : BooleanFunction n) :
    mutualInformation 0 f = 0 := by
  rw [mutualInformation_eq_information_all, information_zero]

theorem mutualInformation_one {n : ℕ} (f : BooleanFunction n) :
    mutualInformation 1 f = Real.binEntropy ((1-mean f)/2) := by
  rw [mutualInformation_eq_information_all, information_one]

theorem mutualInformation_one_le {n : ℕ} (f : BooleanFunction n) :
    mutualInformation 1 f ≤ phi 1 := by
  rw [mutualInformation_eq_information_all]
  exact information_one_le f

theorem mutualInformation_one_eq_iff_balanced {n : ℕ} (f : BooleanFunction n) :
    mutualInformation 1 f = phi 1 ↔ Balanced f := by
  rw [mutualInformation_eq_information_all]
  exact information_one_eq_iff_balanced f

theorem booleanFunction_one_cases (f : BooleanFunction 1) :
    f = (fun _ => false) ∨ f = (fun _ => true) ∨
      f = (fun x => x 0) ∨ f = (fun x => !(x 0)) := by
  have hx (x : Cube 1) : x = fun _ => x 0 := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    rw [hi]
  have hpoint (x : Cube 1) : f x =
      if x 0 then f (fun _ => true) else f (fun _ => false) := by
    conv_lhs => rw [hx x]
    cases h : x 0 <;> simp
  cases hF : f (fun _ => false) <;> cases hT : f (fun _ => true)
  · left
    funext x
    rw [hpoint]
    simp [hF, hT]
  · right; right; left
    funext x
    rw [hpoint]
    simp [hF, hT]
  · right; right; right
    funext x
    rw [hpoint]
    simp [hF, hT]
  · right; left
    funext x
    rw [hpoint]
    simp [hF, hT]

theorem information_one_dimension (ρ : ℝ) (f : BooleanFunction 1) :
    information ρ f ≤ phi ρ := by
  rcases booleanFunction_one_cases f with hf | hf | hf | hf
  · rw [hf, information_const]
    exact phi_nonneg ρ
  · rw [hf, information_const]
    exact phi_nonneg ρ
  · rw [hf, information_coordinate]
  · rw [hf, information_complement, information_coordinate]

theorem mutualInformation_one_dimension {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction 1) : mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information hρ]
  exact information_one_dimension ρ f

end
end CK
