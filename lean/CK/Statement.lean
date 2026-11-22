module

public import CK.Basic.MutualInformation

/-! Statements of the Shannon inequality and attainment by signed dictators. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

/-- Courtade–Kumar for every Boolean function, with no balance assumption. -/
def CKAt (n : ℕ) (ρ : ℝ) : Prop :=
  ∀ f : BooleanFunction n, mutualInformation ρ f ≤ phi ρ

/-- Noise-functional form of the Courtade–Kumar inequality. -/
def FunctionalCKAt (n : ℕ) (ρ : ℝ) : Prop :=
  ∀ f : BooleanFunction n, information ρ f ≤ phi ρ

/-- Signed-dictator attainment, as stated in STOC theorem `jp:main`. -/
def DictatorAttainmentAt (n : ℕ) (ρ : ℝ) : Prop :=
  ∀ f : BooleanFunction n, IsSignedDictator f → mutualInformation ρ f = phi ρ

/-- Exact scope of STOC theorem `jp:main`: universal inequality and
attainment by signed dictators. -/
def MainStatement : Prop :=
  (∀ n : ℕ, 0 < n → ∀ ρ : ℝ, ρ ∈ Set.Icc (0 : ℝ) 1 → CKAt n ρ) ∧
  (∀ n : ℕ, 0 < n → ∀ ρ : ℝ, ρ ∈ Set.Icc (0 : ℝ) 1 → DictatorAttainmentAt n ρ)

def FunctionalMainStatement : Prop :=
  (∀ n : ℕ, 0 < n → ∀ ρ : ℝ, ρ ∈ Set.Icc (0 : ℝ) 1 → FunctionalCKAt n ρ) ∧
  (∀ n : ℕ, 0 < n → ∀ ρ : ℝ, ρ ∈ Set.Icc (0 : ℝ) 1 →
    ∀ f : BooleanFunction n, IsSignedDictator f → information ρ f = phi ρ)

theorem functional_ckAt_zero (n : ℕ) : FunctionalCKAt n 0 := by
  intro f
  simp [information_zero]

theorem functional_ckAt_one (n : ℕ) : FunctionalCKAt n 1 := information_one_le

/-- Every Boolean function ties at complete noise. -/
theorem functional_equality_zero {n : ℕ} (f : BooleanFunction n) : information 0 f = phi 0 := by
  simp [information_zero]

/-- Exactly balanced functions tie at zero noise. -/
theorem functional_equality_one {n : ℕ} (f : BooleanFunction n) :
    information 1 f = phi 1 ↔ Balanced f := information_one_eq_iff_balanced f

end
end CK
