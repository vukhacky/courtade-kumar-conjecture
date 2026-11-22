module

public import CK.Basic.Entropy

/-! Finite Shannon mutual information for the binary symmetric channel. See `CK.Basic.ShannonBridge` for the noise-functional identity and `CK.ProbabilitySpace` for its probability-space form. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

/-- Shannon entropy of a finite mass function, in nats. Probability
normalization and nonnegativity are supplied separately. -/
def entropyMass {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Joint law of a uniform input and its independently corrupted output. -/
def jointMass {n : ℕ} (ρ : ℝ) (x y : Cube n) : ℝ :=
  (Fintype.card (Cube n) : ℝ)⁻¹ * bscKernel ρ x y

/-- Pushforward of the input through the Boolean summary, retaining the
entire noisy observation. -/
def outputJoint {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) (b : Bool) (y : Cube n) : ℝ :=
  ∑ x, if f x = b then jointMass ρ x y else 0

def outputMarginal {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) (b : Bool) : ℝ :=
  ∑ y, outputJoint ρ f b y

def observationMarginal {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) (y : Cube n) : ℝ :=
  ∑ b, outputJoint ρ f b y

/-- The actual finite Shannon quantity `H(f(X))+H(Y)-H(f(X),Y)`. -/
def mutualInformation {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  entropyMass (outputMarginal ρ f) + entropyMass (observationMarginal ρ f) -
    entropyMass (fun z : Bool × Cube n => outputJoint ρ f z.1 z.2)

theorem zero_mul_log_zero : (0 : ℝ) * Real.log 0 = 0 := by simp

theorem jointMass_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (x y : Cube n) : 0 ≤ jointMass ρ x y :=
  mul_nonneg (inv_nonneg.mpr (le_of_lt (card_cube_pos n))) (bscKernel_nonneg hρ x y)

theorem jointMass_first_marginal {n : ℕ} (ρ : ℝ) (x : Cube n) :
    ∑ y, jointMass ρ x y = (Fintype.card (Cube n) : ℝ)⁻¹ := by
  simp only [jointMass, ← Finset.mul_sum, bscKernel_sum, mul_one]

theorem jointMass_second_marginal {n : ℕ} (ρ : ℝ) (y : Cube n) :
    ∑ x, jointMass ρ x y = (Fintype.card (Cube n) : ℝ)⁻¹ := by
  simp only [jointMass, bscKernel_symm ρ _ y, ← Finset.mul_sum, bscKernel_sum, mul_one]

theorem jointMass_total (n : ℕ) (ρ : ℝ) :
    ∑ x : Cube n, ∑ y, jointMass ρ x y = 1 := by
  simp [jointMass_first_marginal]

theorem outputJoint_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (f : BooleanFunction n) (b : Bool) (y : Cube n) : 0 ≤ outputJoint ρ f b y := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact jointMass_nonneg hρ x y
  · exact le_rfl

theorem observationMarginal_eq_uniform {n : ℕ} (ρ : ℝ) (f : BooleanFunction n)
    (y : Cube n) : observationMarginal ρ f y = (Fintype.card (Cube n) : ℝ)⁻¹ := by
  unfold observationMarginal outputJoint
  rw [Finset.sum_comm]
  simpa using jointMass_second_marginal ρ y

theorem outputJoint_total {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    ∑ b : Bool, ∑ y, outputJoint ρ f b y = 1 := by
  rw [Finset.sum_comm]
  change ∑ y, observationMarginal ρ f y = 1
  simp [observationMarginal_eq_uniform]

/-- The Shannon bridge proved by `CK.informationBridge`. -/
def InformationBridgeStatement : Prop :=
  ∀ n : ℕ, ∀ ρ : ℝ, ρ ∈ Set.Icc (0 : ℝ) 1 → ∀ f : BooleanFunction n,
    mutualInformation ρ f = information ρ f

end
end CK
