module

public import CK.Basic.MutualInformation

/-! Exact finite Shannon semantics for the BSC model. The identities use
`Real.negMulLog_mul`, whose proof includes zero masses, so no division by
a possibly zero output probability is used. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

/-- The mass of a sign-valued bit with mean `t`, encoded by `Bool`. -/
def binaryMass (t : ℝ) (b : Bool) : ℝ := (1 + sign b * t) / 2

theorem binaryMass_false (t : ℝ) : binaryMass t false = (1-t)/2 := by
  simp [binaryMass, sub_eq_add_neg]

theorem binaryMass_true (t : ℝ) : binaryMass t true = (1+t)/2 := by
  simp [binaryMass]

theorem binaryMass_sum (t : ℝ) : ∑ b : Bool, binaryMass t b = 1 := by
  simp [binaryMass]
  ring

theorem binaryMass_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) (b : Bool) :
    0 ≤ binaryMass t b := by
  cases b <;> simp only [binaryMass_false, binaryMass_true] <;> linarith [ht.1, ht.2]

theorem entropyMass_eq_sum_negMulLog {α : Type*} [Fintype α] (p : α → ℝ) :
    entropyMass p = ∑ x, Real.negMulLog (p x) := by
  simp [entropyMass, Real.negMulLog, Finset.sum_neg_distrib]

theorem entropyMass_binaryMass (t : ℝ) :
    entropyMass (binaryMass t) = Real.binEntropy ((1-t)/2) := by
  rw [entropyMass_eq_sum_negMulLog,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [Fintype.sum_bool, binaryMass_false, binaryMass_true]
  rw [show 1 - (1-t)/2 = (1+t)/2 by ring]
  ac_rfl

theorem avg_binaryMass {n : ℕ} (g : Cube n → ℝ) (b : Bool) :
    avg (fun x => binaryMass (g x) b) = binaryMass (avg g) b := by
  have hf : (fun x => binaryMass (g x) b) =
      fun x => (1/2 : ℝ) + (sign b / 2) * g x := by
    funext x
    simp only [binaryMass]
    ring
  rw [hf, avg_add, avg_const, avg_smul]
  unfold binaryMass
  ring

/-- Exact posterior identity. The observation marginal is positive and
uniform, including the complete-noise and zero-noise endpoints. -/
theorem outputJoint_eq_posterior {n : ℕ} (ρ : ℝ) (f : BooleanFunction n)
    (b : Bool) (y : Cube n) :
    outputJoint ρ f b y = (Fintype.card (Cube n) : ℝ)⁻¹ *
      binaryMass (noise ρ (lift f) y) b := by
  classical
  let c : ℝ := (Fintype.card (Cube n) : ℝ)⁻¹
  have hterm (x : Cube n) :
      (if f x = b then jointMass ρ x y else 0) =
      (c/2) * bscKernel ρ y x + (c * sign b / 2) *
        (bscKernel ρ y x * lift f x) := by
    dsimp [jointMass, c, lift]
    rw [bscKernel_symm ρ x y]
    cases hb : b <;> cases hf : f x <;> simp [sign] <;> ring
  unfold outputJoint
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    bscKernel_sum]
  change c / 2 * 1 + c * sign b / 2 * noise ρ (lift f) y = _
  change c / 2 * 1 + c * sign b / 2 * noise ρ (lift f) y =
    c * binaryMass (noise ρ (lift f) y) b
  unfold binaryMass
  ring

theorem outputMarginal_eq_mean {n : ℕ} (ρ : ℝ) (f : BooleanFunction n)
    (b : Bool) : outputMarginal ρ f b = binaryMass (mean f) b := by
  unfold outputMarginal
  simp_rw [outputJoint_eq_posterior]
  rw [← Finset.mul_sum]
  change avg (fun y => binaryMass (noise ρ (lift f) y) b) = _
  rw [avg_binaryMass, avg_noise]
  rfl

theorem outputMarginal_nonneg {n : ℕ} (ρ : ℝ) (f : BooleanFunction n)
    (b : Bool) : 0 ≤ outputMarginal ρ f b := by
  rw [outputMarginal_eq_mean]
  exact binaryMass_nonneg (mean_mem_Icc f) b

theorem outputMarginal_total {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    ∑ b : Bool, outputMarginal ρ f b = 1 := by
  simp_rw [outputMarginal_eq_mean]
  exact binaryMass_sum _

theorem entropy_outputMarginal {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    entropyMass (outputMarginal ρ f) = Real.binEntropy ((1-mean f)/2) := by
  simp_rw [show outputMarginal ρ f = binaryMass (mean f) by
    funext b; exact outputMarginal_eq_mean ρ f b]
  exact entropyMass_binaryMass _

/-- Shannon's chain rule for the actual BSC output joint mass, expressed
without conditional probabilities on null events. -/
theorem entropy_outputJoint {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    entropyMass (fun z : Bool × Cube n => outputJoint ρ f z.1 z.2) =
      entropyMass (observationMarginal ρ f) +
        avg (fun y => Real.binEntropy ((1-noise ρ (lift f) y)/2)) := by
  let c : ℝ := (Fintype.card (Cube n) : ℝ)⁻¹
  have hsum (y : Cube n) :
      ∑ b : Bool, Real.negMulLog (outputJoint ρ f b y) =
        Real.negMulLog c + c * Real.binEntropy ((1-noise ρ (lift f) y)/2) := by
    simp_rw [outputJoint_eq_posterior, Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
      binaryMass_sum, one_mul]
    rw [← entropyMass_eq_sum_negMulLog, entropyMass_binaryMass]
  rw [entropyMass_eq_sum_negMulLog, Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [entropyMass_eq_sum_negMulLog]
  simp_rw [observationMarginal_eq_uniform]
  rfl

/-- Algebraic identity between the Shannon quantity defined from the joint
mass and the entropy/noise functional. Probability hypotheses are supplied
by the public bridge below and the mass nonnegativity theorems. -/
theorem mutualInformation_eq_information_all {n : ℕ} (ρ : ℝ)
    (f : BooleanFunction n) : mutualInformation ρ f = information ρ f := by
  rw [mutualInformation, entropy_outputMarginal, entropy_outputJoint,
    information_eq_entropy_difference]
  ring

/-- The Shannon bridge on the full binary symmetric channel parameter interval. -/
theorem mutualInformation_eq_information {n : ℕ} {ρ : ℝ}
    (_hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    mutualInformation ρ f = information ρ f :=
  mutualInformation_eq_information_all ρ f

theorem informationBridge : InformationBridgeStatement := by
  intro n ρ hρ f
  exact mutualInformation_eq_information hρ f

end
end CK
