module

public import CK.ProbabilitySpace
public import CK.Results.LowRange

@[expose] public section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
namespace CK
noncomputable section

/-- Low-correlation CK on any probability space, given its BSC joint law. -/
theorem randomMutualInformation_le_phi_low_range {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) (457/500)) (hBSC : HasBSCJointLaw μ X Y ρ)
    (f : BooleanFunction n) : randomMutualInformation μ (f ∘ X) Y ≤ phi ρ := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f]
  exact mutualInformation_le_phi_low_range hρ f

/-- Low-correlation CK from a uniform input and independent Bernoulli flips,
including the independence of the entire flip vector from the input. -/
theorem randomMutualInformation_low_independent_flips {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Z : Ω → Cube n)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hZind : iIndepFun (fun i ω => Z ω i) μ)
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) (457/500))
    (hXuniform : ∀ x, lawMass μ X x = (Fintype.card (Cube n) : ℝ)⁻¹)
    (hZflip : ∀ i, lawMass μ (fun ω => Z ω i) true = (1-ρ)/2) (f : BooleanFunction n) :
    randomMutualInformation μ (f ∘ X) (fun ω => xorCube (X ω) (Z ω)) ≤
      Real.log 2 - Real.binEntropy ((1-ρ)/2) := by
  rw [randomMutualInformation_independent_flips μ X Z hX hZ hXZ hZind hXuniform hZflip f]
  exact mutualInformation_le_phi_low_range hρ f

end
end CK
