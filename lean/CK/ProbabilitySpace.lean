module

public import CK.Basic.BaseCases
public import CK.Results.LargeMean
public import Mathlib.Probability.Independence.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-! Finite Shannon entropy of random variables on an arbitrary probability
space, transport through the full joint law, and an independent bit-flip
constructor. `IsProbabilityMeasure` ensures every atom has finite mass;
no totalized value `ENNReal.toReal ∞` is used as a probability. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory
namespace CK
noncomputable section

def lawMass {Ω α : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → α) (a : α) : ℝ :=
  μ.real (X ⁻¹' {a})

def randomEntropy {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (μ : Measure Ω) (X : Ω → α) : ℝ := entropyMass (lawMass μ X)

/-- Actual finite Shannon mutual information of arbitrary random variables. -/
def randomMutualInformation {Ω α β : Type*} [MeasurableSpace Ω] [Fintype α] [Fintype β]
    (μ : Measure Ω) (X : Ω → α) (Y : Ω → β) : ℝ :=
  randomEntropy μ X + randomEntropy μ Y - randomEntropy μ (fun ω => (X ω, Y ω))

theorem lawMass_nonneg {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → α) (a : α) : 0 ≤ lawMass μ X a := ENNReal.toReal_nonneg

theorem lawMass_finite {Ω α : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (a : α) :
    μ (X ⁻¹' {a}) ≠ ∞ := measure_ne_top _ _

theorem lawMass_total {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Fintype α] [MeasurableSingletonClass α] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → α) (hX : Measurable X) : ∑ a, lawMass μ X a = 1 := by
  have h := sum_measureReal_preimage_singleton (μ := μ) Finset.univ
    (fun a _ => (measurableSet_singleton a).preimage hX)
  simpa only [lawMass, Finset.coe_univ, Set.preimage_univ, probReal_univ] using h

theorem lawMass_comp {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [Fintype α] [MeasurableSingletonClass α] [DecidableEq β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (hX : Measurable X)
    (f : α → β) (b : β) :
    lawMass μ (f ∘ X) b = ∑ a, if f a = b then lawMass μ X a else 0 := by
  classical
  let s : Finset α := Finset.univ.filter (fun a => f a = b)
  have h := sum_measureReal_preimage_singleton (μ := μ) s
    (fun a _ => (measurableSet_singleton a).preimage hX)
  have heq : (f ∘ X) ⁻¹' {b} = X ⁻¹' (s : Set α) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply,
      Finset.mem_coe, s, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lawMass
  rw [heq, ← h]
  simp only [s, Finset.sum_filter]

theorem lawMass_fst {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [Fintype α] [Fintype β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) (a : α) :
    lawMass μ X a = ∑ b, lawMass μ (fun ω => (X ω, Y ω)) (a,b) := by
  classical
  have h := lawMass_comp μ (fun ω => (X ω, Y ω)) (hX.prodMk hY) Prod.fst a
  simp only [Function.comp_def, Fintype.sum_prod_type] at h
  rw [Finset.sum_comm] at h
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using h

theorem lawMass_snd {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [Fintype α] [Fintype β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) (b : β) :
    lawMass μ Y b = ∑ a, lawMass μ (fun ω => (X ω, Y ω)) (a,b) := by
  classical
  have h := lawMass_comp μ (fun ω => (X ω, Y ω)) (hX.prodMk hY) Prod.snd b
  simpa only [Function.comp_def, Fintype.sum_prod_type, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] using h

/-- Full joint law, rather than pairwise correlation data. -/
def HasBSCJointLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (X Y : Ω → Cube n) (ρ : ℝ) : Prop :=
  ∀ x y, lawMass μ (fun ω => (X ω, Y ω)) (x,y) = jointMass ρ x y

theorem lawMass_outputJoint {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hBSC : HasBSCJointLaw μ X Y ρ)
    (f : BooleanFunction n) (b : Bool) (y : Cube n) :
    lawMass μ (fun ω => (f (X ω), Y ω)) (b,y) = outputJoint ρ f b y := by
  dsimp only [HasBSCJointLaw] at hBSC
  have h := lawMass_comp μ (fun ω => (X ω, Y ω)) (hX.prodMk hY)
    (fun p : Cube n × Cube n => (f p.1, p.2)) (b,y)
  simp only [Function.comp_def, Fintype.sum_prod_type, Prod.mk.injEq, ite_and,
    hBSC, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h
  exact h

theorem randomMutualInformation_eq_canonical {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hBSC : HasBSCJointLaw μ X Y ρ)
    (f : BooleanFunction n) :
    randomMutualInformation μ (f ∘ X) Y = mutualInformation ρ f := by
  have hf : Measurable (f ∘ X) := (measurable_of_countable f).comp hX
  have hJ : lawMass μ (fun ω => ((f ∘ X) ω, Y ω)) =
      fun p : Bool × Cube n => outputJoint ρ f p.1 p.2 := by
    funext p
    exact lawMass_outputJoint μ X Y hX hY hBSC f p.1 p.2
  have hA : lawMass μ (f ∘ X) = outputMarginal ρ f := by
    funext b
    rw [lawMass_fst μ (f ∘ X) Y hf hY, hJ]
    rfl
  have hB : lawMass μ Y = observationMarginal ρ f := by
    funext y
    rw [lawMass_snd μ (f ∘ X) Y hf hY, hJ]
    rfl
  simp only [randomMutualInformation, randomEntropy, hA, hB, hJ, mutualInformation]

theorem randomMutualInformation_eq_information {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hBSC : HasBSCJointLaw μ X Y ρ)
    (f : BooleanFunction n) :
    randomMutualInformation μ (f ∘ X) Y = information ρ f := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f,
    mutualInformation_eq_information_all]

theorem lawMass_indepFun {Ω α β : Type*} [MeasurableSpace Ω]
    [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (μ : Measure Ω) (X : Ω → α) (Z : Ω → β) (hXZ : IndepFun X Z μ) (x : α) (z : β) :
    lawMass μ (fun ω => (X ω, Z ω)) (x,z) = lawMass μ X x * lawMass μ Z z := by
  have heq : (fun ω => (X ω, Z ω)) ⁻¹' {(x,z)} = X ⁻¹' {x} ∩ Z ⁻¹' {z} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_inter_iff]
  simp only [lawMass, Measure.real, heq,
    hXZ.measure_inter_preimage_eq_mul {x} {z} (measurableSet_singleton _) (measurableSet_singleton _),
    ENNReal.toReal_mul]

theorem lawMass_iIndepFun {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (Z : Ω → Cube n) (hZ : iIndepFun (fun i ω => Z ω i) μ) (z : Cube n) :
    lawMass μ Z z = ∏ i : Fin n, lawMass μ (fun ω => Z ω i) (z i) := by
  have heq : Z ⁻¹' {z} = ⋂ i ∈ (Finset.univ : Finset (Fin n)), (fun ω => Z ω i) ⁻¹' {z i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_univ,
      forall_const, funext_iff]
  have h := hZ.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun i => {z i}) (fun _ _ => measurableSet_singleton _)
  simp only [lawMass, Measure.real, heq, h, ENNReal.toReal_prod]

def xorCube {n : ℕ} (x z : Cube n) : Cube n := fun i => Bool.xor (x i) (z i)

theorem xorCube_involutive {n : ℕ} (x : Cube n) : Function.Involutive (xorCube x) := by
  intro y
  funext i
  change Bool.xor (x i) (Bool.xor (x i) (y i)) = y i
  cases x i <;> cases y i <;> rfl

theorem xorCube_eq_iff {n : ℕ} (x z y : Cube n) : xorCube x z = y ↔ z = xorCube x y := by
  constructor
  · intro h
    rw [← h, xorCube_involutive x z]
  · intro h
    rw [h, xorCube_involutive x y]

theorem measurable_xorCube {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (X Z : Ω → Cube n) (hX : Measurable X) (hZ : Measurable Z) :
    Measurable (fun ω => xorCube (X ω) (Z ω)) :=
  (measurable_of_countable (fun p : Cube n × Cube n => xorCube p.1 p.2)).comp (hX.prodMk hZ)

theorem bitKernel_xor (ρ : ℝ) (a b : Bool) : bitKernel ρ false (Bool.xor a b) = bitKernel ρ a b := by
  cases a <;> cases b <;> rfl

theorem lawMass_bool_of_flip_probability {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Bool) (hZ : Measurable Z)
    (ρ : ℝ) (hflip : lawMass μ Z true = (1-ρ)/2) (b : Bool) :
    lawMass μ Z b = bitKernel ρ false b := by
  cases b
  · have h := lawMass_total μ Z hZ
    simp only [Fintype.sum_bool] at h
    simp only [bitKernel, ↓reduceIte]
    linarith
  · simpa only [bitKernel, Bool.false_eq_true, ↓reduceIte] using hflip

/-- Independent Bernoulli flips, independent of the uniform input, produce
the full BSC joint law. Degenerate flip probabilities are allowed. -/
theorem hasBSCJointLaw_of_independent_flips {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Z : Ω → Cube n)
    (hZmeas : Measurable Z) (hXZ : IndepFun X Z μ)
    (hZind : iIndepFun (fun i ω => Z ω i) μ)
    {ρ : ℝ} (hXuniform : ∀ x, lawMass μ X x = (Fintype.card (Cube n) : ℝ)⁻¹)
    (hZflip : ∀ i, lawMass μ (fun ω => Z ω i) true = (1-ρ)/2) :
    HasBSCJointLaw μ X (fun ω => xorCube (X ω) (Z ω)) ρ := by
  intro x y
  have heq : (fun ω => (X ω, xorCube (X ω) (Z ω))) ⁻¹' {(x,y)} =
      (fun ω => (X ω, Z ω)) ⁻¹' {(x, xorCube x y)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨hx, hy⟩
      refine ⟨hx, ?_⟩
      rw [hx] at hy
      exact (xorCube_eq_iff x (Z ω) y).mp hy
    · rintro ⟨hx, hz⟩
      refine ⟨hx, ?_⟩
      rw [hx]
      exact (xorCube_eq_iff x (Z ω) y).mpr hz
  change μ.real _ = _
  rw [heq]
  change lawMass μ (fun ω => (X ω, Z ω)) (x, xorCube x y) = _
  rw [lawMass_indepFun μ X Z hXZ, hXuniform, lawMass_iIndepFun μ Z hZind]
  unfold jointMass bscKernel
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [lawMass_bool_of_flip_probability μ (fun ω => Z ω i)
    ((measurable_pi_apply i).comp hZmeas) ρ (hZflip i)]
  exact bitKernel_xor ρ (x i) (y i)

theorem randomMutualInformation_independent_flips {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Z : Ω → Cube n)
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hZind : iIndepFun (fun i ω => Z ω i) μ)
    {ρ : ℝ} (hXuniform : ∀ x, lawMass μ X x = (Fintype.card (Cube n) : ℝ)⁻¹)
    (hZflip : ∀ i, lawMass μ (fun ω => Z ω i) true = (1-ρ)/2) (f : BooleanFunction n) :
    randomMutualInformation μ (f ∘ X) (fun ω => xorCube (X ω) (Z ω)) = mutualInformation ρ f :=
  randomMutualInformation_eq_canonical μ X _ hX (measurable_xorCube X Z hX hZ)
    (hasBSCJointLaw_of_independent_flips μ X Z hZ hXZ hZind hXuniform hZflip) f

theorem input_uniform_of_hasBSCJointLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hBSC : HasBSCJointLaw μ X Y ρ)
    (x : Cube n) : lawMass μ X x = (Fintype.card (Cube n) : ℝ)⁻¹ := by
  dsimp only [HasBSCJointLaw] at hBSC
  rw [lawMass_fst μ X Y hX hY]
  simp only [hBSC, jointMass_first_marginal]

theorem randomMutualInformation_const {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hBSC : HasBSCJointLaw μ X Y ρ)
    (b : Bool) : randomMutualInformation μ (fun _ => b) Y = 0 := by
  have h := randomMutualInformation_eq_canonical μ X Y hX hY hBSC (fun _ => b)
  simpa only [Function.comp_def, mutualInformation_const] using h

theorem randomMutualInformation_signedDictator {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hBSC : HasBSCJointLaw μ X Y ρ) {f : BooleanFunction n} (hf : IsSignedDictator f) :
    randomMutualInformation μ (f ∘ X) Y = phi ρ := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f]
  exact mutualInformation_signedDictator hρ hf

theorem randomMutualInformation_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) (hBSC : HasBSCJointLaw μ X Y 0)
    (f : BooleanFunction n) : randomMutualInformation μ (f ∘ X) Y = 0 := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f, mutualInformation_zero]

theorem randomMutualInformation_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) (hBSC : HasBSCJointLaw μ X Y 1)
    (f : BooleanFunction n) :
    randomMutualInformation μ (f ∘ X) Y = Real.binEntropy ((1-mean f)/2) := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f, mutualInformation_one]

theorem randomMutualInformation_one_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) (hBSC : HasBSCJointLaw μ X Y 1)
    (f : BooleanFunction n) : randomMutualInformation μ (f ∘ X) Y ≤ phi 1 := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f]
  exact mutualInformation_one_le f

theorem randomMutualInformation_one_eq_iff_balanced {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) (hBSC : HasBSCJointLaw μ X Y 1)
    (f : BooleanFunction n) : randomMutualInformation μ (f ∘ X) Y = phi 1 ↔ Balanced f := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f]
  exact mutualInformation_one_eq_iff_balanced f

theorem randomMutualInformation_one_dimension {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → Cube 1)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hBSC : HasBSCJointLaw μ X Y ρ) (f : BooleanFunction 1) :
    randomMutualInformation μ (f ∘ X) Y ≤ phi ρ := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f]
  exact mutualInformation_one_dimension hρ f

theorem randomMutualInformation_le_phi_of_large_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ} (X Y : Ω → Cube n)
    (hX : Measurable X) (hY : Measurable Y) {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hBSC : HasBSCJointLaw μ X Y ρ) (f : BooleanFunction n)
    (hmean : (61/100 : ℝ) ≤ |mean f|) : randomMutualInformation μ (f ∘ X) Y ≤ phi ρ := by
  rw [randomMutualInformation_eq_canonical μ X Y hX hY hBSC f]
  exact mutualInformation_le_phi_of_large_mean hρ f hmean

end
end CK
