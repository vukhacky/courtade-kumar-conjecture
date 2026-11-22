import CK

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace CK.Paper

/-- Shannon entropy in nats, written in terms of the atom masses. -/
noncomputable def H {A : Type*} [Fintype A] (q : A → ℝ) : ℝ :=
  -∑ u, q u * Real.log (q u)

/-- Mutual information of two finite-valued random variables. -/
noncomputable def I {Ω A B : Type*} [MeasurableSpace Ω] [Fintype A] [Fintype B]
    (μ : Measure Ω) (U : Ω → A) (V : Ω → B) : ℝ :=
  H (fun a => μ.real (U ⁻¹' {a})) + H (fun b => μ.real (V ⁻¹' {b})) -
    H (fun t : A × B => μ.real ((fun ω => (U ω, V ω)) ⁻¹' {t}))

noncomputable def Hb (p : ℝ) : ℝ := -(p * Real.log p) - (1-p) * Real.log (1-p)

theorem hb_eq (p : ℝ) : Hb p = Real.binEntropy p := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  unfold Hb Real.negMulLog
  ring

/-- The paper's main inequality and its attainment by every signed dictator. -/
theorem stoc_main {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 1 ≤ n) (X Z : Ω → (Fin n → Bool))
    (hX : Measurable X) (hZ : Measurable Z) (hXZ : IndepFun X Z μ)
    (hZind : iIndepFun (fun i ω => Z ω i) μ)
    {ρ : ℝ} (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (hUniform : ∀ x, μ.real (X ⁻¹' {x}) = (2 ^ n : ℝ)⁻¹)
    (hFlips : ∀ i, μ.real ((fun ω => Z ω i) ⁻¹' {true}) = (1-ρ)/2)
    (f : (Fin n → Bool) → Bool) :
    let Y : Ω → Fin n → Bool := fun ω i => Bool.xor (X ω i) (Z ω i)
    I μ (fun ω => f (X ω)) Y ≤ Real.log 2 - Hb ((1-ρ)/2) ∧
    ((∃ i : Fin n, ∃ negated : Bool, ∀ x, f x = Bool.xor (x i) negated) →
      I μ (fun ω => f (X ω)) Y = Real.log 2 - Hb ((1-ρ)/2)) := by
  have hu : ∀ x, CK.lawMass μ X x = (Fintype.card (CK.Cube n) : ℝ)⁻¹ := by
    intro x
    simpa only [CK.lawMass, CK.card_cube, Nat.cast_pow, Nat.cast_ofNat] using hUniform x
  have hf : ∀ i, CK.lawMass μ (fun ω => Z ω i) true = (1-ρ)/2 := hFlips
  simp only [hb_eq]
  constructor
  · exact CK.randomMutualInformation_le_binaryEntropy_independent_flips μ hn X Z hX hZ
      hXZ hZind ⟨hρ₀,hρ₁⟩ hu hf f
  · intro h
    rcases h with ⟨i, negated, hi⟩
    apply CK.randomMutualInformation_signedDictator μ X _
      hX (CK.measurable_xorCube X Z hX hZ) ⟨hρ₀,hρ₁⟩
        (CK.hasBSCJointLaw_of_independent_flips μ X Z hZ hXZ hZind hu hf)
    exact ⟨i, by
      cases negated
      · exact Or.inl (fun x => by rw [hi x]; cases x i <;> rfl)
      · exact Or.inr (fun x => by rw [hi x]; cases x i <;> rfl)⟩

end CK.Paper
