module

public import CK.High.SpectralLedger

/-! The uniform spectral gate, with mean compensation, a common production
budget, arbitrary coefficient ceilings, and the actual gap derivative. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK
noncomputable section

theorem retainedSpectralCost_le_budget {n : ℕ} {γ t ρ z b : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (g : Cube n → ℝ)
    (hb : ∀ i ∈ spectralRetainedSet ρ z g, spectralCost γ t ρ |fourier g {i}| ≤ b) :
    retainedSpectralCost γ t ρ z g ≤ b*retainedHeightBudget (spectralRetainedSet ρ z g) ρ g := by
  unfold retainedSpectralCost retainedHeightBudget
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hw : 0 ≤ |fourier g {i}| *profileHeight ρ |fourier g {i}| :=
    mul_nonneg (abs_nonneg _) (profileHeight_nonneg hρ (abs_nonneg _))
  nlinarith only [mul_le_mul_of_nonneg_left (hb i hi) hw]

theorem spectral_gate_numerator_le {n : ℕ} {γ t ρ z b : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (f : BooleanFunction n) (hm : Monotone (lift f)) (hf : ∃ u v, f u ≠ f v)
    (hgap : 0 < informationGap ρ f)
    (hη : 0 ≤ meanTransferCoefficient ((Real.pi^2/4)*shiftedMultiplier γ t)
      (γ*Certificate.arcsineSharpConstant) ρ)
    (hb : ρ+(Real.pi^2/4)*spectralTau γ t ρ z ≤ b)
    (hcost : ∀ i ∈ spectralRetainedSet ρ z (lift f),
      spectralCost γ t ρ |fourier (lift f) {i}| ≤ b) :
    spectralNumerator γ t ρ ≤ b*(entropyProduction (noise ρ (lift f))/ρ) := by
  have hΓ : 0 < γ*Certificate.arcsineSharpConstant :=
    mul_pos ((le_max_left _ _).trans_lt hγ) Certificate.arcsineSharpConstant_pos
  have htransfer := variance_entropy_transfer hρ hΓ f hgap hη
  have hmean := mul_nonneg hη (sq_nonneg (mean f))
  have hledger := spectral_master_ledger hγ ht hρ hz f hm hf hgap
  have hcostSum := retainedSpectralCost_le_budget hρ (lift f) hcost
  have hbudget := (retainedHeightBudget_le_total hρ (spectralRetainedSet ρ z (lift f)) (lift f)).trans
    (profileHeight_common_budget hρ f hf hgap)
  have hmul := mul_le_mul_of_nonneg_right hb (sub_nonneg.mpr hbudget)
  unfold spectralNumerator
  nlinarith only [htransfer,hmean,hledger,hcostSum,hmul]

theorem spectral_gate_bound_positive {γ t ρ z b : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (hb : ρ+(Real.pi^2/4)*spectralTau γ t ρ z ≤ b) : 0 < b := by
  have hm := mul_nonneg (show 0 ≤ Real.pi^2/4 by positivity) (spectralTau_nonneg hγ hρ hz)
  linarith only [hm,hb,hρ.1]

/-- STOC `as:gate`. An upper bound on the scalar cost over a genuine
coefficient interval controls every retained coordinate, including an
empty retained set. -/
theorem uniform_spectral_gate {n : ℕ} {γ t ρ z b α : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (f : BooleanFunction n) (hm : Monotone (lift f)) (hf : ∃ u v, f u ≠ f v)
    (hgap : 0 < informationGap ρ f)
    (hη : 0 ≤ meanTransferCoefficient ((Real.pi^2/4)*shiftedMultiplier γ t)
      (γ*Certificate.arcsineSharpConstant) ρ)
    (hb : ρ+(Real.pi^2/4)*spectralTau γ t ρ z ≤ b)
    (hα : ∀ i, |fourier (lift f) {i}| ≤ α)
    (hcost : ∀ a ∈ Icc (profileCoefficient ρ z) α, spectralCost γ t ρ a ≤ b) :
    spectralNumerator γ t ρ/b ≤ entropyProduction (noise ρ (lift f))/ρ := by
  have h := spectral_gate_numerator_le hγ ht hρ hz f hm hf hgap hη hb
    (fun i hi => hcost _ ⟨spectralRetainedSet_mem.mp hi,hα i⟩)
  exact (div_le_iff₀ (spectral_gate_bound_positive hγ hρ hz hb)).mpr (by nlinarith only [h])

/-- Positive-gap derivative criterion. The function `f` is fixed during
differentiation; the retained set is used only in the pointwise bound. -/
theorem uniform_spectral_derivative {n : ℕ} {γ t ρ z b α : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hz : 0 < z)
    (f : BooleanFunction n) (hm : Monotone (lift f)) (hf : ∃ u v, f u ≠ f v)
    (hgap : 0 < informationGap ρ f)
    (hη : 0 ≤ meanTransferCoefficient ((Real.pi^2/4)*shiftedMultiplier γ t)
      (γ*Certificate.arcsineSharpConstant) ρ)
    (hb : ρ+(Real.pi^2/4)*spectralTau γ t ρ z ≤ b)
    (hα : ∀ i, |fourier (lift f) {i}| ≤ α)
    (hcost : ∀ a ∈ Icc (profileCoefficient ρ z) α, spectralCost γ t ρ a ≤ b)
    (hstrict : Real.artanh ρ*b < spectralNumerator γ t ρ) :
    0 < deriv (fun r => informationGap r f) ρ := by
  have h := uniform_spectral_gate hγ ht hρ hz f hm hf hgap hη hb hα hcost
  have hs : Real.artanh ρ < spectralNumerator γ t ρ/b :=
    (lt_div_iff₀ (spectral_gate_bound_positive hγ hρ hz hb)).mpr hstrict
  rw [(hasDerivAt_informationGap hρ f hf).deriv,
    phiSlope_eq_artanh ⟨by linarith [hρ.1],hρ.2⟩]
  linarith only [h,hs]

end
end CK
