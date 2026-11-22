module

public import CK.Fourier.Laplacian
public import CK.Basic.BaseCases
public import CK.Analysis.BinaryEntropy
public import CK.Analysis.Barrier

/-! Entropy production and the gap derivative for a fixed Boolean function.
All differentiation occurs at strictly interior noise means. The endpoints
are handled by continuity and exact endpoint identities. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def entropyProduction {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  avg (fun x => laplacian g x * phiSlope (g x))

def conditionalEntropy {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  avg (fun x => Real.binEntropy ((1-noise ρ (lift f) x)/2))

def informationGap {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  information ρ f - phi ρ

theorem entropyProduction_eq_artanh {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) :
    entropyProduction g = avg (fun x => laplacian g x * Real.artanh (g x)) := by
  unfold entropyProduction
  congr 1
  funext x
  rw [phiSlope_eq_artanh (hg x)]

theorem entropyProduction_eq_edges {n : ℕ} (g : Cube n → ℝ) :
    entropyProduction g = ∑ i : Fin n, avg (fun x =>
      (g x - g (flipCoordinate i x)) *
        (phiSlope (g x) - phiSlope (g (flipCoordinate i x))) / 4) := by
  unfold entropyProduction laplacian
  simp_rw [Finset.sum_mul]
  rw [avg_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [avg_partial_mul i g (fun x => phiSlope (g x))]
  congr 1
  funext x
  unfold coordinatePartial
  ring

theorem information_eq_initial_sub_conditional {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    information ρ f = Real.binEntropy ((1-mean f)/2) - conditionalEntropy ρ f :=
  information_eq_entropy_difference ρ f

theorem hasDerivAt_information {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) :
    HasDerivAt (fun r => information r f) (entropyProduction (noise ρ (lift f)) / ρ) ρ := by
  have hr : ρ ≠ 0 := ne_of_gt hρ.1
  have hdom (x : Cube n) := noise_lift_mem_Ioo ⟨by linarith [hρ.1], hρ.2⟩ f hf x
  have hpoint (x : Cube n) :
      HasDerivAt (fun r => phi (noise r (lift f) x))
        (phiSlope (noise ρ (lift f) x) * (laplacian (noise ρ (lift f)) x / ρ)) ρ := by
    have h := (hasDerivAt_phi (hdom x)).comp ρ (hasDerivAt_noise_laplacian hr (lift f) x)
    exact h
  have hsum := ((HasDerivAt.fun_sum (u := Finset.univ) (fun x _ => hpoint x)).const_mul
    ((Fintype.card (Cube n) : ℝ)⁻¹)).sub_const (phi (mean f))
  change HasDerivAt (fun r => information r f)
    ((Fintype.card (Cube n) : ℝ)⁻¹ *
      ∑ x, phiSlope (noise ρ (lift f) x) * (laplacian (noise ρ (lift f)) x / ρ)) ρ at hsum
  apply hsum.congr_deriv
  unfold entropyProduction avg
  simp only [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  ring

theorem hasDerivAt_conditionalEntropy {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) :
    HasDerivAt (fun r => conditionalEntropy r f)
      (-(entropyProduction (noise ρ (lift f)) / ρ)) ρ := by
  have hfun : (fun r => conditionalEntropy r f) =
      fun r => Real.binEntropy ((1-mean f)/2) - information r f := by
    funext r
    rw [information_eq_initial_sub_conditional]
    ring
  rw [hfun]
  exact (hasDerivAt_information hρ f hf).const_sub _

theorem hasDerivAt_informationGap {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) :
    HasDerivAt (fun r => informationGap r f)
      (entropyProduction (noise ρ (lift f)) / ρ - phiSlope ρ) ρ :=
  (hasDerivAt_information hρ f hf).sub (hasDerivAt_phi ⟨by linarith [hρ.1], hρ.2⟩)

theorem gap_derivative_identity {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) :
    ρ * deriv (fun r => informationGap r f) ρ =
      entropyProduction (noise ρ (lift f)) - ρ * Real.artanh ρ := by
  rw [(hasDerivAt_informationGap hρ f hf).deriv,
    phiSlope_eq_artanh ⟨by linarith [hρ.1], hρ.2⟩]
  field_simp [ne_of_gt hρ.1]

theorem conditionalEntropy_derivative_identity {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) :
    -ρ * deriv (fun r => conditionalEntropy r f) ρ =
      entropyProduction (noise ρ (lift f)) := by
  rw [(hasDerivAt_conditionalEntropy hρ f hf).deriv]
  field_simp [ne_of_gt hρ.1]

theorem continuous_information {n : ℕ} (f : BooleanFunction n) :
    Continuous (fun ρ => information ρ f) := by
  unfold information avg
  apply Continuous.sub
  · apply Continuous.const_mul
    apply continuous_finsetSum
    intro x _
    exact continuous_phi.comp (continuous_noise (lift f) x)
  · exact continuous_const

theorem continuous_informationGap {n : ℕ} (f : BooleanFunction n) :
    Continuous (fun ρ => informationGap ρ f) :=
  (continuous_information f).sub continuous_phi

theorem informationGap_zero {n : ℕ} (f : BooleanFunction n) : informationGap 0 f = 0 := by
  simp [informationGap, information_zero]

theorem informationGap_one {n : ℕ} (f : BooleanFunction n) :
    informationGap 1 f = -phi (mean f) := by
  rw [informationGap, information_one, phi_one]
  unfold phi
  ring

theorem informationGap_one_nonpos {n : ℕ} (f : BooleanFunction n) :
    informationGap 1 f ≤ 0 := by
  rw [informationGap_one]
  exact neg_nonpos.mpr (phi_nonneg _)

theorem entropyProduction_nonneg {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Ioo (-1 : ℝ) 1) : 0 ≤ entropyProduction g := by
  rw [entropyProduction_eq_edges]
  apply Finset.sum_nonneg
  intro i _
  have hp (x : Cube n) : 0 ≤ (g x - g (flipCoordinate i x)) *
      (phiSlope (g x) - phiSlope (g (flipCoordinate i x))) / 4 := by
    rw [phiSlope_eq_artanh (hg x), phiSlope_eq_artanh (hg (flipCoordinate i x))]
    apply div_nonneg _ (by norm_num)
    by_cases hxy : g (flipCoordinate i x) ≤ g x
    · exact mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr
        (Real.strictMonoOn_artanh.monotoneOn (hg (flipCoordinate i x)) (hg x) hxy))
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (le_of_not_ge hxy))
        (sub_nonpos.mpr (Real.strictMonoOn_artanh.monotoneOn (hg x)
          (hg (flipCoordinate i x)) (le_of_not_ge hxy)))
  have h := avg_mono hp
  simpa only [avg_const] using h

/-- The terminal-range criterion reduces the entropy comparison to a sign condition on entropy production. -/
theorem information_le_of_positive_gap_production {n : ℕ} {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v)
    (hprod : ∀ ρ ∈ Set.Ioo a 1, 0 < informationGap ρ f →
      ρ * Real.artanh ρ ≤ entropyProduction (noise ρ (lift f))) :
    ∀ ρ ∈ Set.Icc a 1, information ρ f ≤ phi ρ := by
  have hgap := positive_gap_barrier ha1 (continuous_informationGap f).continuousOn
    (G := fun r => informationGap r f)
    (fun r hr => (hasDerivAt_informationGap ⟨lt_of_le_of_lt ha0 hr.1, hr.2⟩ f hf).differentiableAt.differentiableWithinAt)
    (informationGap_one_nonpos f)
    (fun r hr hpos => by
      have hr01 : r ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_lt ha0 hr.1, hr.2⟩
      have hid := gap_derivative_identity hr01 f hf
      have hp := hprod r hr hpos
      have hmul : 0 ≤ r * deriv (fun s => informationGap s f) r := by linarith
      exact nonneg_of_mul_nonneg_right hmul hr01.1)
  intro r hr
  exact sub_nonpos.mp (hgap r hr)

end
end CK
