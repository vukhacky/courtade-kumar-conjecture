module

public import CK.Analysis.Production
public import CK.Functional.SignEntropy
public import CK.Certificate.LogBounds

/-! The Walsh form of spectral square completion and the exact
mean compensation in the high-correlation argument. Negative spectral
weights are allowed, with a strictly positive shifted denominator. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def entropyRemainder (t : ℝ) : ℝ := t^2*Real.log 2-phi t

def entropyRemainderMean {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  avg (fun x => entropyRemainder (g x))

def meanTransferCoefficient (Λ Γ ρ : ℝ) : ℝ :=
  Γ*(1/2-(1-ρ^2)*Real.log 2)-Λ*ρ^2

def spectralQuadratic {n : ℕ} (weights : Finset (Fin n) → ℝ)
    (g : Cube n → ℝ) : ℝ := ∑ S : Finset (Fin n), weights S * fourier g S ^ 2

theorem entropyRemainder_zero : entropyRemainder 0 = 0 := by simp [entropyRemainder,phi_zero]

theorem entropyRemainder_one : entropyRemainder 1 = 0 := by simp [entropyRemainder,phi_one]

theorem entropyRemainder_neg (t : ℝ) : entropyRemainder (-t) = entropyRemainder t := by
  simp [entropyRemainder,phi_neg]

theorem entropyRemainder_nonneg {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    0 ≤ entropyRemainder t := by
  have ha : |t| ∈ Set.Icc (0 : ℝ) 1 := ⟨abs_nonneg _, abs_le.mpr ht⟩
  have h := phi_mul_le_sq_mul ha (by norm_num : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1)
  rw [mul_one,phi_one,sq_abs] at h
  have habs : phi |t| = phi t := by
    rcases le_total 0 t with hp | hn
    · rw [abs_of_nonneg hp]
    · rw [abs_of_nonpos hn,phi_neg]
  rw [habs] at h
  exact sub_nonneg.mpr h

theorem entropyRemainder_le_quadratic {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    entropyRemainder t ≤ (Real.log 2-1/2)*t^2 := by
  have h := sq_div_two_le_phi ht
  dsimp [entropyRemainder]
  nlinarith only [h]

theorem entropyRemainderMean_nonneg {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) : 0 ≤ entropyRemainderMean g := by
  have h := avg_mono (fun x => entropyRemainder_nonneg (hg x))
  simpa only [avg_const,entropyRemainderMean] using h

theorem entropyRemainderMean_identity {n : ℕ} (g : Cube n → ℝ) :
    entropyRemainderMean g = variance g * Real.log 2 + entropyRemainder (avg g) -
      (avg (fun x => phi (g x)) - phi (avg g)) := by
  unfold entropyRemainderMean entropyRemainder
  rw [avg_sub,variance_eq_avg_sq_sub_sq]
  have he : (fun x => g x^2*Real.log 2) = fun x => Real.log 2*g x^2 := by
    funext x
    ring
  rw [he,avg_smul]
  ring

theorem entropyRemainderMean_noise {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    entropyRemainderMean (noise ρ (lift f)) =
      variance (noise ρ (lift f))*Real.log 2 + entropyRemainder (mean f) - information ρ f := by
  rw [entropyRemainderMean_identity,avg_noise]
  rfl

theorem scalar_spectral_square_completion {lam γ x y : ℝ} (hshift : 0 < lam+γ) :
    (γ*lam/(γ+lam))*y^2 ≤ lam*x^2+γ*(x-y)^2 := by
  have hid : lam*x^2+γ*(x-y)^2 - (γ*lam/(γ+lam))*y^2 =
      (lam+γ)*(x-γ*y/(lam+γ))^2 := by
    have hd : lam+γ ≠ 0 := ne_of_gt hshift
    have hd' : γ+lam ≠ 0 := by linarith
    field_simp
    ring
  have h := mul_nonneg hshift.le (sq_nonneg (x-γ*y/(lam+γ)))
  rw [← hid] at h
  linarith

/-- Finite Walsh spectral transfer. No eigenbasis or operator positivity
is assumed beyond the displayed, pointwise shifted-weight condition. -/
theorem walsh_spectral_square_completion {n : ℕ}
    (weights : Finset (Fin n) → ℝ) (γ : ℝ)
    (hshift : ∀ S, 0 < weights S+γ) (v w : Cube n → ℝ) :
    spectralQuadratic (fun S => γ*weights S/(γ+weights S)) w ≤
      spectralQuadratic weights v + γ*avg (fun x => (v x-w x)^2) := by
  rw [spectralQuadratic,spectralQuadratic,parseval,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  rw [fourier_sub]
  exact scalar_spectral_square_completion (hshift S)

/-- Mean compensation in STOC `ub:transfer`, for the actual information
gap of a fixed Boolean function, retaining its squared mean. -/
theorem variance_entropy_transfer {n : ℕ} {ρ Λ Γ : ℝ}
    (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) (hΓ : 0 < Γ)
    (f : BooleanFunction n) (hgap : 0 < informationGap ρ f)
    (hη : 0 ≤ meanTransferCoefficient Λ Γ ρ) :
    Λ*variance (noise ρ (lift f)) - Γ*entropyRemainderMean (noise ρ (lift f)) ≥
      Λ*ρ^2-Γ*entropyRemainder ρ+meanTransferCoefficient Λ Γ ρ*mean f^2 := by
  have hlog : 1/2 < Real.log 2 := by linarith [Certificate.log_two_coarse_bounds.1]
  have hρ2 : 0 < ρ^2 := sq_pos_of_pos hρ.1
  have hc : Λ-Γ*Real.log 2 ≤ 0 := by
    have hpositive := mul_pos hΓ (sub_pos.mpr hlog)
    have he : (Λ-Γ*Real.log 2)*ρ^2 < 0 := by
      dsimp [meanTransferCoefficient] at hη
      nlinarith only [hη,hpositive]
    nlinarith only [he,hρ2]
  have hv := variance_noise_boolean_le
    (show ρ ∈ Set.Icc (-1 : ℝ) 1 from ⟨by linarith [hρ.1],hρ.2.le⟩) f
  have hvmul := mul_le_mul_of_nonpos_left hv hc
  have hp := entropyRemainder_le_quadratic (mean_mem_Icc f)
  have hpmul := mul_le_mul_of_nonneg_left hp hΓ.le
  have hinfo : phi ρ < information ρ f := by
    dsimp [informationGap] at hgap
    linarith
  have himul := mul_lt_mul_of_pos_left hinfo hΓ
  rw [entropyRemainderMean_noise]
  dsimp [entropyRemainder] at hpmul
  dsimp [entropyRemainder,meanTransferCoefficient]
  nlinarith only [hvmul,hpmul,himul]

end
end CK
