module

public import CK.Middle.TwoCoreEntropy
public import CK.Certificate.MomentEntropy
public import CK.Basic.ShannonBridge

/-! The P01 certificate connected to an actual Boolean-function Shannon
inequality, including the arbitrary mean and interaction coefficient. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem andPosteriorEntropy_eq_source (ρ : ℝ) :
    andPosteriorEntropy ρ = Certificate.andEntropyExpression ρ := by
  rw [andPosteriorEntropy_formula]
  unfold Certificate.andEntropyExpression Certificate.andEntropyExpressionP
  rw [show (1+ρ)/2 = 1-(1-ρ)/2 by ring]
  rw [← Real.binEntropy_one_sub ((1-(1-ρ)/2)^2)]
  rw [show 1-(1-(1-ρ)/2)^2 = 2*((1-ρ)/2)-((1-ρ)/2)^2 by ring]

theorem information_gap_eq_posterior {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) :
    phi ρ - information ρ f = posteriorEntropy ρ f + phi (mean f) - signEntropy ρ := by
  rw [information_eq_signEntropy_sub_posterior, signEntropy_eq_log_two_sub_phi,
    signEntropy_eq_log_two_sub_phi]
  ring

/-- Actual entropy gap dominates the full source polynomial on the P01 band.
Only monotonicity and the displayed coefficient interval remain as hypotheses. -/
theorem information_gap_ge_momentQ {m : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction (2+m))
    (hf : Monotone (lift f))
    (ha : fourier (lift f) {(0 : Fin 2).castAdd m} ∈
      Set.Icc (2/3 : ℝ) (76043/100000)) :
    (1-ρ^2) * Certificate.localMomentQ ρ
      (fourier (lift f) {(0 : Fin 2).castAdd m})
      (fourier (lift f) {(1 : Fin 2).castAdd m}) ≤ phi ρ - information ρ f := by
  let a := fourier (lift f) {(0 : Fin 2).castAdd m}
  let b := fourier (lift f) {(1 : Fin 2).castAdd m}
  let c := fourier (lift f) {(0 : Fin 2).castAdd m, (1 : Fin 2).castAdd m}
  have hρ01 : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hρ.1], by linarith [hρ.2]⟩
  have hb : 0 ≤ b := monotone_singleton_nonneg hf _
  have hab : a+b ≤ 1 := twoCore_singletons_sum_le_one f
  have hc : |c| ≤ b := twoCore_interaction_abs_le_second f hf
  have hexp (x : Cube 2) : noise ρ (coreAverage (lift f)) x =
      mean f + Certificate.twoCoreSignal ρ a b c x := by
    rw [noise_twoCore_expansion]
    dsimp [Certificate.twoCoreSignal, a, b, c]
    ring
  have hg (x : Cube 2) : mean f + Certificate.twoCoreSignal ρ a b c x ∈
      Set.Icc (-1 : ℝ) 1 := by
    rw [← hexp]
    exact noise_mem_Icc ⟨by linarith [hρ01.1], hρ01.2⟩ _
      (coreAverage_mem_Icc (lift f) (fun z => sign_mem_Icc (f z))) _
  have hscalar := Certificate.twoCore_entropy_moment_lower_bound hρ ha hb hab hc hg
  have hcore := posteriorEntropy_ge_twoCore hρ01 f hf
  simp_rw [hexp] at hcore
  have hJ := Certificate.and_entropy_rational hρ
  rw [← andPosteriorEntropy_eq_source] at hJ
  have hJmul := mul_le_mul_of_nonneg_left hJ (mul_nonneg (sq_nonneg ρ) hb)
  rw [information_gap_eq_posterior]
  change (1-ρ^2)*Certificate.localMomentQ ρ a b ≤ _
  change ρ^2*(a*signEntropy ρ+b*(2*andPosteriorEntropy ρ-signEntropy ρ)) +
    (1-ρ^2)*avg (fun x => signEntropy (mean f+Certificate.twoCoreSignal ρ a b c x)) ≤
      posteriorEntropy ρ f at hcore
  nlinarith

/-- Uniform positive gap on the entire P01 parameter polygon. -/
theorem information_gap_ge_moment_band {m : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction (2+m))
    (hf : Monotone (lift f))
    (ha : fourier (lift f) {(0 : Fin 2).castAdd m} ∈
      Set.Icc (2/3 : ℝ) (76043/100000))
    (hl : (64/25 : ℝ) ≤ 3*fourier (lift f) {(0 : Fin 2).castAdd m} +
      7*fourier (lift f) {(1 : Fin 2).castAdd m}) :
    (1-ρ^2)/1000 ≤ phi ρ-information ρ f := by
  have hpoly := Certificate.localMomentQ_lower_bound hρ ha (twoCore_singletons_sum_le_one f) hl
  have hlam : 0 ≤ 1-ρ^2 := by nlinarith [hρ.1, hρ.2]
  have h := mul_le_mul_of_nonneg_left hpoly hlam
  have ha' := information_gap_ge_momentQ hρ f hf ha
  nlinarith

/-- Shannon CK is strict for the actual monotone Boolean functions in P01. -/
theorem mutualInformation_lt_phi_moment_band {m : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction (2+m))
    (hf : Monotone (lift f))
    (ha : fourier (lift f) {(0 : Fin 2).castAdd m} ∈
      Set.Icc (2/3 : ℝ) (76043/100000))
    (hl : (64/25 : ℝ) ≤ 3*fourier (lift f) {(0 : Fin 2).castAdd m} +
      7*fourier (lift f) {(1 : Fin 2).castAdd m}) :
    mutualInformation ρ f < phi ρ := by
  rw [mutualInformation_eq_information_all]
  have h := information_gap_ge_moment_band hρ f hf ha hl
  have hlam : 0 < 1-ρ^2 := by nlinarith [hρ.1, hρ.2]
  linarith

end
end CK
