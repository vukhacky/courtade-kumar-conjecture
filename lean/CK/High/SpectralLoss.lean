module

public import CK.High.SignedOperator

/-! Degreewise loss estimates for the signed Walsh multiplier. These are
finite exact inequalities for every cube dimension and every retained set. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def spectralDeltaTwo (γ t ρ : ℝ) : ℝ :=
  (shiftedMultiplier γ t-shiftedMultiplier γ 2)*ρ^4

def spectralDeltaOne (γ t ρ : ℝ) : ℝ :=
  (shiftedMultiplier γ t-shiftedMultiplier γ 1)*ρ^2

def spectralDeltaOutside (γ t ρ : ℝ) : ℝ :=
  (shiftedMultiplier γ t-shiftedMultiplier γ (t-Real.exp (2*t-3)/2))*ρ^2

theorem spectralDeltaTwo_nonneg {γ t ρ : ℝ} (hγ : 0 < γ) (ht : (2 : ℝ) ≤ t) :
    0 ≤ spectralDeltaTwo γ t ρ := by
  apply mul_nonneg
  · exact sub_nonneg.mpr (shiftedMultiplier_monotone (by linarith) ht)
  · positivity

theorem spectralDeltaOne_ge_two {γ t ρ : ℝ} (hγ : 0 < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : spectralDeltaTwo γ t ρ ≤ spectralDeltaOne γ t ρ := by
  have h12 : shiftedMultiplier γ 1 ≤ shiftedMultiplier γ 2 := shiftedMultiplier_monotone (by linarith) (by norm_num)
  have h2t : shiftedMultiplier γ 2 ≤ shiftedMultiplier γ t := shiftedMultiplier_monotone (by linarith) ht
  have hp : ρ^4 ≤ ρ^2 := pow_le_pow_of_le_one hρ.1 hρ.2 (by norm_num)
  have hm1 := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr h2t)
  have hm2 := mul_le_mul_of_nonneg_right h12 (sq_nonneg ρ)
  unfold spectralDeltaTwo spectralDeltaOne
  nlinarith only [hm1,hm2]

theorem spectralDeltaOutside_nonneg {γ t ρ : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) : 0 ≤ spectralDeltaOutside γ t ρ := by
  have ho : 0 < γ+(t-Real.exp (2*t-3)/2) := by linarith [(le_max_right _ _).trans_lt hγ]
  have ht : t-Real.exp (2*t-3)/2 ≤ t := by linarith [(Real.exp_pos (2*t-3)).le]
  exact mul_nonneg (sub_nonneg.mpr (shiftedMultiplier_monotone ho ht)) (sq_nonneg ρ)

theorem inside_mode_loss_le {γ t ρ : ℝ} (hγ : 0 < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) {j : ℕ} (hj : 2 ≤ j) :
    (shiftedMultiplier γ t-shiftedMultiplier γ (j : ℝ))*ρ^(2*j) ≤ spectralDeltaTwo γ t ρ := by
  have hjR : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have h2j : shiftedMultiplier γ 2 ≤ shiftedMultiplier γ (j : ℝ) :=
    shiftedMultiplier_monotone (by linarith) hjR
  have h2t : shiftedMultiplier γ 2 ≤ shiftedMultiplier γ t :=
    shiftedMultiplier_monotone (by linarith) ht
  have hp : ρ^(2*j) ≤ ρ^4 := pow_le_pow_of_le_one hρ.1 hρ.2 (by omega)
  have hm1 := mul_le_mul_of_nonneg_right h2j (pow_nonneg hρ.1 (2*j))
  have hm2 := mul_le_mul_of_nonneg_left hp (sub_nonneg.mpr h2t)
  unfold spectralDeltaTwo
  nlinarith only [hm1,hm2]

theorem variance_fourier_mask {n : ℕ} (g : Cube n → ℝ) :
    variance g = ∑ S : Finset (Fin n), if S=∅ then 0 else fourier g S^2 := by
  classical
  rw [variance_eq_sum_nonempty]
  have h := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S => if S=∅ then (0 : ℝ) else fourier g S^2) (Finset.mem_univ ∅)
  simp only [ite_true,add_zero] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro S hS
  rw [ite_eq_right (Finset.mem_erase.mp hS).1]

theorem noise_fourier_square {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (noise ρ g) S^2 = ρ^(2*S.card)*fourier g S^2 := by
  rw [fourier_noise,mul_pow,← pow_mul,Nat.mul_comm S.card 2]

/-- Simultaneous finite loss ledger, with the inside projection and the
two singleton classes distinguished exactly. -/
theorem shifted_spectral_loss_bound {n : ℕ} {γ t ρ : ℝ}
    (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ) (ht : (2 : ℝ) ≤ t)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (K : Finset (Fin n)) (g : Cube n → ℝ) :
    shiftedMultiplier γ t*variance (noise ρ g) ≤
      spectralQuadratic (fun S => shiftedMultiplier γ (signedSpectralWeight K t S)) (noise ρ g) +
      spectralDeltaTwo γ t ρ*variance (coordinateProjection K g) +
      (spectralDeltaOne γ t ρ-spectralDeltaTwo γ t ρ)*insideSingletonEnergy K g +
      spectralDeltaOutside γ t ρ*outsideSingletonEnergy K g := by
  classical
  have hg0 : 0 < γ := (le_max_left _ _).trans_lt hγ
  rw [variance_fourier_mask,variance_fourier_mask,insideSingletonEnergy_mask,
    outsideSingletonEnergy_mask,spectralQuadratic]
  simp only [noise_fourier_square,fourier_coordinateProjection]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS0 : S=∅
  · subst S
    simp [signedSpectralWeight_empty,shiftedMultiplier_zero]
  · have hcard0 : 1 ≤ S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS0)
    by_cases hSK : S⊆K
    · by_cases hcard : S.card=1
      · simp only [signedSpectralWeight,hS0,hSK,hcard,↓reduceIte,
          Nat.cast_one,show 2*1=2 by norm_num]
        unfold spectralDeltaOne spectralDeltaTwo
        ring_nf <;> exact le_rfl
      · have hc2 : 2 ≤ S.card := by omega
        have h := mul_le_mul_of_nonneg_right (inside_mode_loss_le hg0 ht hρ hc2)
          (sq_nonneg (fourier g S))
        simp only [signedSpectralWeight,hS0,hSK,hcard,↓reduceIte,mul_zero,add_zero]
        nlinarith only [h]
    · by_cases hcard : S.card=1
      · simp only [signedSpectralWeight,hS0,hSK,hcard,↓reduceIte,
          show 2*1=2 by norm_num,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
        unfold spectralDeltaOutside
        ring_nf <;> exact le_rfl
      · simp only [signedSpectralWeight,hS0,hSK,hcard,↓reduceIte,
          zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero]
        ring_nf <;> exact le_rfl

end
end CK
