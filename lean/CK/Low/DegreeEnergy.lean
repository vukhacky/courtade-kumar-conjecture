module

public import CK.Fourier.Parseval
public import CK.Functional.SignEntropy

/-! Fourier degree truncation and its quadratic and cubic entropy bounds. The statements take explicit scalar entropy and Fourier bounds as premises. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def degreeCorrection {n : ℕ} (ρ : ℝ) (d : ℕ) (g : Cube n → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 d, (ρ^(2*k)-ρ^(d+k)) * fourierWeight g k

theorem degreeCorrection_eq_subsets {n : ℕ} (ρ : ℝ) (d : ℕ) (g : Cube n → ℝ) :
    degreeCorrection ρ d g = ∑ S : Finset (Fin n),
      if 1 ≤ S.card ∧ S.card < d then (ρ^(2*S.card)-ρ^(d+S.card))*fourier g S^2 else 0 := by
  classical
  unfold degreeCorrection fourierWeight
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp only [Finset.sum_ite_eq, Finset.mem_Ico]

theorem degree_energy {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (d : ℕ) (g : Cube n → ℝ) :
    avg (fun x => noise ρ g x ^ 2) ≤ ρ^d * avg (fun x => g x * noise ρ g x) +
      (1-ρ^d)*avg g ^ 2 + degreeCorrection ρ d g := by
  classical
  rw [parseval, parseval_bilinear, degreeCorrection_eq_subsets]
  simp only [fourier_noise]
  have hzero : (1-ρ^d)*avg g ^ 2 = ∑ S : Finset (Fin n),
      if S.card = 0 then (1-ρ^d)*fourier g S ^ 2 else 0 := by
    simp [Finset.card_eq_zero, fourier_empty]
  rw [hzero, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  by_cases h0 : S.card = 0
  · simp only [h0, pow_zero, one_mul]
    norm_num
    ring_nf
    exact le_rfl
  · have hp : 1 ≤ S.card := by omega
    by_cases hlt : S.card < d
    · simp only [ite_eq_right h0, hp, hlt, and_self, ↓reduceIte, add_zero]
      rw [pow_add, mul_pow, ← pow_mul, Nat.mul_comm S.card 2]
      ring_nf
      exact le_rfl
    · simp only [ite_eq_right h0, hlt, and_false, ↓reduceIte, add_zero]
      have hpow : ρ^(2*S.card) ≤ ρ^(d+S.card) :=
        pow_le_pow_of_le_one hρ.1 hρ.2 (by omega)
      have h := mul_le_mul_of_nonneg_right hpow (sq_nonneg (fourier g S))
      rw [mul_pow, ← pow_mul, Nat.mul_comm S.card 2]
      convert h using 1 <;> ring

theorem lift_mul_le_abs {n : ℕ} (f : BooleanFunction n) (g : Cube n → ℝ) (x : Cube n) :
    lift f x * g x ≤ |g x| := by
  unfold lift
  cases f x <;> simp only [sign_false, sign_true, neg_one_mul, one_mul]
  · exact neg_le_abs _
  · exact le_abs_self _

theorem degree_product_energy {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (d : ℕ) (f : BooleanFunction n) :
    (1-ρ^d)*(1-mean f^2)-degreeCorrection ρ d (lift f) ≤
      avg (fun x => (1-|noise ρ (lift f) x|)*(1+|noise ρ (lift f) x|-ρ^d)) := by
  have he := degree_energy hρ d (lift f)
  have hm := avg_mono (lift_mul_le_abs f (noise ρ (lift f)))
  have hr : 0 ≤ ρ^d := pow_nonneg hρ.1 d
  have hmul := mul_le_mul_of_nonneg_left hm hr
  have hp (x : Cube n) : (1-|noise ρ (lift f) x|)*(1+|noise ρ (lift f) x|-ρ^d) =
      (1-ρ^d) + ρ^d * |noise ρ (lift f) x| - noise ρ (lift f) x^2 := by
    nlinarith [sq_abs (noise ρ (lift f) x)]
  simp_rw [hp]
  rw [avg_sub, avg_add, avg_const, avg_smul]
  unfold mean
  linarith

theorem degreeCorrection_two {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) :
    degreeCorrection ρ 2 g = ρ^2*(1-ρ)*fourierWeight g 1 := by
  simp only [degreeCorrection, show Finset.Ico 1 2 = {1} by decide, Finset.sum_singleton]
  norm_num only [Nat.reduceMul, Nat.reduceAdd]
  ring

theorem degreeCorrection_three {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) :
    degreeCorrection ρ 3 g = (ρ^2-ρ^4)*fourierWeight g 1 +
      (ρ^4-ρ^5)*fourierWeight g 2 := by
  norm_num [degreeCorrection, show Finset.Ico 1 3 = {1,2} by decide]

theorem quadratic_product_energy {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction n) :
    (1-ρ^2)*(1-mean f^2)-ρ^2*(1-ρ)*fourierWeight (lift f) 1 ≤
      avg (fun x => (1-|noise ρ (lift f) x|)*(1+|noise ρ (lift f) x|-ρ^2)) := by
  simpa only [degreeCorrection_two] using degree_product_energy hρ 2 f

theorem cubic_product_energy {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (f : BooleanFunction n) :
    (1-ρ^3)*(1-mean f^2)-(ρ^2-ρ^4)*fourierWeight (lift f) 1 -
      (ρ^4-ρ^5)*fourierWeight (lift f) 2 ≤
      avg (fun x => (1-|noise ρ (lift f) x|)*(1+|noise ρ (lift f) x|-ρ^3)) := by
  have h := degree_product_energy hρ 3 f
  rw [degreeCorrection_three] at h
  linarith

theorem signEntropy_abs (t : ℝ) : signEntropy |t| = signEntropy t := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), signEntropy_neg]

theorem posteriorEntropy_ge_degree_gate {n : ℕ} {ρ c : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c) (d : ℕ)
    (hgate : ∀ t ∈ Set.Icc (0 : ℝ) 1, c*(1-t)*(1+t-ρ^d) ≤ signEntropy t)
    (f : BooleanFunction n) :
    c*((1-ρ^d)*(1-mean f^2)-degreeCorrection ρ d (lift f)) ≤ posteriorEntropy ρ f := by
  calc
    _ ≤ c * avg (fun x => (1-|noise ρ (lift f) x|)*(1+|noise ρ (lift f) x|-ρ^d)) :=
      mul_le_mul_of_nonneg_left (degree_product_energy hρ d f) hc
    _ = avg (fun x => c*(1-|noise ρ (lift f) x|)*(1+|noise ρ (lift f) x|-ρ^d)) := by
      rw [← avg_smul]
      congr 1
      funext x
      ring
    _ ≤ posteriorEntropy ρ f := by
      apply avg_mono
      intro x
      have hx := noise_mem_Icc (show ρ ∈ Set.Icc (-1 : ℝ) 1 from ⟨by linarith [hρ.1], hρ.2⟩)
        (lift f) (fun y => sign_mem_Icc (f y)) x
      have ht : |noise ρ (lift f) x| ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨abs_nonneg _, abs_le.mpr hx⟩
      simpa only [signEntropy_abs] using hgate _ ht

theorem quadratic_information_budget {n : ℕ} {ρ c C : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c)
    (hgate : ∀ t ∈ Set.Icc (0 : ℝ) 1, c*(1-t)*(1+t-ρ^2) ≤ signEntropy t)
    (f : BooleanFunction n) (hcap : fourierWeight (lift f) 1 + mean f^2 ≤ C) :
    c*((1-ρ^2)-ρ^2*(1-ρ)*C)-signEntropy ρ+phi (mean f)-
      c*(1-2*ρ^2+ρ^3)*mean f^2 ≤ phi ρ-information ρ f := by
  have h := posteriorEntropy_ge_degree_gate hρ hc 2 hgate f
  rw [degreeCorrection_two] at h
  have hn : 0 ≤ c*ρ^2*(1-ρ) := mul_nonneg (mul_nonneg hc (sq_nonneg ρ)) (sub_nonneg.mpr hρ.2)
  have hcap' := mul_le_mul_of_nonneg_left hcap hn
  rw [information_eq_signEntropy_sub_posterior, signEntropy_eq_log_two_sub_phi,
    signEntropy_eq_log_two_sub_phi]
  nlinarith

end
end CK
