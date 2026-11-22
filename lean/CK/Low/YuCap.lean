module

public import CK.Fourier.Parseval
public import CK.Basic.NoiseExtras
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! A finite negative-noise proof of the first-level cap used in Yu's
balanced-coordinate reduction.  Every BSC with parameter in `[-1,1]` is a
positive kernel, including negative parameters.  Bounding its degrees at
least two by `t²` yields the optimized cap without an asymptotic argument. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem neg_pow_le_sq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    {k : ℕ} (hk : 2 ≤ k) : (-t) ^ k ≤ t ^ 2 := by
  calc
    (-t) ^ k ≤ |(-t) ^ k| := le_abs_self _
    _ = t ^ k := by rw [abs_pow, abs_neg, abs_of_nonneg ht.1]
    _ ≤ t ^ 2 := pow_le_pow_of_le_one ht.1 ht.2 hk

/-- Positivity at a negative BSC parameter gives a dimension-free spectral
constraint for every nonnegative function. -/
theorem firstLevel_negative_noise_bound {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (t + t ^ 2) * fourierWeight g 1 ≤
      (1-t ^ 2) * avg g ^ 2 + t ^ 2 * avg (fun x => g x ^ 2) := by
  classical
  have hparam : -t ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hpos : 0 ≤ avg (fun x => g x * noise (-t) g x) := by
    have h := avg_mono (fun x => mul_nonneg (hg x) (noise_nonneg hparam hg x))
    simpa only [avg_const] using h
  rw [parseval_bilinear] at hpos
  simp_rw [fourier_noise] at hpos
  have hupper : (∑ S : Finset (Fin n), (-t) ^ S.card * fourier g S ^ 2) ≤
      (1-t^2) * fourierWeight g 0 - (t+t^2) * fourierWeight g 1 +
        t^2 * ∑ S : Finset (Fin n), fourier g S ^ 2 := by
    unfold fourierWeight
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro S _
    by_cases h0 : S.card = 0
    · have h1 : S.card ≠ 1 := by omega
      simp [h0]
      <;> ring_nf
      <;> exact le_rfl
    · by_cases h1 : S.card = 1
      · simp [h1]
        <;> ring_nf
        <;> exact le_rfl
      · have hk : 2 ≤ S.card := by omega
        simpa only [h0, h1, ↓reduceIte, mul_zero, sub_zero, zero_add] using
          mul_le_mul_of_nonneg_right (neg_pow_le_sq ht hk) (sq_nonneg (fourier g S))
  rw [fourierWeight_zero, ← parseval] at hupper
  have hid : (∑ S : Finset (Fin n), fourier g S * ((-t) ^ S.card * fourier g S)) =
      ∑ S : Finset (Fin n), (-t) ^ S.card * fourier g S ^ 2 := by
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [hid] at hpos
  linarith

/-- The optimized cap for a nonnegative idempotent function, in square-root
form.  An indicator of mean `p` satisfies the square-moment premise. -/
theorem firstLevel_indicator_sqrt_cap {n : ℕ} (g : Cube n → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hsq : avg (fun x => g x ^ 2) = avg g)
    (hp : avg g ∈ Set.Icc (0 : ℝ) (1/4)) :
    fourierWeight g 1 ≤ 2 * avg g * Real.sqrt (avg g) - 2 * avg g ^ 2 := by
  by_cases hp0 : avg g = 0
  · have h := firstLevel_negative_noise_bound g hg (t := 1) (by norm_num)
    rw [hsq, hp0] at h
    simp only [hp0, Real.sqrt_zero]
    nlinarith only [h]
  · have hpp : 0 < avg g := lt_of_le_of_ne hp.1 (Ne.symm hp0)
    let s := Real.sqrt (avg g)
    have hs0 : 0 < s := Real.sqrt_pos.2 hpp
    have hs2 : s ^ 2 = avg g := Real.sq_sqrt hp.1
    have hsle : s ≤ 1/2 := by
      have hn := Real.sqrt_nonneg (avg g)
      dsimp [s]
      nlinarith only [Real.sq_sqrt hp.1, hn, hp.2]
    have hden : 0 < 1-s := by linarith
    let t := s/(1-s)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg hs0.le hden.le
      · exact (div_le_one hden).2 (by linarith)
    have h := firstLevel_negative_noise_bound g hg ht
    rw [hsq, ← hs2] at h
    have hm := mul_le_mul_of_nonneg_right h (sq_nonneg (1-s))
    have hleft : (t+t^2) * fourierWeight g 1 * (1-s)^2 = s * fourierWeight g 1 := by
      dsimp [t]
      field_simp
      <;> ring
    have hright : ((1-t^2)*s^4+t^2*s^2)*(1-s)^2 = 2*s^4*(1-s) := by
      dsimp [t]
      field_simp
      <;> ring
    rw [hleft] at hm
    have hright' : ((1-t^2)*(s^2)^2+t^2*s^2)*(1-s)^2 = 2*s^4*(1-s) := by
      convert hright using 1 <;> ring
    rw [hright'] at hm
    have hcancel : fourierWeight g 1 ≤ 2*s^3*(1-s) := by
      apply (mul_le_mul_iff_right₀ hs0).mp
      nlinarith only [hm]
    change fourierWeight g 1 ≤ 2 * avg g * s - 2 * avg g ^ 2
    rw [← hs2]
    nlinarith only [hcancel]

/-- Indicator of the negative value of a sign-valued Boolean function. -/
def negativeIndicator {n : ℕ} (f : BooleanFunction n) (x : Cube n) : ℝ :=
  (1-lift f x)/2

theorem negativeIndicator_nonneg {n : ℕ} (f : BooleanFunction n) (x : Cube n) :
    0 ≤ negativeIndicator f x := by
  unfold negativeIndicator lift
  cases f x <;> norm_num [sign]

theorem negativeIndicator_sq {n : ℕ} (f : BooleanFunction n) (x : Cube n) :
    negativeIndicator f x ^ 2 = negativeIndicator f x := by
  unfold negativeIndicator lift
  cases f x <;> norm_num [sign]

theorem negativeIndicator_eq {n : ℕ} (f : BooleanFunction n) :
    negativeIndicator f = fun x => (1/2 : ℝ) - (1/2 : ℝ) * lift f x := by
  funext x
  unfold negativeIndicator
  ring

theorem avg_negativeIndicator {n : ℕ} (f : BooleanFunction n) :
    avg (negativeIndicator f) = (1-mean f)/2 := by
  rw [negativeIndicator_eq, avg_sub, avg_const, avg_smul]
  unfold mean
  ring

theorem fourier_negativeIndicator_nonempty {n : ℕ} (f : BooleanFunction n)
    {S : Finset (Fin n)} (hS : S ≠ ∅) :
    fourier (negativeIndicator f) S = -(1/2 : ℝ) * fourier (lift f) S := by
  rw [negativeIndicator_eq, fourier_sub, fourier_const, fourier_smul]
  simp [hS]

theorem fourierWeight_negativeIndicator_one {n : ℕ} (f : BooleanFunction n) :
    fourierWeight (negativeIndicator f) 1 = (1/4 : ℝ) * fourierWeight (lift f) 1 := by
  classical
  unfold fourierWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card = 1
  · have hne : S ≠ ∅ := by intro he; simp [he] at hS
    simp only [hS, ↓reduceIte, fourier_negativeIndicator_nonempty f hne]
    ring
  · simp [hS]

theorem fourierWeight_complement {n : ℕ} (f : BooleanFunction n) (k : ℕ) :
    fourierWeight (lift (fun x => !(f x))) k = fourierWeight (lift f) k := by
  have hf : lift (fun x => !(f x)) = fun x => (-1 : ℝ) * lift f x := by
    funext x
    simp [lift]
  unfold fourierWeight
  simp only [hf, fourier_smul, mul_pow]
  norm_num

/-- Square-root form of the refined biased first-level bound.  This theorem
includes constant Boolean functions; there is no balance assumption. -/
theorem firstLevel_positive_bias_sqrt_cap {n : ℕ} (f : BooleanFunction n)
    (ha : (1/2 : ℝ) ≤ mean f) :
    fourierWeight (lift f) 1 ≤
      8 * ((1-mean f)/2) * Real.sqrt ((1-mean f)/2) - 8 * ((1-mean f)/2)^2 := by
  have hp : avg (negativeIndicator f) ∈ Set.Icc (0 : ℝ) (1/4) := by
    rw [avg_negativeIndicator]
    constructor <;> linarith [(mean_mem_Icc f).2]
  have hsq : avg (fun x => negativeIndicator f x ^ 2) = avg (negativeIndicator f) := by
    simp only [negativeIndicator_sq]
  have h := firstLevel_indicator_sqrt_cap (negativeIndicator f)
    (negativeIndicator_nonneg f) hsq hp
  rw [fourierWeight_negativeIndicator_one, avg_negativeIndicator] at h
  nlinarith only [h]

/-- Refined Yu cap for arbitrary signed Boolean functions with absolute
mean at least `1/2`, obtained by complementing the negative-mean case. -/
theorem firstLevel_biased_sqrt_cap {n : ℕ} (f : BooleanFunction n)
    (ha : (1/2 : ℝ) ≤ |mean f|) :
    fourierWeight (lift f) 1 ≤
      8 * ((1-|mean f|)/2) * Real.sqrt ((1-|mean f|)/2) - 8 * ((1-|mean f|)/2)^2 := by
  by_cases hm : 0 ≤ mean f
  · rw [abs_of_nonneg hm] at ha ⊢
    exact firstLevel_positive_bias_sqrt_cap f ha
  · have hm' : mean f ≤ 0 := le_of_not_ge hm
    rw [abs_of_nonpos hm'] at ha ⊢
    have h := firstLevel_positive_bias_sqrt_cap (fun x => !(f x)) (by
      rw [mean_complement]
      exact ha)
    rw [fourierWeight_complement, mean_complement] at h
    exact h

end
end CK
