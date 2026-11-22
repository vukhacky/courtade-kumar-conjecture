module

public import CK.Fourier.Walsh

/-! Parseval, Fourier levels, and variance for the normalized finite cube. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def fourierWeight {n : ℕ} (g : Cube n → ℝ) (k : ℕ) : ℝ :=
  ∑ S : Finset (Fin n), if S.card = k then fourier g S ^ 2 else 0

def variance {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  avg (fun x => (g x - avg g) ^ 2)

theorem parseval_bilinear {n : ℕ} (g h : Cube n → ℝ) :
    avg (fun x => g x * h x) =
      ∑ S : Finset (Fin n), fourier g S * fourier h S := by
  have hpoint : (fun x => g x * h x) = fun x =>
      ∑ S : Finset (Fin n), fourier g S * (h x * walsh S x) := by
    funext x
    calc
      g x * h x = (∑ S : Finset (Fin n), fourier g S * walsh S x) * h x := by
        rw [fourier_inversion]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro S _
        ring
  rw [hpoint, avg_sum]
  simp only [avg_smul]
  rfl

theorem parseval {n : ℕ} (g : Cube n → ℝ) :
    avg (fun x => g x ^ 2) = ∑ S : Finset (Fin n), fourier g S ^ 2 := by
  simpa only [pow_two] using parseval_bilinear g g

theorem fourierWeight_nonneg {n : ℕ} (g : Cube n → ℝ) (k : ℕ) :
    0 ≤ fourierWeight g k := by
  exact Finset.sum_nonneg fun S _ => by split_ifs <;> positivity

theorem fourierWeight_zero {n : ℕ} (g : Cube n → ℝ) :
    fourierWeight g 0 = avg g ^ 2 := by
  classical
  simp [fourierWeight, Finset.card_eq_zero, fourier_empty]

theorem fourierWeight_eq_zero_of_lt {n : ℕ} (g : Cube n → ℝ) {k : ℕ}
    (hk : n < k) : fourierWeight g k = 0 := by
  apply Finset.sum_eq_zero
  intro S _
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  simp [show S.card ≠ k by omega]

theorem sum_fourierWeight {n : ℕ} (g : Cube n → ℝ) :
    ∑ k ∈ Finset.range (n+1), fourierWeight g k = avg (fun x => g x ^ 2) := by
  classical
  rw [parseval]
  unfold fourierWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  have hS : S.card < n+1 := by
    have hle : S.card ≤ n := by simpa using Finset.card_le_univ S
    omega
  simp [hS]

theorem avg_lift_sq {n : ℕ} (f : BooleanFunction n) :
    avg (fun x => lift f x ^ 2) = 1 := by
  change avg (fun x => sign (f x) ^ 2) = 1
  simp only [sign_sq, avg_const]

theorem parseval_boolean {n : ℕ} (f : BooleanFunction n) :
    ∑ S : Finset (Fin n), fourier (lift f) S ^ 2 = 1 := by
  rw [← parseval, avg_lift_sq]

theorem sum_fourierWeight_boolean {n : ℕ} (f : BooleanFunction n) :
    ∑ k ∈ Finset.range (n+1), fourierWeight (lift f) k = 1 := by
  rw [sum_fourierWeight, avg_lift_sq]

theorem fourierWeight_zero_boolean {n : ℕ} (f : BooleanFunction n) :
    fourierWeight (lift f) 0 = mean f ^ 2 := fourierWeight_zero (lift f)

theorem variance_nonneg {n : ℕ} (g : Cube n → ℝ) : 0 ≤ variance g := by
  have h := avg_mono (fun x : Cube n => sq_nonneg (g x - avg g))
  simpa [variance, avg_const] using h

theorem variance_eq_avg_sq_sub_sq {n : ℕ} (g : Cube n → ℝ) :
    variance g = avg (fun x => g x ^ 2) - avg g ^ 2 := by
  have hpoint : (fun x => (g x - avg g) ^ 2) =
      fun x => g x ^ 2 - (2 * avg g) * g x + avg g ^ 2 := by
    funext x
    ring
  rw [variance, hpoint, avg_add, avg_sub, avg_smul, avg_const]
  ring

theorem variance_boolean {n : ℕ} (f : BooleanFunction n) :
    variance (lift f) = 1 - mean f ^ 2 := by
  rw [variance_eq_avg_sq_sub_sq, avg_lift_sq]
  rfl

theorem variance_eq_sum_nonempty {n : ℕ} (g : Cube n → ℝ) :
    variance g = ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
      fourier g S ^ 2 := by
  classical
  rw [variance_eq_avg_sq_sub_sq, parseval]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S => fourier g S ^ 2) (Finset.mem_univ (∅ : Finset (Fin n)))
  rw [fourier_empty] at hsum
  linarith

theorem fourierWeight_noise {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (k : ℕ) :
    fourierWeight (noise ρ g) k = ρ ^ (2*k) * fourierWeight g k := by
  classical
  unfold fourierWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : S.card = k
  · simp only [hS, ite_true, fourier_noise, mul_pow, ← pow_mul]
    rw [Nat.mul_comm k 2]
  · simp only [ite_eq_right hS, mul_zero]

theorem noise_square_energy {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) :
    avg (fun x => noise ρ g x ^ 2) =
      ∑ k ∈ Finset.range (n+1), ρ ^ (2*k) * fourierWeight g k := by
  rw [← sum_fourierWeight]
  simp_rw [fourierWeight_noise]

theorem variance_noise_le {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (g : Cube n → ℝ) : variance (noise ρ g) ≤ ρ ^ 2 * variance g := by
  classical
  rw [variance_eq_sum_nonempty, variance_eq_sum_nonempty, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hc : S.card ≠ 0 := by
    intro hc
    exact (Finset.mem_erase.mp hS).1 (Finset.card_eq_zero.mp hc)
  have hr : ρ ^ 2 ≤ 1 := by
    have h1 : 0 ≤ ρ+1 := by linarith [hρ.1]
    have h2 : 0 ≤ 1-ρ := by linarith [hρ.2]
    nlinarith [mul_nonneg h1 h2]
  have hp : (ρ ^ S.card) ^ 2 ≤ ρ ^ 2 := by
    rw [← pow_mul, Nat.mul_comm S.card 2, pow_mul]
    exact pow_le_of_le_one (sq_nonneg ρ) hr hc
  rw [fourier_noise, mul_pow]
  exact mul_le_mul_of_nonneg_right hp (sq_nonneg _)

theorem variance_noise_boolean_le {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1) (f : BooleanFunction n) :
    variance (noise ρ (lift f)) ≤ ρ ^ 2 * (1-mean f ^ 2) := by
  simpa only [variance_boolean] using variance_noise_le hρ (lift f)

/-- Uniform probability that two Boolean functions disagree. -/
def booleanDistance {n : ℕ} (f g : BooleanFunction n) : ℝ :=
  avg (fun x => if f x = g x then 0 else 1)

def signedCoordinate {n : ℕ} (i : Fin n) (b : Bool) : BooleanFunction n :=
  fun x => if b then x i else !(x i)

theorem lift_signedCoordinate {n : ℕ} (i : Fin n) (b : Bool) (x : Cube n) :
    lift (signedCoordinate i b) x = sign b * sign (x i) := by
  change sign (if b then x i else !(x i)) = sign b * sign (x i)
  cases b <;> simp

theorem signedCoordinate_isSignedDictator {n : ℕ} (i : Fin n) (b : Bool) :
    IsSignedDictator (signedCoordinate i b) := by
  refine ⟨i, ?_⟩
  cases b
  · right; intro x; rfl
  · left; intro x; rfl

theorem booleanDistance_eq_correlation {n : ℕ} (f g : BooleanFunction n) :
    booleanDistance f g = (1-avg (fun x => lift f x * lift g x))/2 := by
  have hpoint : (fun x : Cube n => if f x = g x then (0 : ℝ) else 1) =
      fun x => (1/2 : ℝ) - (1/2 : ℝ) * (lift f x * lift g x) := by
    funext x
    change (if f x = g x then (0 : ℝ) else 1) =
      (1/2 : ℝ) - (1/2 : ℝ) * (sign (f x) * sign (g x))
    cases hf : f x <;> cases hg : g x <;> norm_num [sign]
  rw [booleanDistance, hpoint, avg_sub, avg_const, avg_smul]
  ring

theorem booleanDistance_signedCoordinate {n : ℕ} (f : BooleanFunction n)
    (i : Fin n) (b : Bool) :
    booleanDistance f (signedCoordinate i b) =
      (1-sign b * fourier (lift f) {i})/2 := by
  rw [booleanDistance_eq_correlation]
  simp_rw [lift_signedCoordinate]
  have hp : (fun x => lift f x * (sign b * sign (x i))) =
      fun x => sign b * (lift f x * sign (x i)) := by
    funext x
    ring
  rw [hp, avg_smul, fourier_singleton]

theorem fin_univ_nonempty {n : ℕ} (hn : 0 < n) :
    (Finset.univ : Finset (Fin n)).Nonempty :=
  ⟨⟨0, hn⟩, Finset.mem_univ _⟩

def maxSingletonCoeff {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) : ℝ :=
  Finset.univ.sup' (fin_univ_nonempty hn) (fun i => |fourier (lift f) {i}|)

def minSignedDictatorDistance {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) : ℝ :=
  (Finset.univ : Finset (Fin n × Bool)).inf'
    ⟨(⟨0, hn⟩, true), Finset.mem_univ _⟩
    (fun p => booleanDistance f (signedCoordinate p.1 p.2))

theorem singleton_le_max {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) (i : Fin n) :
    |fourier (lift f) {i}| ≤ maxSingletonCoeff hn f := by
  exact Finset.le_sup' (fun j => |fourier (lift f) {j}|) (Finset.mem_univ i)

theorem exists_max_singleton {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    ∃ i : Fin n, maxSingletonCoeff hn f = |fourier (lift f) {i}| := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' (fin_univ_nonempty hn)
    (fun j => |fourier (lift f) {j}|)
  exact ⟨i, hi⟩

theorem minSignedDictatorDistance_eq {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    minSignedDictatorDistance hn f = (1-maxSingletonCoeff hn f)/2 := by
  classical
  apply le_antisymm
  · obtain ⟨i, hi⟩ := exists_max_singleton hn f
    by_cases hc : 0 ≤ fourier (lift f) {i}
    · have hle : minSignedDictatorDistance hn f ≤
          booleanDistance f (signedCoordinate i true) :=
        Finset.inf'_le _ (Finset.mem_univ (i, true))
      rw [booleanDistance_signedCoordinate, sign_true, one_mul] at hle
      rw [hi, abs_of_nonneg hc]
      exact hle
    · have hle : minSignedDictatorDistance hn f ≤
          booleanDistance f (signedCoordinate i false) :=
        Finset.inf'_le _ (Finset.mem_univ (i, false))
      rw [booleanDistance_signedCoordinate, sign_false, neg_one_mul] at hle
      rw [hi, abs_of_neg (lt_of_not_ge hc)]
      exact hle
  · apply Finset.le_inf'
    intro p _
    rw [booleanDistance_signedCoordinate]
    have hmax := singleton_le_max hn f p.1
    have hsign : sign p.2 * fourier (lift f) {p.1} ≤
        |fourier (lift f) {p.1}| := by
      cases hb : p.2
      · simpa using neg_le_abs (fourier (lift f) {p.1})
      · simpa using le_abs_self (fourier (lift f) {p.1})
    linarith

theorem isSignedDictator_iff_exists_signedCoordinate {n : ℕ} (f : BooleanFunction n) :
    IsSignedDictator f ↔ ∃ i b, f = signedCoordinate i b := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i, true, funext hi⟩
    · exact ⟨i, false, funext hi⟩
  · rintro ⟨i, b, rfl⟩
    exact signedCoordinate_isSignedDictator i b

theorem fourier_boolean_mem_Icc {n : ℕ} (f : BooleanFunction n)
    (S : Finset (Fin n)) : fourier (lift f) S ∈ Set.Icc (-1 : ℝ) 1 := by
  have hp (x : Cube n) : (lift f x * walsh S x) ^ 2 = 1 := by
    rw [mul_pow, walsh_sq, mul_one]
    exact sign_sq (f x)
  have hlo := avg_mono (fun x : Cube n => show (-1 : ℝ) ≤ lift f x * walsh S x by
    nlinarith [hp x, sq_nonneg (lift f x * walsh S x + 1)])
  have hhi := avg_mono (fun x : Cube n => show lift f x * walsh S x ≤ (1 : ℝ) by
    nlinarith [hp x, sq_nonneg (lift f x * walsh S x - 1)])
  rw [avg_const] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem maxSingletonCoeff_mem_Icc {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    maxSingletonCoeff hn f ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨i, hi⟩ := exists_max_singleton hn f
  rw [hi]
  exact ⟨abs_nonneg _, abs_le.mpr (fourier_boolean_mem_Icc f {i})⟩

theorem minSignedDictatorDistance_mem_Icc {n : ℕ} (hn : 0 < n)
    (f : BooleanFunction n) : minSignedDictatorDistance hn f ∈ Set.Icc (0 : ℝ) (1/2) := by
  rw [minSignedDictatorDistance_eq]
  have h := maxSingletonCoeff_mem_Icc hn f
  constructor <;> linarith [h.1, h.2]

end
end CK
