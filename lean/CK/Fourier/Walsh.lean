module

public import CK.Basic.NoiseExtras

/-! Finite Fourier--Walsh characters with the normalization used by the
STOC source: characters are products of signs, and coefficients are
normalized uniform averages. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def walsh {n : ℕ} (S : Finset (Fin n)) (x : Cube n) : ℝ :=
  ∏ i ∈ S, sign (x i)

def fourier {n : ℕ} (g : Cube n → ℝ) (S : Finset (Fin n)) : ℝ :=
  avg (fun x => g x * walsh S x)

theorem sign_sq (b : Bool) : sign b ^ 2 = 1 := by
  cases b <;> norm_num [sign]

theorem sign_mul_self (b : Bool) : sign b * sign b = 1 := by
  simpa only [pow_two] using sign_sq b

@[simp] theorem walsh_empty {n : ℕ} (x : Cube n) : walsh ∅ x = 1 := by
  simp [walsh]

@[simp] theorem walsh_singleton {n : ℕ} (i : Fin n) (x : Cube n) :
    walsh {i} x = sign (x i) := by
  simp [walsh]

theorem walsh_eq_prod_univ {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walsh S x = ∏ i : Fin n, if i ∈ S then sign (x i) else 1 := by
  classical
  rw [← Finset.prod_filter]
  simp [walsh]

theorem walsh_sq {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walsh S x ^ 2 = 1 := by
  rw [walsh, ← Finset.prod_pow]
  simp only [sign_sq, Finset.prod_const_one]

theorem walsh_mul_self {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walsh S x * walsh S x = 1 := by
  simpa only [pow_two] using walsh_sq S x

theorem fourier_empty {n : ℕ} (g : Cube n → ℝ) : fourier g ∅ = avg g := by
  simp [fourier]

theorem fourier_singleton {n : ℕ} (g : Cube n → ℝ) (i : Fin n) :
    fourier g {i} = avg (fun x => g x * sign (x i)) := by
  simp only [fourier, walsh_singleton]

/-- The kernel of the unnormalized Walsh matrix squared. This also covers
the zero-dimensional internal cube. -/
theorem walsh_completeness {n : ℕ} (x y : Cube n) :
    ∑ S : Finset (Fin n), walsh S x * walsh S y =
      if x = y then (Fintype.card (Cube n) : ℝ) else 0 := by
  classical
  have hprod : (∑ S : Finset (Fin n), walsh S x * walsh S y) =
      ∏ i : Fin n, (1 + sign (x i) * sign (y i)) := by
    simp only [walsh, ← Finset.prod_mul_distrib]
    simpa using (Finset.prod_one_add (f := fun i : Fin n => sign (x i) * sign (y i))
      Finset.univ).symm
  rw [hprod]
  by_cases hxy : x = y
  · subst y
    simp only [sign_mul_self]
    norm_num [card_cube]
  · rw [ite_eq_right hxy]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ y i := by
      by_contra h
      push Not at h
      exact hxy (funext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hx : x i <;> cases hy : y i <;> simp_all [sign]

theorem avg_sum {n : ℕ} {α : Type*} [Fintype α] (g : α → Cube n → ℝ) :
    avg (fun x => ∑ a, g a x) = ∑ a, avg (g a) := by
  unfold avg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem fourier_inversion {n : ℕ} (g : Cube n → ℝ) (x : Cube n) :
    ∑ S : Finset (Fin n), fourier g S * walsh S x = g x := by
  classical
  unfold fourier avg
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  have hinner (y : Cube n) :
      (∑ S : Finset (Fin n), (g y * walsh S y) * walsh S x) =
        g y * (if y = x then (Fintype.card (Cube n) : ℝ) else 0) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, walsh_completeness]
  simp_rw [hinner]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hc : (Fintype.card (Cube n) : ℝ) ≠ 0 := ne_of_gt (card_cube_pos n)
  field_simp

theorem sum_walsh_mul {n : ℕ} (S T : Finset (Fin n)) :
    (∑ x : Cube n, walsh S x * walsh T x) =
      if S = T then (Fintype.card (Cube n) : ℝ) else 0 := by
  classical
  simp_rw [walsh_eq_prod_univ, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b =>
    (if i ∈ S then sign b else 1) * (if i ∈ T then sign b else 1))]
  by_cases hST : S = T
  · subst T
    have hi (i : Fin n) : (∑ b : Bool,
        (if i ∈ S then sign b else 1) * (if i ∈ S then sign b else 1)) = 2 := by
      by_cases h : i ∈ S <;> norm_num [h, sign]
    simp_rw [hi]
    simp
  · rw [ite_eq_right hST]
    obtain ⟨i, hi⟩ : ∃ i, ¬ (i ∈ S ↔ i ∈ T) := by
      by_contra h
      push Not at h
      exact hST (Finset.ext h)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all [sign]

theorem walsh_orthogonality {n : ℕ} (S T : Finset (Fin n)) :
    avg (fun x => walsh S x * walsh T x) = if S = T then 1 else 0 := by
  classical
  rw [avg, sum_walsh_mul]
  split_ifs <;> simp

theorem fourier_walsh {n : ℕ} (S T : Finset (Fin n)) :
    fourier (walsh S) T = if S = T then 1 else 0 :=
  walsh_orthogonality S T

theorem noise_walsh {n : ℕ} (ρ : ℝ) (S : Finset (Fin n)) (x : Cube n) :
    noise ρ (walsh S) x = ρ ^ S.card * walsh S x := by
  classical
  unfold noise
  simp_rw [walsh_eq_prod_univ, bscKernel, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i b => bitKernel ρ (x i) b *
    (if i ∈ S then sign b else 1))]
  have hi (i : Fin n) :
      (∑ b : Bool, bitKernel ρ (x i) b * (if i ∈ S then sign b else 1)) =
        if i ∈ S then ρ * sign (x i) else 1 := by
    by_cases h : i ∈ S
    · simp only [ite_eq_left h]
      exact bitKernel_sign_sum ρ (x i)
    · simp only [ite_eq_right h, mul_one]
      exact bitKernel_sum ρ (x i)
  simp_rw [hi]
  rw [← Finset.prod_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  rw [← walsh_eq_prod_univ]
  rfl

theorem avg_noise_mul {n : ℕ} (ρ : ℝ) (g h : Cube n → ℝ) :
    avg (fun x => noise ρ g x * h x) = avg (fun x => g x * noise ρ h x) := by
  unfold avg noise
  congr 1
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  rw [bscKernel_symm ρ x y]
  ring

theorem fourier_noise {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (noise ρ g) S = ρ ^ S.card * fourier g S := by
  rw [fourier, avg_noise_mul]
  simp_rw [noise_walsh]
  have hterm : (fun x => g x * (ρ ^ S.card * walsh S x)) =
      fun x => ρ ^ S.card * (g x * walsh S x) := by
    funext x
    ring
  rw [hterm, avg_smul]
  rfl

theorem avg_walsh {n : ℕ} (S : Finset (Fin n)) :
    avg (walsh S) = if S = ∅ then 1 else 0 := by
  classical
  simpa only [walsh_empty, mul_one] using walsh_orthogonality S ∅

theorem fourier_add {n : ℕ} (g h : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (fun x => g x + h x) S = fourier g S + fourier h S := by
  simp only [fourier, add_mul, avg_add]

theorem fourier_smul {n : ℕ} (c : ℝ) (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (fun x => c * g x) S = c * fourier g S := by
  simp only [fourier, mul_assoc, avg_smul]

theorem fourier_sub {n : ℕ} (g h : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (fun x => g x - h x) S = fourier g S - fourier h S := by
  simp only [fourier, sub_mul, avg_sub]

theorem fourier_sum {n : ℕ} {α : Type*} [Fintype α]
    (g : α → Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (fun x => ∑ a, g a x) S = ∑ a, fourier (g a) S := by
  simp only [fourier, Finset.sum_mul, avg_sum]

theorem fourier_const {n : ℕ} (c : ℝ) (S : Finset (Fin n)) :
    fourier (fun _ : Cube n => c) S = if S = ∅ then c else 0 := by
  classical
  rw [fourier, avg_smul, avg_walsh]
  split_ifs <;> ring

theorem fourier_ext {n : ℕ} {g h : Cube n → ℝ}
    (hgh : ∀ S, fourier g S = fourier h S) : g = h := by
  funext x
  rw [← fourier_inversion g x, ← fourier_inversion h x]
  simp_rw [hgh]

theorem noise_fourier_expansion {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noise ρ g x = ∑ S : Finset (Fin n), ρ ^ S.card * fourier g S * walsh S x := by
  rw [← fourier_inversion (noise ρ g) x]
  simp_rw [fourier_noise]

end
end CK
