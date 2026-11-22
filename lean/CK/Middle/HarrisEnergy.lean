module

public import CK.Functional.Harris
public import CK.Fourier.Influences

/-! The conditional Harris/Fourier comparison from the STOC middle-range
argument. The mean is retained; no balance assumption is used. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def cubeComplement {n : ℕ} (x : Cube n) : Cube n := fun i => !(x i)

theorem cubeComplement_involutive (n : ℕ) : Function.Involutive (@cubeComplement n) := by
  intro x
  funext i
  simp [cubeComplement]

theorem cubeComplement_cubeComplement {n : ℕ} (x : Cube n) :
    cubeComplement (cubeComplement x) = x := cubeComplement_involutive n x

def cubeComplementEquiv (n : ℕ) : Cube n ≃ Cube n where
  toFun := cubeComplement
  invFun := cubeComplement
  left_inv := cubeComplement_involutive n
  right_inv := cubeComplement_involutive n

theorem avg_cubeComplement {n : ℕ} (g : Cube n → ℝ) :
    avg (fun x => g (cubeComplement x)) = avg g := by
  unfold avg
  congr 1
  exact (cubeComplementEquiv n).sum_comp g

theorem bool_not_antitone : Antitone Bool.not := by
  intro a b hab
  cases a <;> cases b
  · exact le_rfl
  · exact Bool.false_le true
  · have h : (false : Bool) = true := Bool.eq_true_of_true_le hab
    cases h
  · exact le_rfl

theorem cubeComplement_antitone {n : ℕ} : Antitone (@cubeComplement n) := by
  intro x y hxy i
  exact bool_not_antitone (hxy i)

def realDual {n : ℕ} (g : Cube n → ℝ) : Cube n → ℝ := fun x => -g (cubeComplement x)

theorem realDual_monotone {n : ℕ} {g : Cube n → ℝ} (hg : Monotone g) :
    Monotone (realDual g) := by
  intro x y hxy
  exact neg_le_neg (hg (cubeComplement_antitone hxy))

theorem walsh_cubeComplement {n : ℕ} (S : Finset (Fin n)) (x : Cube n) :
    walsh S (cubeComplement x) = (-1 : ℝ) ^ S.card * walsh S x := by
  simp only [walsh, cubeComplement, sign_not, Finset.prod_neg]

theorem fourier_realDual {n : ℕ} (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (realDual g) S = (-1 : ℝ) ^ (S.card+1) * fourier g S := by
  rw [fourier, ← avg_cubeComplement (fun x => realDual g x * walsh S x)]
  simp only [realDual, cubeComplement_cubeComplement, walsh_cubeComplement]
  have hp : (fun x => -g x * ((-1 : ℝ)^S.card * walsh S x)) =
      fun x => (-1 : ℝ)^(S.card+1) * (g x * walsh S x) := by
    funext x
    rw [pow_succ]
    ring
  rw [hp, avg_smul]
  rfl

/-- The covariance comparison after conditioning on coordinates in `K`.
The constant Fourier term is canceled explicitly on both sides. -/
theorem core_harris {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (K : Finset (Fin n)) (g : Cube n → ℝ) (hg : Monotone g) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
      if S ⊆ K then (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2 else 0) ≤
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
      (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2 := by
  classical
  have h := avg_projected_mul_le K g (noise ρ (realDual g)) hg
    (noise_monotone hρ (realDual_monotone hg))
  rw [parseval_bilinear, parseval_bilinear] at h
  simp only [fourier_coordinateProjection, fourier_noise, fourier_realDual] at h
  have hfull :
      (∑ S : Finset (Fin n),
        (if S ⊆ K then fourier g S else 0) *
          (if S ⊆ K then ρ ^ S.card * ((-1 : ℝ) ^ (S.card+1) * fourier g S) else 0)) =
      ∑ S : Finset (Fin n),
        if S ⊆ K then (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro S _
    split_ifs <;> ring
  rw [hfull] at h
  have hfull' : (∑ S : Finset (Fin n),
      fourier g S * (ρ^S.card * ((-1 : ℝ)^(S.card+1) * fourier g S))) =
      ∑ S : Finset (Fin n), (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2 := by
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [hfull'] at h
  have hL := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S => if S ⊆ K then (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2 else 0)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  have hR := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S => (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  simp only [Finset.empty_subset, ite_true] at hL
  linarith

theorem fourierWeight_eq_sum_nonempty {n : ℕ} (g : Cube n → ℝ) {k : ℕ}
    (hk : 0 < k) : fourierWeight g k =
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
        if S.card = k then fourier g S ^ 2 else 0 := by
  classical
  have h := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin n)))
    (fun S => if S.card = k then fourier g S ^ 2 else 0)
    (Finset.mem_univ (∅ : Finset (Fin n)))
  have hne : (∅ : Finset (Fin n)).card ≠ k := by
    simpa only [Finset.card_empty] using (ne_of_lt hk)
  rw [ite_eq_right hne, add_zero] at h
  exact h.symm

theorem odd_signed_power_le_cubic {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    {k : ℕ} (hk : 3 ≤ k) : (-1 : ℝ)^(k+1) * ρ^k ≤ ρ^3 := by
  have hs : (-1 : ℝ)^(k+1) ≤ 1 := by
    simpa only [abs_neg_one_pow] using le_abs_self ((-1 : ℝ)^(k+1))
  calc
    _ ≤ 1 * ρ^k := mul_le_mul_of_nonneg_right hs (pow_nonneg hρ.1 k)
    _ ≤ ρ^3 := by simpa only [one_mul] using pow_le_pow_of_le_one hρ.1 hρ.2 hk

theorem dual_spectral_cubic_bound {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube n → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
      (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2) ≤
      (ρ-ρ^3) * fourierWeight g 1 + (-ρ^2-ρ^3) * fourierWeight g 2 +
        ρ^3 * variance g := by
  classical
  rw [fourierWeight_eq_sum_nonempty g (by decide : 0 < 1),
    fourierWeight_eq_sum_nonempty g (by decide : 0 < 2), variance_eq_sum_nonempty,
    Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S hS
  have hcard : 0 < S.card := Finset.card_pos.mpr
    (Finset.ne_empty_iff_nonempty.mp (Finset.mem_erase.mp hS).1)
  by_cases h1 : S.card = 1
  · norm_num [h1]
    ring_nf
    exact le_rfl
  · by_cases h2 : S.card = 2
    · norm_num [h2]
      ring_nf
      exact le_rfl
    · simp only [ite_eq_right h1, ite_eq_right h2, mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_right (odd_signed_power_le_cubic hρ (by omega))
        (sq_nonneg _)

theorem sum_nonempty_subsets_eq_powerset {n : ℕ} (K : Finset (Fin n))
    (c : Finset (Fin n) → ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
      if S ⊆ K then c S else 0) = ∑ S ∈ K.powerset.erase ∅, c S := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
    Finset.mem_powerset, and_true]

theorem core_harris_singleton {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin n) (g : Cube n → ℝ) (hg : Monotone g) :
    ρ * fourier g {i} ^ 2 ≤
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
        (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2 := by
  have h := core_harris hρ {i} g hg
  rw [sum_nonempty_subsets_eq_powerset] at h
  have hpow : ({i} : Finset (Fin n)).powerset = {∅, {i}} := by
    ext S
    simp [Finset.mem_powerset, Finset.subset_singleton_iff]
  have hsum : (∑ S ∈ ({i} : Finset (Fin n)).powerset.erase ∅,
      (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2) = ρ * fourier g {i} ^ 2 := by
    rw [hpow]
    simp
  rw [hsum] at h
  exact h

theorem harris_W2_singleton {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioc (0 : ℝ) 1)
    (i : Fin n) (f : BooleanFunction n) (hf : Monotone (lift f)) :
    ρ*(1+ρ) * fourierWeight (lift f) 2 ≤
      (1-ρ^2) * fourierWeight (lift f) 1 + ρ^2 * (1-mean f^2) -
        fourier (lift f) {i} ^ 2 := by
  have h01 : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hρ.1, hρ.2⟩
  have h := (core_harris_singleton h01 i (lift f) hf).trans
    (dual_spectral_cubic_bound h01 (lift f))
  rw [variance_boolean] at h
  have hprod : ρ * (ρ*(1+ρ) * fourierWeight (lift f) 2) ≤
      ρ * ((1-ρ^2) * fourierWeight (lift f) 1 + ρ^2 * (1-mean f^2) -
        fourier (lift f) {i} ^ 2) := by nlinarith [h]
  exact (mul_le_mul_iff_right₀ hρ.1).mp hprod

theorem core_harris_pair {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (i j : Fin n) (hij : i ≠ j) (g : Cube n → ℝ) (hg : Monotone g) :
    ρ * (fourier g {i} ^ 2 + fourier g {j} ^ 2) - ρ^2 * fourier g {i,j} ^ 2 ≤
      ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).erase ∅,
        (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2 := by
  classical
  have h := core_harris hρ {i,j} g hg
  rw [sum_nonempty_subsets_eq_powerset] at h
  have hpow : ({i,j} : Finset (Fin n)).powerset = {∅, {i}, {j}, {i,j}} := by
    have hpj : ({j} : Finset (Fin n)).powerset = {∅, {j}} := by
      ext S
      simp [Finset.mem_powerset, Finset.subset_singleton_iff]
    rw [Finset.powerset_insert, hpj]
    simp only [Finset.image_insert, Finset.image_singleton]
    ext S
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hne_i : ({i} : Finset (Fin n)) ≠ {i,j} := by
    intro hEq
    have hj : j ∈ ({i} : Finset (Fin n)) := hEq ▸ (by simp : j ∈ ({i,j} : Finset (Fin n)))
    simp only [Finset.mem_singleton] at hj
    exact hij hj.symm
  have hne_j : ({j} : Finset (Fin n)) ≠ {i,j} := by
    intro hEq
    have hi : i ∈ ({j} : Finset (Fin n)) := hEq ▸ (by simp : i ∈ ({i,j} : Finset (Fin n)))
    simp only [Finset.mem_singleton] at hi
    exact hij hi
  have hsum : (∑ S ∈ ({i,j} : Finset (Fin n)).powerset.erase ∅,
      (-1 : ℝ)^(S.card+1) * ρ^S.card * fourier g S ^ 2) =
      ρ * (fourier g {i} ^ 2 + fourier g {j} ^ 2) - ρ^2 * fourier g {i,j} ^ 2 := by
    rw [hpow]
    simp [hij, hne_i, hne_j]
    ring
  rw [hsum] at h
  exact h

theorem harris_W2_pair {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioc (0 : ℝ) 1)
    (i j : Fin n) (hij : i ≠ j) (f : BooleanFunction n) (hf : Monotone (lift f)) :
    ρ*(1+ρ) * fourierWeight (lift f) 2 ≤
      (1-ρ^2) * fourierWeight (lift f) 1 + ρ^2 * (1-mean f^2) -
        fourier (lift f) {i} ^ 2 - fourier (lift f) {j} ^ 2 +
        ρ * fourier (lift f) {i,j} ^ 2 := by
  have h01 : ρ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hρ.1, hρ.2⟩
  have h := (core_harris_pair h01 i j hij (lift f) hf).trans
    (dual_spectral_cubic_bound h01 (lift f))
  rw [variance_boolean] at h
  have hprod : ρ * (ρ*(1+ρ) * fourierWeight (lift f) 2) ≤
      ρ * ((1-ρ^2) * fourierWeight (lift f) 1 + ρ^2 * (1-mean f^2) -
        fourier (lift f) {i} ^ 2 - fourier (lift f) {j} ^ 2 +
        ρ * fourier (lift f) {i,j} ^ 2) := by nlinarith [h]
  exact (mul_le_mul_iff_right₀ hρ.1).mp hprod

theorem harris_W2_pair_simplified {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioc (0 : ℝ) 1)
    (i j : Fin n) (hij : i ≠ j) (f : BooleanFunction n) (hf : Monotone (lift f)) :
    ρ*(1+ρ) * fourierWeight (lift f) 2 ≤
      (1-ρ^2) * fourierWeight (lift f) 1 + ρ^2 -
        fourier (lift f) {i} ^ 2 - (1-ρ) * fourier (lift f) {j} ^ 2 := by
  have h := harris_W2_pair hρ i j hij f hf
  have habs := abs_fourier_le_singleton_of_mem hf j {i,j} (by simp)
  have hb : 0 ≤ fourier (lift f) {j} := (abs_nonneg _).trans habs
  have hsq : fourier (lift f) {i,j} ^ 2 ≤ fourier (lift f) {j} ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr habs)
      (add_nonneg hb (abs_nonneg (fourier (lift f) {i,j}))),
      sq_abs (fourier (lift f) {i,j})]
  have hmul := mul_le_mul_of_nonneg_left hsq (le_of_lt hρ.1)
  nlinarith [mul_nonneg (sq_nonneg ρ) (sq_nonneg (mean f))]

end
end CK
