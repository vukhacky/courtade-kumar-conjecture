module

public import CK.Low.OddLift

/-! Elementary first-level bounds. These are proved directly from Parseval
and the two Boolean sections; they do not assume Yu's stronger LP bound
or the KST Rademacher estimate. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem mean_sq_add_first_le {n : ℕ} (g : Cube n → ℝ) :
    avg g ^ 2 + fourierWeight g 1 ≤ avg (fun x => g x ^ 2) := by
  rw [← fourierWeight_zero, parseval]
  unfold fourierWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro S _
  by_cases h0 : S.card = 0
  · have h1 : S.card ≠ 1 := by omega
    simp [h0]
  · by_cases h1 : S.card = 1
    · simp [h1]
    · simpa only [h0, h1, ↓reduceIte, zero_add] using sq_nonneg (fourier g S)

theorem avg_sectionMean {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ) :
    avg (sectionMean i g) = avg g := (avg_cube_insertNth i g).symm

theorem fourier_sectionMean_singleton {n : ℕ} (i : Fin (n+1))
    (g : Cube (n+1) → ℝ) (j : Fin n) :
    fourier (sectionMean i g) {j} = fourier g {i.succAbove j} := by
  rw [fourier_singleton, fourier_singleton, avg_cube_insertNth i]
  congr 1
  funext x
  simp only [sectionMean, Fin.insertNth_apply_succAbove]
  ring

theorem fourierWeight_sectionMean {n : ℕ} (i : Fin (n+1)) (g : Cube (n+1) → ℝ) :
    fourierWeight g 1 = fourier g {i} ^ 2 + fourierWeight (sectionMean i g) 1 := by
  rw [fourierWeight_one, Fin.sum_univ_succAbove _ i, fourierWeight_one]
  simp only [fourier_sectionMean_singleton]

theorem sectionMean_sq_add_abs_difference {n : ℕ} (i : Fin (n+1))
    (f : BooleanFunction (n+1)) (x : Cube n) :
    sectionMean i (lift f) x ^ 2 + |sectionDifference i (lift f) x| = 1 := by
  unfold sectionMean sectionDifference lift
  cases f (i.insertNth false x) <;> cases f (i.insertNth true x) <;> norm_num [sign]

/-- The first branch of the LP cap follows from elementary finite-cube
identities, and this form also retains the original mean. -/
theorem firstLevel_mean_coordinate_cap {n : ℕ} (f : BooleanFunction n) (i : Fin n) :
    fourierWeight (lift f) 1 + mean f ^ 2 ≤
      fourier (lift f) {i} ^ 2 + 1 - |fourier (lift f) {i}| := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hb := mean_sq_add_first_le (sectionMean i (lift f))
    rw [avg_sectionMean] at hb
    have habs := abs_avg_le_avg_abs (sectionDifference i (lift f))
    rw [← fourier_singleton_eq_avg_sectionDifference] at habs
    have hsum : avg (fun x => sectionMean i (lift f) x ^ 2) +
        avg (fun x => |sectionDifference i (lift f) x|) = 1 := by
      rw [← avg_add]
      simp only [sectionMean_sq_add_abs_difference, avg_const]
    rw [fourierWeight_sectionMean i (lift f)]
    change avg (lift f) ^ 2 + fourierWeight (sectionMean i (lift f)) 1 ≤ _ at hb
    unfold mean
    linarith

theorem firstLevel_mean_cap {n : ℕ} (f : BooleanFunction n) :
    fourierWeight (lift f) 1 ≤ 1 - |mean f| := by
  have h := firstLevel_mean_coordinate_cap (oddLift f) 0
  rw [fourierWeight_oddLift_one, fourier_oddLift_zero] at h
  have hz : mean (oddLift f) = 0 := oddLift_balanced f
  rw [hz] at h
  linarith

theorem firstLevel_coordinate_cap {n : ℕ} (f : BooleanFunction n) (i : Fin n) :
    fourierWeight (lift f) 1 ≤ fourier (lift f) {i} ^ 2 + 1 - |fourier (lift f) {i}| := by
  have h := firstLevel_mean_coordinate_cap f i
  linarith [sq_nonneg (mean f)]

end
end CK
