module

public import CK.Middle.HarrisEnergy
public import CK.Reduction.Compression

/-! Fourier identities for the balanced odd lift, which retains the original mean as a singleton coefficient. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem fourierWeight_one {n : ℕ} (g : Cube n → ℝ) :
    fourierWeight g 1 = ∑ i : Fin n, fourier g {i} ^ 2 := by
  classical
  unfold fourierWeight
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => ({i} : Finset (Fin n)))
  · intro i _
    simp
  · intro i _ j _ hij
    exact Finset.singleton_injective hij
  · intro S hS
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hS).2
    exact ⟨i, Finset.mem_univ _, rfl⟩
  · intro i _
    rfl

def oddLift {n : ℕ} (f : BooleanFunction n) : BooleanFunction (n+1) :=
  fun x => if x 0 then f (Fin.tail x) else !(f (cubeComplement (Fin.tail x)))

theorem lift_oddLift_cons_false {n : ℕ} (f : BooleanFunction n) (x : Cube n) :
    lift (oddLift f) (Fin.cons false x) = realDual (lift f) x := by
  simp [lift, oddLift, realDual]

theorem lift_oddLift_cons_true {n : ℕ} (f : BooleanFunction n) (x : Cube n) :
    lift (oddLift f) (Fin.cons true x) = lift f x := by
  simp [lift, oddLift]

theorem oddLift_balanced {n : ℕ} (f : BooleanFunction n) : Balanced (oddLift f) := by
  unfold Balanced mean
  rw [avg_cube_cons]
  simp only [lift_oddLift_cons_false, lift_oddLift_cons_true, avg_pair,
    realDual, avg_neg, avg_cubeComplement]
  ring

theorem fourier_oddLift_zero {n : ℕ} (f : BooleanFunction n) :
    fourier (lift (oddLift f)) {0} = mean f := by
  rw [fourier_singleton, avg_cube_cons]
  simp only [lift_oddLift_cons_false, lift_oddLift_cons_true, Fin.cons_zero,
    sign_false, sign_true, mul_neg_one, mul_one, avg_pair, realDual, neg_neg, avg_cubeComplement]
  unfold mean
  ring

theorem fourier_oddLift_succ {n : ℕ} (f : BooleanFunction n) (i : Fin n) :
    fourier (lift (oddLift f)) {i.succ} = fourier (lift f) {i} := by
  rw [fourier_singleton, avg_cube_cons]
  simp only [lift_oddLift_cons_false, lift_oddLift_cons_true, Fin.cons_succ, avg_pair]
  rw [← fourier_singleton, ← fourier_singleton, fourier_realDual]
  norm_num

theorem fourierWeight_oddLift_one {n : ℕ} (f : BooleanFunction n) :
    fourierWeight (lift (oddLift f)) 1 = fourierWeight (lift f) 1 + mean f ^ 2 := by
  rw [fourierWeight_one, Fin.sum_univ_succ, fourier_oddLift_zero, fourierWeight_one]
  simp only [fourier_oddLift_succ]
  ring

theorem maxSingletonCoeff_oddLift {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) :
    maxSingletonCoeff (Nat.succ_pos n) (oddLift f) = max (maxSingletonCoeff hn f) |mean f| := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := exists_max_singleton (Nat.succ_pos n) (oddLift f)
    rw [hj]
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [fourier_oddLift_zero]
      exact le_max_right _ _
    · rw [fourier_oddLift_succ]
      exact (singleton_le_max hn f i).trans (le_max_left _ _)
  · apply max_le
    · obtain ⟨i, hi⟩ := exists_max_singleton hn f
      rw [hi, ← fourier_oddLift_succ f i]
      exact singleton_le_max (Nat.succ_pos n) (oddLift f) i.succ
    · rw [← fourier_oddLift_zero f]
      exact singleton_le_max (Nat.succ_pos n) (oddLift f) 0

end
end CK
