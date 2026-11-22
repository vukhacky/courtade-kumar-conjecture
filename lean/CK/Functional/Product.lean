module

public import CK.Functional.Entropy

/-! Product decompositions for normalized cube averages, entropy and noise.
The zero-dimensional cube is included in all identities. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem sum_cube_cons {n : ℕ} (v : Cube (n + 1) → ℝ) :
    ∑ x, v x = ∑ x : Cube n, (v (Fin.cons false x) + v (Fin.cons true x)) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp v]
  simp only [Fintype.sum_prod_type, Fin.consEquiv_apply]
  simp [Finset.sum_add_distrib, add_comm]

theorem avg_cube_cons {n : ℕ} (v : Cube (n + 1) → ℝ) :
    avg v = avg (fun x : Cube n => (v (Fin.cons false x) + v (Fin.cons true x)) / 2) := by
  unfold avg
  rw [card_cube, card_cube, sum_cube_cons]
  push_cast
  simp only [pow_succ, mul_inv_rev, ← Finset.sum_div]
  ring

theorem avg_cube_zero (v : Cube 0 → ℝ) : avg v = v Fin.elim0 := by
  have h : v = fun _ : Cube 0 => v Fin.elim0 := by
    funext x
    have hx : x = Fin.elim0 := by funext i; exact Fin.elim0 i
    rw [hx]
  rw [h, avg_const]

theorem entropyFunctional_cube_zero (v : Cube 0 → ℝ) : entropyFunctional v = 0 := by
  simp only [entropyFunctional, avg_cube_zero, sub_self]

theorem entropyFunctional_chain {n : ℕ} (v : Cube (n + 1) → ℝ) :
    entropyFunctional v =
      avg (fun x : Cube n => twoPointEntropy (v (Fin.cons false x)) (v (Fin.cons true x))) +
      entropyFunctional (fun x : Cube n => (v (Fin.cons false x) + v (Fin.cons true x)) / 2) := by
  unfold entropyFunctional twoPointEntropy
  rw [avg_cube_cons (fun x => v x * Real.log (v x)), avg_cube_cons v, avg_sub]
  ring

theorem bscKernel_cons {n : ℕ} (ρ : ℝ) (a b : Bool) (x y : Cube n) :
    bscKernel ρ (Fin.cons a x) (Fin.cons b y) = bitKernel ρ a b * bscKernel ρ x y := by
  simp [bscKernel, Fin.prod_univ_succ]

theorem noise_cons {n : ℕ} (ρ : ℝ) (v : Cube (n + 1) → ℝ) (a : Bool) (x : Cube n) :
    noise ρ v (Fin.cons a x) =
      bitKernel ρ a false * noise ρ (fun y => v (Fin.cons false y)) x +
      bitKernel ρ a true * noise ρ (fun y => v (Fin.cons true y)) x := by
  rw [noise, sum_cube_cons]
  simp only [bscKernel_cons, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, noise]

theorem noise_mean_sections {n : ℕ} (ρ : ℝ) (v : Cube (n + 1) → ℝ) (x : Cube n) :
    (noise ρ v (Fin.cons false x) + noise ρ v (Fin.cons true x)) / 2 =
      noise ρ (fun y => (v (Fin.cons false y) + v (Fin.cons true y)) / 2) x := by
  rw [noise_cons, noise_cons]
  simp only [bitKernel, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false]
  unfold noise
  ring_nf
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]

theorem noise_nonneg_values {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (v : Cube n → ℝ) (hv : ∀ x, 0 ≤ v x) (x : Cube n) : 0 ≤ noise ρ v x := by
  exact Finset.sum_nonneg fun y _ =>
    mul_nonneg (bscKernel_nonneg ⟨by linarith [hρ.1], hρ.2⟩ x y) (hv y)

/-- Averaging in the remaining coordinates cannot increase conditional
two-point entropy. The proof includes zero values and zero transition weights. -/
theorem avg_twoPointEntropy_noise_le {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (a b : Cube n → ℝ) (ha : ∀ x, 0 ≤ a x) (hb : ∀ x, 0 ≤ b x) :
    avg (fun x => twoPointEntropy (noise ρ a x) (noise ρ b x)) ≤
      avg (fun x => twoPointEntropy (a x) (b x)) := by
  calc
    _ ≤ avg (noise ρ (fun x => twoPointEntropy (a x) (b x))) := by
      apply avg_mono
      intro x
      exact twoPointEntropy_sum_le (bscKernel ρ x) a b
        (fun y => bscKernel_nonneg ⟨by linarith [hρ.1], hρ.2⟩ x y) ha hb
    _ = _ := avg_noise ρ _

theorem avg_pair {n : ℕ} (a b : Cube n → ℝ) :
    avg (fun x => (a x + b x) / 2) = (avg a + avg b) / 2 := by
  have heq : (fun x => (a x + b x) / 2) = fun x => (1 / 2 : ℝ) * (a x + b x) := by
    funext x
    ring
  rw [heq, avg_smul, avg_add]
  ring

theorem avg_div {n : ℕ} (g : Cube n → ℝ) (c : ℝ) :
    avg (fun x => g x / c) = avg g / c := by
  rw [show (fun x => g x / c) = (fun x => c⁻¹ * g x) by funext x; ring, avg_smul]
  ring

theorem sum_cube_insertNth {n : ℕ} (i : Fin (n + 1)) (v : Cube (n + 1) → ℝ) :
    ∑ x, v x = ∑ x : Cube n, (v (i.insertNth false x) + v (i.insertNth true x)) := by
  rw [← (Fin.insertNthEquiv (fun _ : Fin (n + 1) => Bool) i).sum_comp v]
  simp only [Fintype.sum_prod_type, Fin.insertNthEquiv_apply]
  simp [Finset.sum_add_distrib, add_comm]

theorem avg_cube_insertNth {n : ℕ} (i : Fin (n + 1)) (v : Cube (n + 1) → ℝ) :
    avg v = avg (fun x : Cube n => (v (i.insertNth false x) + v (i.insertNth true x)) / 2) := by
  unfold avg
  rw [card_cube, card_cube, sum_cube_insertNth i]
  push_cast
  simp only [pow_succ, mul_inv_rev, ← Finset.sum_div]
  ring

theorem bscKernel_insertNth {n : ℕ} (i : Fin (n + 1)) (ρ : ℝ)
    (a b : Bool) (x y : Cube n) :
    bscKernel ρ (i.insertNth a x) (i.insertNth b y) =
      bitKernel ρ a b * bscKernel ρ x y := by
  unfold bscKernel
  rw [Fin.prod_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

theorem noise_insertNth {n : ℕ} (i : Fin (n + 1)) (ρ : ℝ)
    (v : Cube (n + 1) → ℝ) (a : Bool) (x : Cube n) :
    noise ρ v (i.insertNth a x) =
      bitKernel ρ a false * noise ρ (fun y => v (i.insertNth false y)) x +
      bitKernel ρ a true * noise ρ (fun y => v (i.insertNth true y)) x := by
  rw [noise, sum_cube_insertNth i]
  simp only [bscKernel_insertNth, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, noise]

theorem abs_avg_le_avg_abs {n : ℕ} (g : Cube n → ℝ) :
    |avg g| ≤ avg (fun x => |g x|) := by
  unfold avg
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (card_cube_pos n).le)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
    (inv_nonneg.mpr (card_cube_pos n).le)

end
end CK
