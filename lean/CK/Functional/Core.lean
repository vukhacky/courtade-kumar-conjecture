module

public import CK.Functional.SignEntropy
public import Mathlib.Logic.Equiv.Fin.Basic

/-! Retained-core entropy comparison. The core consists of the first `k`
coordinates and the remaining `m` coordinates are averaged explicitly. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem sum_cube_append {k m : ℕ} (g : Cube (k + m) → ℝ) :
    ∑ z, g z = ∑ x : Cube k, ∑ y : Cube m, g (Fin.append x y) := by
  rw [← (Fin.appendEquiv k m).sum_comp g]
  simp only [Fintype.sum_prod_type]
  rfl

theorem avg_cube_append {k m : ℕ} (g : Cube (k + m) → ℝ) :
    avg g = avg (fun x : Cube k => avg (fun y : Cube m => g (Fin.append x y))) := by
  unfold avg
  rw [card_cube, card_cube, card_cube, sum_cube_append]
  push_cast
  rw [pow_add, mul_inv_rev, ← Finset.mul_sum]
  ring

theorem avg_avg_comm {k m : ℕ} (g : Cube k → Cube m → ℝ) :
    avg (fun x => avg (g x)) = avg (fun y => avg (fun x => g x y)) := by
  unfold avg
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
  ring

theorem bscKernel_append {k m : ℕ} (ρ : ℝ)
    (x x' : Cube k) (y y' : Cube m) :
    bscKernel ρ (Fin.append x y) (Fin.append x' y') =
      bscKernel ρ x x' * bscKernel ρ y y' := by
  simp only [bscKernel, Fin.prod_univ_add, Fin.append_left, Fin.append_right]

/-- Noise only in the retained block. -/
def coreNoise {k m : ℕ} (ρ : ℝ) (g : Cube (k + m) → ℝ)
    (x : Cube k) (y : Cube m) : ℝ :=
  noise ρ (fun x' => g (Fin.append x' y)) x

/-- Conditional expectation given the retained block. -/
def coreAverage {k m : ℕ} (g : Cube (k + m) → ℝ) (x : Cube k) : ℝ :=
  avg (fun y : Cube m => g (Fin.append x y))

theorem noise_append_core {k m : ℕ} (ρ : ℝ) (g : Cube (k + m) → ℝ)
    (x : Cube k) (y : Cube m) :
    noise ρ g (Fin.append x y) = noise ρ (coreNoise ρ g x) y := by
  rw [noise, sum_cube_append]
  simp only [bscKernel_append, coreNoise, noise, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y' _
  apply Finset.sum_congr rfl
  intro x' _
  ring

theorem avg_coreNoise {k m : ℕ} (ρ : ℝ) (g : Cube (k + m) → ℝ) (x : Cube k) :
    avg (coreNoise ρ g x) = noise ρ (coreAverage g) x := by
  unfold coreNoise noise coreAverage avg
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x' _
  ring

theorem coreNoise_mem_Icc {k m : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube (k + m) → ℝ) (hg : ∀ z, g z ∈ Set.Icc (-1 : ℝ) 1)
    (x : Cube k) (y : Cube m) : coreNoise ρ g x y ∈ Set.Icc (-1 : ℝ) 1 := by
  exact noise_mem_Icc ⟨by linarith [hρ.1], hρ.2⟩ _ (fun z => hg _) _

/-- Exact specialization of retained-core entropy contraction to finite cubes.
All dimensions, including an empty retained block or an empty complement, are
allowed; `g` may be any function taking values in the closed interval. -/
theorem signEntropy_noise_ge_core {k m : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (g : Cube (k + m) → ℝ) (hg : ∀ z, g z ∈ Set.Icc (-1 : ℝ) 1) :
    ρ ^ 2 * avg (fun y : Cube m => avg (fun x : Cube k => signEntropy (coreNoise ρ g x y))) +
      (1 - ρ ^ 2) * avg (fun x : Cube k => signEntropy (noise ρ (coreAverage g) x)) ≤
      avg (fun z => signEntropy (noise ρ g z)) := by
  rw [avg_cube_append]
  simp_rw [noise_append_core]
  have h := avg_mono (fun x : Cube k =>
    signEntropy_noise_ge hρ (coreNoise ρ g x) (coreNoise_mem_Icc hρ g hg x))
  simp only [avg_coreNoise, avg_add, avg_smul] at h
  rw [avg_avg_comm] at h
  exact h

end
end CK
