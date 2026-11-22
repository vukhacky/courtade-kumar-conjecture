module

public import CK.Fourier.Walsh
public import CK.Basic.ShannonBridge
public import Mathlib.Logic.Equiv.Fintype

/-! Coordinate equivalences preserve finite cube averages, noise, Fourier
coefficients, and Shannon mutual information. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def cubeEquiv {n m : ℕ} (e : Fin n ≃ Fin m) : Cube n ≃ Cube m where
  toFun x j := x (e.symm j)
  invFun y i := y (e i)
  left_inv x := by funext i; simp
  right_inv y := by funext j; simp

def reindexFunction {α : Type*} {n m : ℕ} (e : Fin n ≃ Fin m) (g : Cube n → α) :
    Cube m → α := fun x => g ((cubeEquiv e).symm x)

@[simp] theorem cubeEquiv_apply {n m : ℕ} (e : Fin n ≃ Fin m) (x : Cube n) (j : Fin m) :
    cubeEquiv e x j = x (e.symm j) := rfl

@[simp] theorem cubeEquiv_symm_apply {n m : ℕ} (e : Fin n ≃ Fin m)
    (x : Cube m) (i : Fin n) : (cubeEquiv e).symm x i = x (e i) := rfl

theorem avg_reindexFunction {n m : ℕ} (e : Fin n ≃ Fin m) (g : Cube n → ℝ) :
    avg (reindexFunction e g) = avg g := by
  unfold avg reindexFunction
  rw [Fintype.card_congr (cubeEquiv e).symm, Equiv.sum_comp]

theorem bscKernel_cubeEquiv {n m : ℕ} (e : Fin n ≃ Fin m)
    (ρ : ℝ) (x y : Cube n) :
    bscKernel ρ (cubeEquiv e x) (cubeEquiv e y) = bscKernel ρ x y := by
  unfold bscKernel
  rw [← e.prod_comp]
  simp only [cubeEquiv_apply, Equiv.symm_apply_apply]

theorem noise_reindexFunction {n m : ℕ} (e : Fin n ≃ Fin m)
    (ρ : ℝ) (g : Cube n → ℝ) (x : Cube m) :
    noise ρ (reindexFunction e g) x = reindexFunction e (noise ρ g) x := by
  unfold noise reindexFunction
  rw [← (cubeEquiv e).sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Equiv.symm_apply_apply]
  congr 1
  conv_lhs => lhs; rw [← (cubeEquiv e).apply_symm_apply x]
  exact bscKernel_cubeEquiv e ρ _ _

theorem walsh_reindex {n m : ℕ} (e : Fin n ≃ Fin m)
    (S : Finset (Fin n)) (x : Cube m) :
    walsh (S.map e.toEmbedding) x = walsh S ((cubeEquiv e).symm x) := by
  simp only [walsh, Finset.prod_map, Equiv.toEmbedding_apply, cubeEquiv_symm_apply]

theorem fourier_reindexFunction {n m : ℕ} (e : Fin n ≃ Fin m)
    (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (reindexFunction e g) (S.map e.toEmbedding) = fourier g S := by
  unfold fourier
  simp only [walsh_reindex]
  exact avg_reindexFunction e (fun x => g x * walsh S x)

theorem lift_reindexFunction {n m : ℕ} (e : Fin n ≃ Fin m) (f : BooleanFunction n) :
    lift (reindexFunction e f) = reindexFunction e (lift f) := rfl

theorem mean_reindexFunction {n m : ℕ} (e : Fin n ≃ Fin m) (f : BooleanFunction n) :
    mean (reindexFunction e f) = mean f := avg_reindexFunction e (lift f)

theorem information_reindexFunction {n m : ℕ} (e : Fin n ≃ Fin m)
    (ρ : ℝ) (f : BooleanFunction n) :
    information ρ (reindexFunction e f) = information ρ f := by
  unfold information
  rw [mean_reindexFunction, lift_reindexFunction]
  simp only [noise_reindexFunction]
  rw [show (fun x => phi (reindexFunction e (noise ρ (lift f)) x)) =
      reindexFunction e (fun x => phi (noise ρ (lift f) x)) by rfl,
    avg_reindexFunction]

theorem mutualInformation_reindexFunction {n m : ℕ} (e : Fin n ≃ Fin m)
    (ρ : ℝ) (f : BooleanFunction n) :
    mutualInformation ρ (reindexFunction e f) = mutualInformation ρ f := by
  rw [mutualInformation_eq_information_all, mutualInformation_eq_information_all,
    information_reindexFunction]

theorem monotone_reindexFunction {α : Type*} [Preorder α] {n m : ℕ}
    (e : Fin n ≃ Fin m) {g : Cube n → α} (hg : Monotone g) :
    Monotone (reindexFunction e g) := by
  intro x y hxy
  exact hg (fun i => hxy (e i))

theorem fourier_reindexFunction_symm {n m : ℕ} (e : Fin n ≃ Fin m)
    (g : Cube m → ℝ) (S : Finset (Fin n)) :
    fourier (reindexFunction e.symm g) S = fourier g (S.map e.toEmbedding) := by
  have h := fourier_reindexFunction e.symm g (S.map e.toEmbedding)
  have he : e.toEmbedding.trans e.symm.toEmbedding = Function.Embedding.refl _ := by
    ext i
    simp
  simpa only [Finset.map_map, he, Finset.map_refl] using h

/-- Any ordered pair of distinct coordinates can be moved to the first two
positions by an actual permutation. -/
theorem exists_perm_two_indices {m : ℕ} (i j : Fin (2+m)) (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin (2+m)),
      e ((0 : Fin 2).castAdd m) = i ∧ e ((1 : Fin 2).castAdd m) = j := by
  have hpair : Function.Injective (![i,j] : Fin 2 → Fin (2+m)) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair
    (Fin.castAdd m : Fin 2 → Fin (2+m)) (![i,j] : Fin 2 → Fin (2+m))
    (Fin.castAddEmb m).injective hpair
  exact ⟨e, by simpa using he 0, by simpa using he 1⟩

end
end CK
