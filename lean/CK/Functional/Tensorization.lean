module

public import CK.Functional.Product

/-! Entropy tensorization for the finite uniform Boolean cube, including
nonnegative functions with zeros and the zero-dimensional cube. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def coordinateEntropy {n : ℕ} (v : Cube n → ℝ) (i : Fin n) (x : Cube n) : ℝ :=
  twoPointEntropy (v (Function.update x i false)) (v (Function.update x i true))

theorem avg_coordinateEntropy_zero {n : ℕ} (v : Cube (n + 1) → ℝ) :
    avg (coordinateEntropy v 0) =
      avg (fun x : Cube n => twoPointEntropy (v (Fin.cons false x)) (v (Fin.cons true x))) := by
  rw [avg_cube_cons]
  congr 1
  funext x
  simp only [coordinateEntropy, Fin.update_cons_zero]
  ring

theorem coordinateEntropy_mean_sections_le {n : ℕ} (v : Cube (n + 1) → ℝ)
    (hv : ∀ x, 0 ≤ v x) (i : Fin n) :
    avg (coordinateEntropy (fun x : Cube n =>
      (v (Fin.cons false x) + v (Fin.cons true x)) / 2) i) ≤
      avg (coordinateEntropy v i.succ) := by
  rw [avg_cube_cons (coordinateEntropy v i.succ)]
  apply avg_mono
  intro x
  simp only [coordinateEntropy, ← Fin.cons_update]
  exact twoPointEntropy_midpoint_le (hv _) (hv _) (hv _) (hv _)

/-- Tensorization of the entropy functional on the finite uniform cube.
No positivity approximation is required: zeros are handled directly by
the finite two-point perspective inequality. -/
theorem entropyFunctional_tensorization (n : ℕ) (v : Cube n → ℝ)
    (hv : ∀ x, 0 ≤ v x) :
    entropyFunctional v ≤ ∑ i : Fin n, avg (coordinateEntropy v i) := by
  induction n with
  | zero => simp [entropyFunctional_cube_zero]
  | succ n ih =>
    rw [entropyFunctional_chain, Fin.sum_univ_succ, avg_coordinateEntropy_zero]
    apply add_le_add le_rfl
    calc
      entropyFunctional (fun x : Cube n =>
          (v (Fin.cons false x) + v (Fin.cons true x)) / 2) ≤
          ∑ i : Fin n, avg (coordinateEntropy (fun x : Cube n =>
            (v (Fin.cons false x) + v (Fin.cons true x)) / 2) i) :=
        ih _ (fun x => div_nonneg (add_nonneg (hv _) (hv _)) (by norm_num))
      _ ≤ ∑ i : Fin n, avg (coordinateEntropy v i.succ) := by
        exact Finset.sum_le_sum fun i _ => coordinateEntropy_mean_sections_le v hv i

end
end CK
