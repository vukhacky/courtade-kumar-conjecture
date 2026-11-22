module

public import CK.High.MartingaleDecomposition
public import CK.High.EntropyL1

/-! The complete outside-projection martingale energy inequality, with
an arbitrary real dual parameter and explicit zero-energy cases. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def outsideL1Energy {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ\K, coordinateL1 g i^2

theorem outsideL1Energy_nonneg {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    0 ≤ outsideL1Energy K g := Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem outsideL1Energy_eq {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    outsideL1Energy K g = ∑ i : Fin n, if i∈K then 0 else coordinateL1 g i^2 := by
  classical
  unfold outsideL1Energy
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,zero_add]
  congr 1
  ext i
  simp

theorem martingalePiece_l1_square_sum_le {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    (∑ i : Fin n, (avg (fun x => |martingalePiece K i g x|))^2) ≤ outsideL1Energy K g := by
  classical
  rw [outsideL1Energy_eq]
  apply Finset.sum_le_sum
  intro i _
  have h := pow_le_pow_left₀ (avg_nonneg _ (fun x => abs_nonneg _)) (martingalePiece_l1_le K g i) 2
  simpa only [ite_pow,zero_pow (by decide : 2 ≠ 0)] using h

theorem martingalePiece_affine {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ)
    (i : Fin n) (lam : ℝ) :
    (1+lam/2)*avg (fun x => martingalePiece K i g x^2) -
      Real.exp (lam-1)/2*(avg (fun x => |martingalePiece K i g x|))^2 ≤
        dirichlet (martingalePiece K i g) := by
  have hE := entropyFunctional_square_affine (martingalePiece K i g) lam
  have hLS := entropyFunctional_square_odd_le i (martingalePiece K i g) (martingalePiece_flip K g i)
  linarith

/-- STOC `as:strengthened-split`, affine form.  Every quantity is an
explicit finite average; there is no positivity premise on the energies. -/
theorem martingale_energy_affine {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) (lam : ℝ) :
    (1+lam/2)*avg (fun x => projectionResidual K g x^2) -
      Real.exp (lam-1)/2*outsideL1Energy K g ≤ dirichlet (projectionResidual K g) := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (fun i _ => martingalePiece_affine K g i lam)
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,
    martingale_square_energy,martingale_dirichlet_energy] at h
  have hb := mul_le_mul_of_nonneg_left (martingalePiece_l1_square_sum_le K g)
    (by positivity : 0 ≤ Real.exp (lam-1)/2)
  linarith

theorem outsideL1Energy_pos_of_residual_pos {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ)
    (hV : 0 < avg (fun x => projectionResidual K g x^2)) : 0 < outsideL1Energy K g := by
  have hb := outsideL1Energy_nonneg K g
  apply lt_of_le_of_ne hb
  intro hz
  have h := martingale_energy_affine K g
    (2*dirichlet (projectionResidual K g)/avg (fun x => projectionResidual K g x^2))
  rw [← hz,mul_zero,sub_zero] at h
  have hid : (1+(2*dirichlet (projectionResidual K g)/avg (fun x => projectionResidual K g x^2))/2)*
      avg (fun x => projectionResidual K g x^2) =
      avg (fun x => projectionResidual K g x^2)+dirichlet (projectionResidual K g) := by
    field_simp
  rw [hid] at h
  linarith

/-- Optimizing the proved affine inequality gives the nonlinear version.
The positivity assumptions are exactly those needed for its logarithm. -/
theorem martingale_energy_log {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ)
    (hV : 0 < avg (fun x => projectionResidual K g x^2)) :
    avg (fun x => projectionResidual K g x^2) +
      avg (fun x => projectionResidual K g x^2)/2*
        Real.log (avg (fun x => projectionResidual K g x^2)/outsideL1Energy K g) ≤
      dirichlet (projectionResidual K g) := by
  have hb := outsideL1Energy_pos_of_residual_pos K g hV
  have h := martingale_energy_affine K g
    (1+Real.log (avg (fun x => projectionResidual K g x^2)/outsideL1Energy K g))
  rw [show 1+Real.log (avg (fun x => projectionResidual K g x^2)/outsideL1Energy K g)-1 =
      Real.log (avg (fun x => projectionResidual K g x^2)/outsideL1Energy K g) by ring,
    Real.exp_log (div_pos hV hb)] at h
  have hid : (avg (fun x => projectionResidual K g x^2)/outsideL1Energy K g)/2*outsideL1Energy K g =
      avg (fun x => projectionResidual K g x^2)/2 := by
    field_simp
  rw [hid] at h
  nlinarith only [h]

end
end CK
