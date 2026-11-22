module

public import CK.Fourier.Influences
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Add

/-! The normalized cube Laplacian is the sum of coordinate half-differences.
Its Dirichlet form and the derivative of the finite noise polynomial use
the exact normalization of the STOC source. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def laplacian {n : ℕ} (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ i : Fin n, coordinatePartial i g x

def dirichlet {n : ℕ} (g : Cube n → ℝ) : ℝ :=
  avg (fun x => g x * laplacian g x)

theorem fourier_laplacian {n : ℕ} (g : Cube n → ℝ) (S : Finset (Fin n)) :
    fourier (laplacian g) S = (S.card : ℝ) * fourier g S := by
  classical
  change fourier (fun x => ∑ i : Fin n, coordinatePartial i g x) S = _
  rw [fourier_sum]
  simp_rw [fourier_coordinatePartial]
  rw [← Finset.sum_filter]
  simp

theorem laplacian_fourier_expansion {n : ℕ} (g : Cube n → ℝ) (x : Cube n) :
    laplacian g x = ∑ S : Finset (Fin n), (S.card : ℝ) * fourier g S * walsh S x := by
  rw [← fourier_inversion (laplacian g) x]
  simp_rw [fourier_laplacian]

theorem dirichlet_eq_fourier {n : ℕ} (g : Cube n → ℝ) :
    dirichlet g = ∑ S : Finset (Fin n), (S.card : ℝ) * fourier g S ^ 2 := by
  rw [dirichlet, parseval_bilinear]
  simp_rw [fourier_laplacian]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem dirichlet_eq_sum_partials {n : ℕ} (g : Cube n → ℝ) :
    dirichlet g = ∑ i : Fin n, avg (fun x => coordinatePartial i g x ^ 2) := by
  classical
  rw [dirichlet_eq_fourier]
  simp_rw [parseval, fourier_coordinatePartial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp

theorem dirichlet_nonneg {n : ℕ} (g : Cube n → ℝ) : 0 ≤ dirichlet g := by
  rw [dirichlet_eq_fourier]
  exact Finset.sum_nonneg (fun S _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

theorem laplacian_selfAdjoint {n : ℕ} (g h : Cube n → ℝ) :
    avg (fun x => laplacian g x * h x) = avg (fun x => g x * laplacian h x) := by
  rw [parseval_bilinear, parseval_bilinear]
  simp_rw [fourier_laplacian]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem avg_partial_mul {n : ℕ} (i : Fin n) (g h : Cube n → ℝ) :
    avg (fun x => coordinatePartial i g x * h x) =
      avg (fun x => coordinatePartial i g x * coordinatePartial i h x) := by
  rw [parseval_bilinear, parseval_bilinear]
  simp_rw [fourier_coordinatePartial]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> ring

def noiseDerivative {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) : ℝ :=
  ∑ S : Finset (Fin n), (S.card : ℝ) * ρ^(S.card-1) * fourier g S * walsh S x

theorem hasDerivAt_noise {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    HasDerivAt (fun r => noise r g x) (noiseDerivative ρ g x) ρ := by
  have hfun : (fun r : ℝ => noise r g x) = fun r =>
      ∑ S : Finset (Fin n), r^S.card * fourier g S * walsh S x :=
    funext (fun r => noise_fourier_expansion r g x)
  rw [hfun]
  simpa only [noiseDerivative, Pi.pow_apply, id_eq, mul_one] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun S _ =>
      (((hasDerivAt_id ρ).pow S.card).mul_const (fourier g S)).mul_const (walsh S x)))

theorem mul_noiseDerivative {n : ℕ} (ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    ρ * noiseDerivative ρ g x = laplacian (noise ρ g) x := by
  rw [noiseDerivative, Finset.mul_sum, laplacian_fourier_expansion]
  simp_rw [fourier_noise]
  apply Finset.sum_congr rfl
  intro S _
  cases hS : S.card with
  | zero => simp
  | succ k => simp only [Nat.add_sub_cancel, pow_succ]; ring

theorem hasDerivAt_noise_laplacian {n : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (g : Cube n → ℝ) (x : Cube n) :
    HasDerivAt (fun r => noise r g x) (laplacian (noise ρ g) x / ρ) ρ := by
  have heq : noiseDerivative ρ g x = laplacian (noise ρ g) x / ρ := by
    rw [← mul_noiseDerivative]
    field_simp
  rw [← heq]
  exact hasDerivAt_noise ρ g x

theorem continuous_noise {n : ℕ} (g : Cube n → ℝ) (x : Cube n) :
    Continuous (fun ρ => noise ρ g x) :=
  continuous_iff_continuousAt.mpr (fun ρ => (hasDerivAt_noise ρ g x).continuousAt)

end
end CK
