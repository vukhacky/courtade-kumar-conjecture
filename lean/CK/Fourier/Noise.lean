module

public import CK.Basic.Cube

/-! Finite algebra for the BSC semigroup. All identities include dimension zero.
The semigroup identities are algebraic and hence hold for every real parameter;
positivity claims below retain their explicit probability-domain hypotheses. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem bitKernel_comp (η ρ : ℝ) (a c : Bool) :
    ∑ b : Bool, bitKernel η a b * bitKernel ρ b c = bitKernel (η * ρ) a c := by
  cases a <;> cases c <;> simp [bitKernel] <;> ring

theorem bscKernel_comp {n : ℕ} (η ρ : ℝ) (x z : Cube n) :
    ∑ y : Cube n, bscKernel η x y * bscKernel ρ y z = bscKernel (η * ρ) x z := by
  simp only [bscKernel, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : Fin n) (b : Bool) =>
    bitKernel η (x i) b * bitKernel ρ b (z i))]
  simp only [bitKernel_comp]

theorem noise_noise {n : ℕ} (η ρ : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noise η (noise ρ g) x = noise (η * ρ) g x := by
  unfold noise
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [← mul_assoc, ← Finset.sum_mul, bscKernel_comp]

theorem noise_add {n : ℕ} (ρ : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noise ρ (fun y => g y + h y) x = noise ρ g x + noise ρ h x := by
  simp [noise, mul_add, Finset.sum_add_distrib]

theorem noise_smul {n : ℕ} (ρ c : ℝ) (g : Cube n → ℝ) (x : Cube n) :
    noise ρ (fun y => c * g y) x = c * noise ρ g x := by
  simp only [noise, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem noise_sub {n : ℕ} (ρ : ℝ) (g h : Cube n → ℝ) (x : Cube n) :
    noise ρ (fun y => g y - h y) x = noise ρ g x - noise ρ h x := by
  simp [noise, mul_sub, Finset.sum_sub_distrib]

theorem noise_mono {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {g h : Cube n → ℝ} (hgh : ∀ y, g y ≤ h y) (x : Cube n) :
    noise ρ g x ≤ noise ρ h x :=
  Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hgh y) (bscKernel_nonneg hρ x y)

theorem noise_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    {g : Cube n → ℝ} (hg : ∀ y, 0 ≤ g y) (x : Cube n) : 0 ≤ noise ρ g x := by
  exact Finset.sum_nonneg fun y _ => mul_nonneg (bscKernel_nonneg hρ x y) (hg y)

theorem avg_mul_noise {n : ℕ} (ρ : ℝ) (g h : Cube n → ℝ) :
    avg (fun x => g x * noise ρ h x) = avg (fun x => noise ρ g x * h x) := by
  unfold avg noise
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [bscKernel_symm ρ y x]
  ring

theorem bitKernel_pos {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1) (a b : Bool) :
    0 < bitKernel ρ a b := by
  unfold bitKernel
  split_ifs <;> linarith [hρ.1, hρ.2]

theorem bscKernel_pos {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (-1 : ℝ) 1)
    (x y : Cube n) : 0 < bscKernel ρ x y := by
  exact Finset.prod_pos fun i _ => bitKernel_pos hρ (x i) (y i)

end
end CK
