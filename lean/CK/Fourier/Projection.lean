module

public import CK.Fourier.Parseval

/-! Coordinate conditional expectation as an actual finite average. Its
Fourier cutoff, orthogonality, tower laws and BSC commutation are proved
from that average, rather than assumed as a spectral definition. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def coordinateMask {n : ℕ} (K : Finset (Fin n)) (x y : Cube n) : Cube n :=
  fun i => if i ∈ K then x i else y i

def coordinateProjection {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ)
    (x : Cube n) : ℝ := avg (fun y => g (coordinateMask K x y))

def DependsOn {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) : Prop :=
  ∀ x y, (∀ i ∈ K, x i = y i) → g x = g y

theorem coordinateMask_empty {n : ℕ} (x y : Cube n) : coordinateMask ∅ x y = y := by
  funext i
  simp [coordinateMask]

theorem coordinateMask_univ {n : ℕ} (x y : Cube n) : coordinateMask Finset.univ x y = x := by
  funext i
  simp [coordinateMask]

theorem coordinateMask_self {n : ℕ} (K : Finset (Fin n)) (x : Cube n) :
    coordinateMask K x x = x := by
  funext i
  simp [coordinateMask]

theorem coordinateProjection_empty {n : ℕ} (g : Cube n → ℝ) (x : Cube n) :
    coordinateProjection ∅ g x = avg g := by
  simp only [coordinateProjection, coordinateMask_empty]

theorem coordinateProjection_univ {n : ℕ} (g : Cube n → ℝ) (x : Cube n) :
    coordinateProjection Finset.univ g x = g x := by
  simp only [coordinateProjection, coordinateMask_univ, avg_const]

theorem coordinateProjection_const {n : ℕ} (K : Finset (Fin n)) (c : ℝ) (x : Cube n) :
    coordinateProjection K (fun _ => c) x = c := avg_const n c

theorem coordinateProjection_add {n : ℕ} (K : Finset (Fin n)) (g h : Cube n → ℝ)
    (x : Cube n) : coordinateProjection K (fun y => g y + h y) x =
      coordinateProjection K g x + coordinateProjection K h x := avg_add _ _

theorem coordinateProjection_smul {n : ℕ} (K : Finset (Fin n)) (c : ℝ)
    (g : Cube n → ℝ) (x : Cube n) :
    coordinateProjection K (fun y => c * g y) x = c * coordinateProjection K g x :=
  avg_smul c _

theorem coordinateProjection_sub {n : ℕ} (K : Finset (Fin n)) (g h : Cube n → ℝ)
    (x : Cube n) : coordinateProjection K (fun y => g y - h y) x =
      coordinateProjection K g x - coordinateProjection K h x := avg_sub _ _

theorem coordinateProjection_mono {n : ℕ} (K : Finset (Fin n))
    {g h : Cube n → ℝ} (hgh : ∀ y, g y ≤ h y) (x : Cube n) :
    coordinateProjection K g x ≤ coordinateProjection K h x :=
  avg_mono (fun y => hgh (coordinateMask K x y))

theorem coordinateProjection_mem_Icc {n : ℕ} (K : Finset (Fin n))
    {a b : ℝ} {g : Cube n → ℝ} (hg : ∀ y, g y ∈ Set.Icc a b) (x : Cube n) :
    coordinateProjection K g x ∈ Set.Icc a b := by
  have hlo := coordinateProjection_mono K (fun y => (hg y).1) x
  have hhi := coordinateProjection_mono K (fun y => (hg y).2) x
  rw [coordinateProjection_const] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem coordinateProjection_dependsOn {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    DependsOn K (coordinateProjection K g) := by
  intro x y hxy
  unfold coordinateProjection
  congr 1
  funext z
  congr 1
  funext i
  by_cases hi : i ∈ K
  · simp only [coordinateMask, ite_eq_left hi, hxy i hi]
  · simp only [coordinateMask, ite_eq_right hi]

theorem coordinateProjection_eq_self {n : ℕ} {K : Finset (Fin n)}
    {g : Cube n → ℝ} (hg : DependsOn K g) : coordinateProjection K g = g := by
  funext x
  have heq (y : Cube n) : g (coordinateMask K x y) = g x :=
    hg _ _ (fun i hi => by simp only [coordinateMask, ite_eq_left hi])
  simp only [coordinateProjection, heq, avg_const]

theorem walsh_coordinateMask {n : ℕ} (S K : Finset (Fin n)) (x y : Cube n) :
    walsh S (coordinateMask K x y) = walsh (S ∩ K) x * walsh (S \ K) y := by
  classical
  simp_rw [walsh_eq_prod_univ]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hS : i ∈ S <;> by_cases hK : i ∈ K <;> simp [coordinateMask, hS, hK]

theorem coordinateProjection_walsh {n : ℕ} (K S : Finset (Fin n)) (x : Cube n) :
    coordinateProjection K (walsh S) x = if S ⊆ K then walsh S x else 0 := by
  classical
  unfold coordinateProjection
  simp_rw [walsh_coordinateMask]
  rw [avg_smul, avg_walsh]
  by_cases h : S ⊆ K
  · rw [Finset.sdiff_eq_empty_iff_subset.mpr h, Finset.inter_eq_left.mpr h]
    simp [h]
  · have hne : S \ K ≠ ∅ := fun heq => h (Finset.sdiff_eq_empty_iff_subset.mp heq)
    simp [hne, h]

theorem coordinateProjection_fourier_expansion {n : ℕ} (K : Finset (Fin n))
    (g : Cube n → ℝ) (x : Cube n) :
    coordinateProjection K g x = ∑ S : Finset (Fin n),
      (if S ⊆ K then fourier g S else 0) * walsh S x := by
  classical
  calc
    coordinateProjection K g x = avg (fun y => ∑ S : Finset (Fin n),
        fourier g S * walsh S (coordinateMask K x y)) := by
      unfold coordinateProjection
      congr 1
      funext y
      exact (fourier_inversion g _).symm
    _ = ∑ S : Finset (Fin n), fourier g S * coordinateProjection K (walsh S) x := by
      rw [avg_sum]
      simp only [avg_smul]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      rw [coordinateProjection_walsh]
      split_ifs <;> ring

theorem fourier_coordinateProjection {n : ℕ} (K S : Finset (Fin n)) (g : Cube n → ℝ) :
    fourier (coordinateProjection K g) S = if S ⊆ K then fourier g S else 0 := by
  classical
  have hfun : coordinateProjection K g = fun x => ∑ T : Finset (Fin n),
      (if T ⊆ K then fourier g T else 0) * walsh T x :=
    funext (coordinateProjection_fourier_expansion K g)
  rw [hfun, fourier_sum]
  simp only [fourier_smul, fourier_walsh, mul_ite, mul_one, mul_zero]
  simp

theorem avg_coordinateProjection {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    avg (coordinateProjection K g) = avg g := by
  rw [← fourier_empty, fourier_coordinateProjection]
  simp [fourier_empty]

theorem coordinateProjection_projection {n : ℕ} (K L : Finset (Fin n)) (g : Cube n → ℝ) :
    coordinateProjection K (coordinateProjection L g) = coordinateProjection (K ∩ L) g := by
  classical
  apply fourier_ext
  intro S
  simp only [fourier_coordinateProjection, Finset.subset_inter_iff]
  by_cases hK : S ⊆ K <;> by_cases hL : S ⊆ L <;> simp [hK, hL]

theorem coordinateProjection_idempotent {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    coordinateProjection K (coordinateProjection K g) = coordinateProjection K g := by
  rw [coordinateProjection_projection, Finset.inter_self]

theorem coordinateProjection_tower {n : ℕ} {K L : Finset (Fin n)} (hKL : K ⊆ L)
    (g : Cube n → ℝ) : coordinateProjection K (coordinateProjection L g) =
      coordinateProjection K g := by
  rw [coordinateProjection_projection, Finset.inter_eq_left.mpr hKL]

theorem coordinateProjection_noise {n : ℕ} (K : Finset (Fin n)) (ρ : ℝ)
    (g : Cube n → ℝ) : coordinateProjection K (noise ρ g) =
      noise ρ (coordinateProjection K g) := by
  classical
  apply fourier_ext
  intro S
  simp only [fourier_coordinateProjection, fourier_noise]
  split_ifs <;> ring

theorem coordinateProjection_selfAdjoint {n : ℕ} (K : Finset (Fin n))
    (g h : Cube n → ℝ) : avg (fun x => coordinateProjection K g x * h x) =
      avg (fun x => g x * coordinateProjection K h x) := by
  classical
  rw [parseval_bilinear, parseval_bilinear]
  apply Finset.sum_congr rfl
  intro S _
  rw [fourier_coordinateProjection, fourier_coordinateProjection]
  split_ifs <;> ring

theorem coordinateProjection_orthogonal {n : ℕ} (K : Finset (Fin n))
    (g h : Cube n → ℝ) :
    avg (fun x => (g x - coordinateProjection K g x) * coordinateProjection K h x) = 0 := by
  classical
  rw [parseval_bilinear]
  apply Finset.sum_eq_zero
  intro S _
  rw [fourier_sub, fourier_coordinateProjection, fourier_coordinateProjection]
  split_ifs <;> ring

theorem coordinateProjection_square_le {n : ℕ} (K : Finset (Fin n))
    (g : Cube n → ℝ) : avg (fun x => coordinateProjection K g x ^ 2) ≤
      avg (fun x => g x ^ 2) := by
  classical
  rw [parseval, parseval]
  apply Finset.sum_le_sum
  intro S _
  rw [fourier_coordinateProjection]
  split_ifs
  · exact le_rfl
  · simpa using sq_nonneg (fourier g S)

end
end CK
