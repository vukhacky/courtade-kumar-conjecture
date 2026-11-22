module

public import CK.High.MartingaleEnergy
public import CK.High.SpectralTransfer
public import CK.High.InfluenceProjection

/-! The signed Fourier multiplier produced by the outside martingale
bound. Only outside singleton modes can be negative; the precise dual
parameter condition makes every shifted multiplier positive. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

def signedSpectralWeight {n : ℕ} (K : Finset (Fin n)) (t : ℝ) (S : Finset (Fin n)) : ℝ :=
  if S⊆K then (S.card : ℝ) else if S.card=1 then t-Real.exp (2*t-3)/2 else t

def shiftedMultiplier (γ s : ℝ) : ℝ := γ*s/(γ+s)

def insideSingletonEnergy {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) : ℝ :=
  ∑ i ∈ K, fourier g {i}^2

def outsideSingletonEnergy {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) : ℝ :=
  ∑ i ∈ Finset.univ\K, fourier g {i}^2

theorem shiftedMultiplier_zero (γ : ℝ) : shiftedMultiplier γ 0=0 := by simp [shiftedMultiplier]

theorem shiftedMultiplier_identity {γ s : ℝ} (hs : γ+s ≠ 0) :
    shiftedMultiplier γ s=γ-γ^2/(γ+s) := by
  unfold shiftedMultiplier
  field_simp
  <;> ring

theorem shiftedMultiplier_monotone {γ s t : ℝ}
    (hs : 0 < γ+s) (hst : s ≤ t) : shiftedMultiplier γ s ≤ shiftedMultiplier γ t := by
  have ht : 0 < γ+t := by linarith
  rw [shiftedMultiplier_identity (ne_of_gt hs),shiftedMultiplier_identity (ne_of_gt ht)]
  exact sub_le_sub_left (div_le_div_of_nonneg_left (sq_nonneg γ) hs (by linarith)) γ

theorem shiftedMultiplier_nonneg {γ s : ℝ} (hγ : 0 < γ) (hs : 0 ≤ s) :
    0 ≤ shiftedMultiplier γ s := by unfold shiftedMultiplier; positivity

theorem signedSpectralWeight_empty {n : ℕ} (K : Finset (Fin n)) (t : ℝ) :
    signedSpectralWeight K t ∅=0 := by simp [signedSpectralWeight]

theorem signedSpectralWeight_shift_pos {n : ℕ} (K : Finset (Fin n)) {t γ : ℝ}
    (ht : (2 : ℝ) ≤ t) (hγ : max 0 (Real.exp (2*t-3)/2-t) < γ)
    (S : Finset (Fin n)) : 0 < signedSpectralWeight K t S+γ := by
  have hg0 : 0 < γ := (le_max_left _ _).trans_lt hγ
  have hgo : Real.exp (2*t-3)/2-t < γ := (le_max_right _ _).trans_lt hγ
  unfold signedSpectralWeight
  split_ifs <;> first | positivity | linarith

theorem sum_singleton_modes {n : ℕ} (q : Finset (Fin n) → ℝ) :
    (∑ S : Finset (Fin n), if S.card=1 then q S else 0) = ∑ i : Fin n, q {i} := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => ({i} : Finset (Fin n)))
  · intro i _
    simp
  · intro i _ j _ hij
    exact Finset.singleton_injective hij
  · intro S hS
    obtain ⟨i,rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hS).2
    exact ⟨i,Finset.mem_univ _,rfl⟩
  · intro i _
    rfl

theorem outsideSingletonEnergy_mask {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    outsideSingletonEnergy K g =
      ∑ S : Finset (Fin n), if S.card=1 then (if S⊆K then 0 else fourier g S^2) else 0 := by
  classical
  rw [sum_singleton_modes]
  simp only [Finset.singleton_subset_iff]
  unfold outsideSingletonEnergy
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,zero_add]
  congr 1
  ext i
  simp

theorem insideSingletonEnergy_mask {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    insideSingletonEnergy K g =
      ∑ S : Finset (Fin n), if S.card=1 then (if S⊆K then fourier g S^2 else 0) else 0 := by
  classical
  rw [sum_singleton_modes]
  simp [insideSingletonEnergy,Finset.singleton_subset_iff]

theorem outsideL1Energy_eq_singletons_of_monotone {n : ℕ}
    (K : Finset (Fin n)) (g : Cube n → ℝ) (hg : Monotone g) :
    outsideL1Energy K g=outsideSingletonEnergy K g := by
  unfold outsideL1Energy outsideSingletonEnergy
  simp only [coordinateL1_eq_singleton_of_monotone g hg]

theorem dirichlet_projection_add_residual {n : ℕ} (K : Finset (Fin n)) (g : Cube n → ℝ) :
    dirichlet (coordinateProjection K g)+dirichlet (projectionResidual K g)=dirichlet g := by
  classical
  simp only [dirichlet_eq_fourier,fourier_coordinateProjection,fourier_projectionResidual]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro S _
  split_ifs <;> ring

theorem signedSpectralQuadratic_identity {n : ℕ} (K : Finset (Fin n)) (t : ℝ) (g : Cube n → ℝ) :
    spectralQuadratic (signedSpectralWeight K t) g =
      dirichlet (coordinateProjection K g) + t*avg (fun x => projectionResidual K g x^2) -
        Real.exp (2*t-3)/2*outsideSingletonEnergy K g := by
  classical
  rw [spectralQuadratic,dirichlet_eq_fourier,parseval,outsideSingletonEnergy_mask]
  simp only [fourier_coordinateProjection,fourier_projectionResidual]
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  unfold signedSpectralWeight
  by_cases hS : S⊆K <;> by_cases hcard : S.card=1 <;> simp [hS,hcard] <;> ring

/-- The actual monotone-function quadratic-form lower bound, before the
arcsine transfer. No spectral operator is postulated. -/
theorem signedSpectralQuadratic_le_dirichlet {n : ℕ} (K : Finset (Fin n)) (t : ℝ)
    (g : Cube n → ℝ) (hg : Monotone g) :
    spectralQuadratic (signedSpectralWeight K t) g ≤ dirichlet g := by
  have h := martingale_energy_affine K g (2*t-2)
  rw [outsideL1Energy_eq_singletons_of_monotone K g hg] at h
  have he : 2*t-2-1=2*t-3 := by ring
  rw [he] at h
  rw [signedSpectralQuadratic_identity,← dirichlet_projection_add_residual K g]
  nlinarith only [h]

end
end CK
