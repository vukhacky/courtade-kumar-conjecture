module

public import CK.Middle.MomentBand
public import CK.Functional.Reindex

/-! The P01 Shannon inequality for an arbitrary ordered pair of distinct
coordinates in every dimension, by a proved coordinate permutation. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem information_gap_ge_moment_band_pair {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Set.Icc (2/3 : ℝ) (76043/100000))
    (hl : (64/25 : ℝ) ≤ 3*fourier (lift f) {i} + 7*fourier (lift f) {j}) :
    (1-ρ^2)/1000 ≤ phi ρ-information ρ f := by
  have hneval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  have hn : 2 ≤ n := by have hi := i.isLt; have hj := j.isLt; omega
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨e, he0, he1⟩ := exists_perm_two_indices i j hij
  let g := reindexFunction e.symm f
  have hmono : Monotone (lift g) := monotone_reindexFunction e.symm hf
  have h0 : fourier (lift g) {(0 : Fin 2).castAdd m} = fourier (lift f) {i} := by
    rw [show lift g = reindexFunction e.symm (lift f) by rfl,
      fourier_reindexFunction_symm]
    simp only [Finset.map_singleton, Equiv.toEmbedding_apply, he0]
  have h1 : fourier (lift g) {(1 : Fin 2).castAdd m} = fourier (lift f) {j} := by
    rw [show lift g = reindexFunction e.symm (lift f) by rfl,
      fourier_reindexFunction_symm]
    simp only [Finset.map_singleton, Equiv.toEmbedding_apply, he1]
  have h := information_gap_ge_moment_band hρ g hmono
    (h0.symm ▸ ha) (by simpa only [h0, h1] using hl)
  simpa only [g, information_reindexFunction] using h

/-- Shannon mutual information bound throughout the P01 coefficient region. -/
theorem mutualInformation_lt_phi_moment_band_pair {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (ha : fourier (lift f) {i} ∈ Set.Icc (2/3 : ℝ) (76043/100000))
    (hl : (64/25 : ℝ) ≤ 3*fourier (lift f) {i} + 7*fourier (lift f) {j}) :
    mutualInformation ρ f < phi ρ := by
  rw [mutualInformation_eq_information_all]
  have h := information_gap_ge_moment_band_pair hρ f hf i j hij ha hl
  have hlam : 0 < 1-ρ^2 := by nlinarith [hρ.1, hρ.2]
  linarith

end
end CK
