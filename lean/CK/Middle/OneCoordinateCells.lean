module

public import CK.Middle.MovingCell

/-! Low-cap and high-cap coefficient-cell bounds from certified endpoint residual and clock inequalities. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle
noncomputable section
open CK.Profile

theorem mutualInformation_le_phi_low_cap_cell {n : ℕ} {ρ l u a A B : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n) (hf : Monotone (lift f))
    (i : Fin n) (hai : fourier (lift f) {i}=a)
    (hmax : ∀ j, fourier (lift f) {j} ≤ a)
    (hl : 0 < l) (ha : a ∈ Icc l u) (k : ℕ) (hA : A ≤ 0)
    (hrl : A*l^2+B-(k : ℝ)*l^2 ≤ l^2)
    (hru : 0 ≤ A*u^2+B-(k : ℝ)*u^2)
    (hW : (A+1)*a^2+B ≤ fourierWeight (lift f) 1)
    (hleft : clock (movingProfile k A B (fun x => x) (l^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ)
    (hright : clock (movingProfile k A B (fun x => x) (u^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ) :
    mutualInformation ρ f ≤ phi ρ := by
  have ha0 := hl.trans_le ha.1
  have hu0 := ha0.trans_le ha.2
  have hsq : a^2 ∈ Icc (l^2) (u^2) :=
    ⟨(sq_le_sq₀ hl.le ha0.le).mpr ha.1,(sq_le_sq₀ ha0.le hu0.le).mpr ha.2⟩
  apply mutualInformation_le_phi_movingCell hρ f i
    (by rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i),hai]) ha0 k
    (fun x => x) (sq_pos_of_pos hl) hsq
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy α β hα hβ hsum
    rfl
  · intro x hx
    exact low_residual_domain k hA hx hrl hru
  · exact sq_pos_of_pos ha0
  · intro j _
    rw [Real.sqrt_sq ha0.le,abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    exact hmax j
  · exact hW
  · exact hleft
  · exact hright

theorem mutualInformation_le_phi_high_cap_cell {n : ℕ} {ρ l u a A B : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n) (hf : Monotone (lift f))
    (i : Fin n) (hai : fourier (lift f) {i}=a)
    (hl : 0 < l) (hu : u < 1) (ha : a ∈ Icc l u) (k : ℕ) (hA : A ≤ 0)
    (hB : 0 ≤ B+A*u)
    (hrl : 0 ≤ A*l^2+B-(k : ℝ)*(1-l)^2)
    (hru : A*u^2+B-(k : ℝ)*(1-u)^2 ≤ (1-u)^2)
    (hW : (A+1)*a^2+B ≤ fourierWeight (lift f) 1)
    (hleft : clock (movingProfile k A B highCap (l^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ)
    (hright : clock (movingProfile k A B highCap (u^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ) :
    mutualInformation ρ f ≤ phi ρ := by
  have ha0 := hl.trans_le ha.1
  have hu0 := ha0.trans_le ha.2
  have ha1 := ha.2.trans_lt hu
  have hsq : a^2 ∈ Icc (l^2) (u^2) :=
    ⟨(sq_le_sq₀ hl.le ha0.le).mpr ha.1,(sq_le_sq₀ ha0.le hu0.le).mpr ha.2⟩
  apply mutualInformation_le_phi_movingCell hρ f i
    (by rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i),hai]) ha0 k highCap
    (sq_pos_of_pos hl) hsq
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy α β hα hβ hsum
    exact highCap_convex.2 ((sq_nonneg l).trans hx.1) ((sq_nonneg l).trans hy.1) hα hβ hsum
  · intro x hx
    exact high_residual_domain_squared k hA hl.le hu0.le hu hx hB hrl hru
  · simp only [highCap,Real.sqrt_sq ha0.le]
    exact sq_pos_of_pos (sub_pos.mpr ha1)
  · intro j hji
    rw [highCap,Real.sqrt_sq ha0.le,Real.sqrt_sq (sub_nonneg.mpr ha1.le),
      abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    have hp := singleton_pair_le_one f j i hji
    rw [hai] at hp
    linarith only [hp]
  · exact hW
  · exact hleft
  · exact hright

theorem mutualInformation_le_phi_high_cap_cell_discriminant {n : ℕ} {ρ l u a A B : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n) (hf : Monotone (lift f))
    (i : Fin n) (hai : fourier (lift f) {i}=a)
    (hl : 0 < l) (hu : u < 1) (ha : a ∈ Icc l u) (k : ℕ) (hA : A ≤ 0)
    (hdisc : B*((k : ℝ)+1-A)+A*((k : ℝ)+1) ≤ 0)
    (hrl : 0 ≤ A*l^2+B-(k : ℝ)*(1-l)^2)
    (hru : 0 ≤ A*u^2+B-(k : ℝ)*(1-u)^2)
    (hW : (A+1)*a^2+B ≤ fourierWeight (lift f) 1)
    (hleft : clock (movingProfile k A B highCap (l^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ)
    (hright : clock (movingProfile k A B highCap (u^2)) (meanEntropy ρ/ρ) ≤ -Real.log ρ) :
    mutualInformation ρ f ≤ phi ρ := by
  have ha0 := hl.trans_le ha.1
  have hu0 := ha0.trans_le ha.2
  have ha1 := ha.2.trans_lt hu
  have hsq : a^2 ∈ Icc (l^2) (u^2) :=
    ⟨(sq_le_sq₀ hl.le ha0.le).mpr ha.1,(sq_le_sq₀ ha0.le hu0.le).mpr ha.2⟩
  apply mutualInformation_le_phi_movingCell hρ f i
    (by rw [abs_of_nonneg (singleton_nonneg_of_monotone hf i),hai]) ha0 k highCap
    (sq_pos_of_pos hl) hsq
  · refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy α β hα hβ hsum
    exact highCap_convex.2 ((sq_nonneg l).trans hx.1) ((sq_nonneg l).trans hy.1) hα hβ hsum
  · intro x hx
    exact high_residual_domain_discriminant_squared k hA hl.le hu0.le hx hrl hru hdisc
  · simp only [highCap,Real.sqrt_sq ha0.le]
    exact sq_pos_of_pos (sub_pos.mpr ha1)
  · intro j hji
    rw [highCap,Real.sqrt_sq ha0.le,Real.sqrt_sq (sub_nonneg.mpr ha1.le),
      abs_of_nonneg (singleton_nonneg_of_monotone hf j)]
    have hp := singleton_pair_le_one f j i hji
    rw [hai] at hp
    linarith only [hp]
  · exact hW
  · exact hleft
  · exact hright

end
end CK.Middle
