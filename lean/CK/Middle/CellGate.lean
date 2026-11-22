module

public import CK.Middle.CubicEnergy
public import CK.Middle.HarrisEnergy

/-! Exact coefficient-cell bridges for the cubic/clock dichotomy. These
lemmas cover real intervals; rational cell data are separate certificates. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
namespace CK
noncomputable section

theorem first_second_levels_le_one {n : ℕ} (f : BooleanFunction n) :
    fourierWeight (lift f) 1 + fourierWeight (lift f) 2 ≤ 1 := by
  classical
  rw [fourierWeight,fourierWeight,← Finset.sum_add_distrib,← parseval_boolean f]
  apply Finset.sum_le_sum
  intro S _
  by_cases h1 : S.card=1
  · simp only [h1,ite_true,show ¬(1:ℕ)=2 by decide,ite_false,add_zero]
    exact le_rfl
  · by_cases h2 : S.card=2
    · simp only [ite_eq_right h1,ite_eq_left h2,zero_add]
      exact le_rfl
    · simp only [ite_eq_right h1,ite_eq_right h2,add_zero]
      exact sq_nonneg _

theorem cubicWeight_le_beta_bound {n : ℕ} {ρ R w v : ℝ}
    (hρ : 0 ≤ ρ) (hR : ρ ≤ R) (f : BooleanFunction n)
    (hw : fourierWeight (lift f) 1 ≤ w) (hv : fourierWeight (lift f) 2 ≤ v) :
    cubicWeight ρ f ≤ w+cubicBeta R*v := by
  have hb := mul_le_mul_of_nonneg_right (cubicBeta_mono hρ hR)
    (fourierWeight_nonneg (lift f) 2)
  have hv' := mul_le_mul_of_nonneg_left hv (cubicBeta_nonneg (hρ.trans hR))
  unfold cubicWeight
  linarith

theorem cubicWeight_le_of_parseval_cell {n : ℕ} {ρ R w M : ℝ}
    (hρ : 0 ≤ ρ) (hR : ρ ≤ R) (hR1 : R ≤ 1) (f : BooleanFunction n)
    (hw : fourierWeight (lift f) 1 ≤ w)
    (hcell : cubicBeta R+(1-cubicBeta R)*w ≤ M) : cubicWeight ρ f ≤ M := by
  have hp := first_second_levels_le_one f
  have h := cubicWeight_le_beta_bound hρ hR f le_rfl (show
    fourierWeight (lift f) 2 ≤ 1-fourierWeight (lift f) 1 by linarith)
  have hb1 := cubicBeta_le_one ⟨hρ.trans hR,hR1⟩
  have hm := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hb1)
  nlinarith only [h,hm,hcell]

theorem secondLevel_le_of_harris_pair_cell {n : ℕ} {η a b w : ℝ}
    (hη : η ∈ Set.Ioc (0 : ℝ) 1) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (f : BooleanFunction n) (hf : Monotone (lift f)) (i j : Fin n) (hij : i ≠ j)
    (hai : a ≤ fourier (lift f) {i}) (hbj : b ≤ fourier (lift f) {j})
    (hw : fourierWeight (lift f) 1 ≤ w) :
    fourierWeight (lift f) 2 ≤ ((1-η^2)*w+η^2-a^2-(1-η)*b^2)/(η*(1+η)) := by
  have he := harris_W2_pair_simplified hη i j hij f hf
  have he2 : 0 ≤ 1-η^2 := by nlinarith [hη.1,hη.2]
  have hw' := mul_le_mul_of_nonneg_left hw he2
  have hai2 : a^2 ≤ fourier (lift f) {i}^2 := by nlinarith
  have hbj2 : b^2 ≤ fourier (lift f) {j}^2 := by nlinarith
  have hb' := mul_le_mul_of_nonneg_left hbj2 (sub_nonneg.mpr hη.2)
  apply (le_div_iff₀ (mul_pos hη.1 (by linarith [hη.1] : 0 < 1+η))).mpr
  nlinarith only [he,hw',hai2,hb']

theorem secondLevel_le_of_harris_singleton_cell {n : ℕ} {η a w : ℝ}
    (hη : η ∈ Set.Ioc (0 : ℝ) 1) (ha : 0 ≤ a)
    (f : BooleanFunction n) (hf : Monotone (lift f)) (i : Fin n)
    (hai : a ≤ fourier (lift f) {i}) (hw : fourierWeight (lift f) 1 ≤ w) :
    fourierWeight (lift f) 2 ≤ ((1-η^2)*w+η^2-a^2)/(η*(1+η)) := by
  have he := harris_W2_singleton hη i f hf
  have he2 : 0 ≤ 1-η^2 := by nlinarith [hη.1,hη.2]
  have hw' := mul_le_mul_of_nonneg_left hw he2
  have hai2 : a^2 ≤ fourier (lift f) {i}^2 := by nlinarith
  have hm := mul_nonneg (sq_nonneg η) (sq_nonneg (mean f))
  apply (le_div_iff₀ (mul_pos hη.1 (by linarith [hη.1] : 0 < 1+η))).mpr
  nlinarith only [he,hw',hai2,hm]

theorem cubicWeight_le_of_harris_pair_cell {n : ℕ} {ρ R η a b w M : ℝ}
    (hρ : 0 ≤ ρ) (hR : ρ ≤ R) (hη : η ∈ Set.Ioc (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (f : BooleanFunction n) (hf : Monotone (lift f))
    (i j : Fin n) (hij : i ≠ j)
    (hai : a ≤ fourier (lift f) {i}) (hbj : b ≤ fourier (lift f) {j})
    (hw : fourierWeight (lift f) 1 ≤ w)
    (hcell : w+cubicBeta R*((1-η^2)*w+η^2-a^2-(1-η)*b^2)/(η*(1+η)) ≤ M) :
    cubicWeight ρ f ≤ M := by
  have hv := secondLevel_le_of_harris_pair_cell hη ha hb f hf i j hij hai hbj hw
  have h := cubicWeight_le_beta_bound hρ hR f hw hv
  rw [← mul_div_assoc] at h
  exact h.trans hcell

theorem cubicWeight_le_of_harris_singleton_cell {n : ℕ} {ρ R η a w M : ℝ}
    (hρ : 0 ≤ ρ) (hR : ρ ≤ R) (hη : η ∈ Set.Ioc (0 : ℝ) 1)
    (ha : 0 ≤ a) (f : BooleanFunction n) (hf : Monotone (lift f)) (i : Fin n)
    (hai : a ≤ fourier (lift f) {i}) (hw : fourierWeight (lift f) 1 ≤ w)
    (hcell : w+cubicBeta R*((1-η^2)*w+η^2-a^2)/(η*(1+η)) ≤ M) :
    cubicWeight ρ f ≤ M := by
  have hv := secondLevel_le_of_harris_singleton_cell hη ha f hf i hai hw
  have h := cubicWeight_le_beta_bound hρ hR f hw hv
  rw [← mul_div_assoc] at h
  exact h.trans hcell

theorem information_le_phi_of_posteriorEntropy {n : ℕ} {ρ : ℝ}
    (f : BooleanFunction n) (hpost : signEntropy ρ ≤ posteriorEntropy ρ f) :
    information ρ f ≤ phi ρ := by
  have hm := sq_div_two_le_phi (mean_mem_Icc f)
  rw [information_eq_signEntropy_sub_posterior,signEntropy_eq_log_two_sub_phi]
  rw [signEntropy_eq_log_two_sub_phi] at hpost
  nlinarith only [hm,hpost,sq_nonneg (mean f)]

/-- A coefficient-cell dichotomy. The high-energy premise is a posterior
entropy bound, to be supplied by the proved profile clock. -/
theorem mutualInformation_le_phi_of_cell_dichotomy {n : ℕ} {ρ M w : ℝ}
    (hρ : ρ ∈ Set.Ico (0 : ℝ) 1) (hC : 0 < cubicC ρ M)
    (hgate : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      cubicKappa ρ M*(1-t)*(1+t-ρ^3) ≤ signEntropy t)
    (hcredit : cubicKappa ρ M*(1-ρ^3) ≤ 1/2)
    (f : BooleanFunction n)
    (hsmall : fourierWeight (lift f) 1 ≤ w → cubicWeight ρ f ≤ M)
    (hlarge : w ≤ fourierWeight (lift f) 1 → signEntropy ρ ≤ posteriorEntropy ρ f) :
    mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information ⟨hρ.1,hρ.2.le⟩]
  rcases le_total (fourierWeight (lift f) 1) w with h | h
  · exact information_le_phi_of_cubicWeight hρ hC hgate hcredit f (hsmall h)
  · exact information_le_phi_of_posteriorEntropy f (hlarge h)

end
end CK
