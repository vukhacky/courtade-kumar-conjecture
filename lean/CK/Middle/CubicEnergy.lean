module

public import CK.Low.DegreeEnergy
public import CK.Low.EnergyGate
public import CK.Basic.ShannonBridge

/-! The cubic Fourier-energy criterion for CK, preserving the mean term.
The scalar entropy gate is an explicit reusable premise here; concrete
correlation bands discharge it in the endpoint-propagation module. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

def cubicBeta (ρ : ℝ) : ℝ := ρ^2/(1+ρ)
def cubicWeight {n : ℕ} (ρ : ℝ) (f : BooleanFunction n) : ℝ :=
  fourierWeight (lift f) 1 + cubicBeta ρ * fourierWeight (lift f) 2

def cubicC (ρ M : ℝ) : ℝ := 1+ρ+ρ^2-ρ^2*(1+ρ)*M
def cubicKappa (ρ M : ℝ) : ℝ := signEntropy ρ/((1-ρ)*cubicC ρ M)

theorem cubicBeta_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ cubicBeta ρ :=
  div_nonneg (sq_nonneg _) (by linarith)

theorem cubicBeta_mono {ρ σ : ℝ} (hρ : 0 ≤ ρ) (hσ : ρ ≤ σ) :
    cubicBeta ρ ≤ cubicBeta σ := by
  have hσ0 : 0 ≤ σ := hρ.trans hσ
  unfold cubicBeta
  apply (div_le_div_iff₀ (by linarith : 0 < 1+ρ) (by linarith : 0 < 1+σ)).mpr
  have h := mul_nonneg (sub_nonneg.mpr hσ) (show 0 ≤ σ+ρ+ρ*σ by positivity)
  nlinarith only [h]

theorem cubicBeta_le_one {ρ : ℝ} (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) : cubicBeta ρ ≤ 1 := by
  have h := cubicBeta_mono hρ.1 hρ.2
  norm_num [cubicBeta] at h
  change cubicBeta ρ ≤ 1/2 at h
  linarith

theorem degreeCorrection_three_eq_cubicWeight {n : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (f : BooleanFunction n) :
    degreeCorrection ρ 3 (lift f) = (ρ^2-ρ^4)*cubicWeight ρ f := by
  rw [degreeCorrection_three]
  unfold cubicWeight cubicBeta
  have hn : 1+ρ ≠ 0 := by linarith
  field_simp
  ring

theorem cubicKappa_nonneg {ρ M : ℝ} (hρ : ρ ∈ Set.Ico (0 : ℝ) 1)
    (hC : 0 < cubicC ρ M) : 0 ≤ cubicKappa ρ M := by
  exact div_nonneg (signEntropy_nonneg ⟨by linarith [hρ.1],hρ.2.le⟩)
    (mul_nonneg (by linarith [hρ.2]) hC.le)

theorem cubicKappa_normalization {ρ M : ℝ} (hρ : ρ < 1) (hC : 0 < cubicC ρ M) :
    cubicKappa ρ M*((1-ρ^3)-(ρ^2-ρ^4)*M) = signEntropy ρ := by
  have hid : (1-ρ^3)-(ρ^2-ρ^4)*M = (1-ρ)*cubicC ρ M := by
    unfold cubicC
    ring
  rw [hid, cubicKappa, div_mul_cancel₀ _ (mul_ne_zero (by linarith) hC.ne')]

/-- Bias-aware cubic energy budget, before the scalar prior-credit condition. -/
theorem information_cubic_budget {n : ℕ} {ρ M : ℝ}
    (hρ : ρ ∈ Set.Ico (0 : ℝ) 1) (hC : 0 < cubicC ρ M)
    (hgate : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      cubicKappa ρ M*(1-t)*(1+t-ρ^3) ≤ signEntropy t)
    (f : BooleanFunction n) (hweight : cubicWeight ρ f ≤ M) :
    phi (mean f)-cubicKappa ρ M*(1-ρ^3)*mean f^2 ≤ phi ρ-information ρ f := by
  have hc := cubicKappa_nonneg hρ hC
  have h := posteriorEntropy_ge_degree_gate ⟨hρ.1,hρ.2.le⟩ hc 3 hgate f
  rw [degreeCorrection_three_eq_cubicWeight hρ.1] at h
  have hd : 0 ≤ ρ^2-ρ^4 := by
    have hs : ρ^2 ≤ 1 := by nlinarith [hρ.1,hρ.2]
    nlinarith [mul_nonneg (sq_nonneg ρ) (sub_nonneg.mpr hs)]
  have hm := mul_le_mul_of_nonneg_left hweight (mul_nonneg hc hd)
  have hn := cubicKappa_normalization hρ.2 hC
  rw [information_eq_signEntropy_sub_posterior,signEntropy_eq_log_two_sub_phi]
  rw [signEntropy_eq_log_two_sub_phi] at hn
  nlinarith only [h,hm,hn]

theorem information_le_phi_of_cubicWeight {n : ℕ} {ρ M : ℝ}
    (hρ : ρ ∈ Set.Ico (0 : ℝ) 1) (hC : 0 < cubicC ρ M)
    (hgate : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      cubicKappa ρ M*(1-t)*(1+t-ρ^3) ≤ signEntropy t)
    (hcredit : cubicKappa ρ M*(1-ρ^3) ≤ 1/2)
    (f : BooleanFunction n) (hweight : cubicWeight ρ f ≤ M) :
    information ρ f ≤ phi ρ := by
  have h := information_cubic_budget hρ hC hgate f hweight
  have hm := mul_le_mul_of_nonneg_right hcredit (sq_nonneg (mean f))
  nlinarith only [h,hm,sq_div_two_le_phi (mean_mem_Icc f)]

theorem mutualInformation_le_phi_of_cubicWeight {n : ℕ} {ρ M : ℝ}
    (hρ : ρ ∈ Set.Ico (0 : ℝ) 1) (hC : 0 < cubicC ρ M)
    (hgate : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      cubicKappa ρ M*(1-t)*(1+t-ρ^3) ≤ signEntropy t)
    (hcredit : cubicKappa ρ M*(1-ρ^3) ≤ 1/2)
    (f : BooleanFunction n) (hweight : cubicWeight ρ f ≤ M) :
    mutualInformation ρ f ≤ phi ρ := by
  rw [mutualInformation_eq_information ⟨hρ.1,hρ.2.le⟩]
  exact information_le_phi_of_cubicWeight hρ hC hgate hcredit f hweight

end
end CK
