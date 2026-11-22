module

public import CK.Low.EnergyGate
public import CK.Low.DegreeEnergy
public import CK.Low.Contraction
public import CK.Certificate.EnergyGateEndpoints
public import CK.Certificate.EnergyPolynomial

/-! Central quadratic-energy bounds. The finite Taylor lower bound and a rational polynomial certificate give positivity throughout the interval. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def centralEnergyFactor (ρ : ℝ) : ℝ := 57/(76-49*ρ^2)

theorem centralEnergy_denominator_pos {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    0 < 76-49*ρ^2 := by
  have hs : ρ^2 ≤ 1 := by nlinarith [hρ.1,hρ.2]
  nlinarith

theorem centralEnergyFactor_pos {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) :
    0 < centralEnergyFactor ρ := div_pos (by norm_num) (centralEnergy_denominator_pos hρ)

theorem quadratic_gate_of_endpoints
    (hlo : ∀ t ∈ Icc (0 : ℝ) 1,
      centralEnergyFactor (3/5)*(1-t)*(1+t-(3/5)^2) ≤ signEntropy t)
    (hhi : ∀ t ∈ Icc (0 : ℝ) 1,
      centralEnergyFactor (457/500)*(1-t)*(1+t-(457/500)^2) ≤ signEntropy t)
    {ρ : ℝ} (hρ : ρ ∈ Icc (3/5 : ℝ) (457/500)) :
    ∀ t ∈ Icc (0 : ℝ) 1, centralEnergyFactor ρ*(1-t)*(1+t-ρ^2) ≤ signEntropy t := by
  intro t ht
  have hρ01 : ρ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hb0 : (3/5 : ℝ)^2 ≤ ρ^2 := by nlinarith [hρ.1]
  have hb1 : ρ^2 ≤ (457/500 : ℝ)^2 := by nlinarith [hρ01.1,hρ.2]
  have hl := hlo t ht
  have hh := hhi t ht
  norm_num [centralEnergyFactor] at hl hh
  have hL : 57*(1-t)*(1+t-(3/5 : ℝ)^2) ≤ (76-49*(3/5 : ℝ)^2)*signEntropy t := by
    nlinarith only [hl]
  have hH : 57*(1-t)*(1+t-(457/500 : ℝ)^2) ≤ (76-49*(457/500 : ℝ)^2)*signEntropy t := by
    nlinarith only [hh]
  have hmid : 57*(1-t)*(1+t-ρ^2) ≤ (76-49*ρ^2)*signEntropy t := by
    by_cases hs : 0 ≤ 57*(1-t)-49*signEntropy t
    · have hm := mul_nonneg (sub_nonneg.mpr hb0) hs
      nlinarith only [hL,hm]
    · have hm := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hb1) (le_of_not_ge hs)
      nlinarith only [hH,hm]
  have heq : centralEnergyFactor ρ*(1-t)*(1+t-ρ^2) =
      (57*(1-t)*(1+t-ρ^2))/(76-49*ρ^2) := by unfold centralEnergyFactor; ring
  rw [heq]
  exact (div_le_iff₀ (centralEnergy_denominator_pos hρ01)).mpr (by nlinarith only [hmid])

theorem central_mean_coefficient_le {ρ : ℝ} (hρ : ρ ∈ Icc (3/5 : ℝ) 1) :
    centralEnergyFactor ρ*(1-2*ρ^2+ρ^3) ≤ 49/100 := by
  have hρ01 : ρ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hρ.1],hρ.2⟩
  have hsq : ρ^2 ≤ ρ := by nlinarith [mul_nonneg hρ01.1 (sub_nonneg.mpr hρ.2)]
  have hk : 0 ≤ 8999*(ρ+3/5)-5700*(ρ^2+(3/5)*ρ+9/25) := by
    nlinarith only [hsq,hρ.2]
  have hp := mul_nonneg (sub_nonneg.mpr hρ.1) hk
  have hpoly : 57*(1-2*ρ^2+ρ^3) ≤ (49/100)*(76-49*ρ^2) := by nlinarith only [hp]
  have heq : centralEnergyFactor ρ*(1-2*ρ^2+ρ^3) =
      (57*(1-2*ρ^2+ρ^3))/(76-49*ρ^2) := by unfold centralEnergyFactor; ring
  rw [heq]
  exact (div_le_iff₀ (centralEnergy_denominator_pos hρ01)).mpr hpoly

theorem central_mean_correction {ρ μ : ℝ} (hρ : ρ ∈ Icc (3/5 : ℝ) 1)
    (hμ : μ ∈ Icc (-1 : ℝ) 1) :
    μ^2/100 ≤ phi μ-centralEnergyFactor ρ*(1-2*ρ^2+ρ^3)*μ^2 := by
  have h := mul_le_mul_of_nonneg_right (central_mean_coefficient_le hρ) (sq_nonneg μ)
  nlinarith only [h,sq_div_two_le_phi hμ]

theorem central_energy_of_polynomial (N : ℕ) {L ρ : ℝ}
    (hL : Real.log 2 ≤ L) (hρ : ρ ∈ Icc (0 : ℝ) (457/500))
    (hpoly : 0 < (1-ρ)*(1+ρ-(193027/250000)*ρ^2) -
      ((76-49*ρ^2)/57)*(L-phiTaylor N ρ)) :
    0 < centralEnergyFactor ρ*((1-ρ^2)-ρ^2*(1-ρ)*(193027/250000)) - signEntropy ρ := by
  have hρ01 : ρ ∈ Icc (0 : ℝ) 1 := ⟨hρ.1,by linarith [hρ.2]⟩
  have hden := centralEnergy_denominator_pos hρ01
  have ht := phiTaylor_le_phi N (show ρ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hρ.1],hρ01.2⟩)
  have hH : signEntropy ρ ≤ L-phiTaylor N ρ := by
    rw [signEntropy_eq_log_two_sub_phi]
    linarith only [hL,ht]
  have hmul := mul_le_mul_of_nonneg_left hH (div_nonneg hden.le (by norm_num : (0 : ℝ) ≤ 57))
  have hstrong : (76-49*ρ^2)*signEntropy ρ <
      57*((1-ρ^2)-ρ^2*(1-ρ)*(193027/250000)) := by
    nlinarith only [hpoly,hmul]
  apply sub_pos.mpr
  have heq : centralEnergyFactor ρ*((1-ρ^2)-ρ^2*(1-ρ)*(193027/250000)) =
      (57*((1-ρ^2)-ρ^2*(1-ρ)*(193027/250000)))/(76-49*ρ^2) := by
    unfold centralEnergyFactor
    ring
  rw [heq]
  exact (lt_div_iff₀ hden).mpr (by nlinarith only [hstrong])

theorem central_entropy_gate {ρ : ℝ} (hρ : ρ ∈ Icc (3/5 : ℝ) (457/500)) :
    ∀ t ∈ Icc (0 : ℝ) 1,
      centralEnergyFactor ρ*(1-t)*(1+t-ρ^2) ≤ signEntropy t := by
  apply quadratic_gate_of_endpoints
  · intro t ht
    simpa only [centralEnergyFactor, show (3/5 : ℝ)^2 = 9/25 by norm_num,
      show (57 : ℝ)/(76-49*(9/25)) = 1425/1459 by norm_num]
      using Certificate.entropy_gate_low ht
  · intro t ht
    exact Certificate.entropy_gate_central ht
  · exact hρ

theorem central_energy_positive {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) (457/500)) :
    0 < centralEnergyFactor ρ*((1-ρ^2)-ρ^2*(1-ρ)*(193027/250000)) - signEntropy ρ :=
  central_energy_of_polynomial 24 Certificate.EnergyPolynomial.log_two_le hρ
    (Certificate.EnergyPolynomial.central_energy_polynomial_pos hρ)

theorem information_lt_phi_central_of_cap {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (3/5 : ℝ) (457/500)) (f : BooleanFunction n)
    (hcap : fourierWeight (lift f) 1 + mean f^2 ≤ 193027/250000) :
    information ρ f < phi ρ := by
  have hρ01 : ρ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hbudget := quadratic_information_budget hρ01 (centralEnergyFactor_pos hρ01).le
    (central_entropy_gate hρ) f hcap
  have hconstant := central_energy_positive ⟨hρ01.1,hρ.2⟩
  have hmean := central_mean_correction ⟨hρ.1,hρ01.2⟩ (mean_mem_Icc f)
  nlinarith only [hbudget,hconstant,hmean,sq_nonneg (mean f)]

theorem information_three_fifths_lt_of_cap {n : ℕ} (f : BooleanFunction n)
    (hcap : fourierWeight (lift f) 1 + mean f^2 ≤ 193027/250000) :
    information (3/5) f < 9/50 := by
  have hρ : (3/5 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hbudget := quadratic_information_budget hρ (centralEnergyFactor_pos hρ).le
    (central_entropy_gate (by norm_num)) f hcap
  have hmean := central_mean_correction (show (3/5 : ℝ) ∈ Icc (3/5 : ℝ) 1 by norm_num)
    (mean_mem_Icc f)
  have hlog := Certificate.EnergyPolynomial.log_two_le
  rw [signEntropy_eq_log_two_sub_phi] at hbudget
  norm_num [centralEnergyFactor] at hbudget hmean
  nlinarith only [hbudget,hmean,hlog,sq_nonneg (mean f)]

theorem information_le_phi_small_of_cap {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Icc (0 : ℝ) (3/5)) (f : BooleanFunction n)
    (hcap : fourierWeight (lift f) 1 + mean f^2 ≤ 193027/250000) :
    information ρ f ≤ phi ρ := by
  have hη : ρ/(3/5) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> nlinarith [hρ.1,hρ.2]
  have h := information_contraction hη (show (3/5 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) f
  rw [div_mul_cancel₀ _ (by norm_num : (3/5 : ℝ) ≠ 0)] at h
  have hm := mul_le_mul_of_nonneg_left (information_three_fifths_lt_of_cap f hcap).le
    (sq_nonneg (ρ/(3/5)))
  have hphi := sq_div_two_le_phi (show ρ ∈ Icc (-1 : ℝ) 1 from
    ⟨by linarith [hρ.1],by linarith [hρ.2]⟩)
  nlinarith only [h,hm,hphi]

end
end CK
