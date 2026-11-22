module

public import CK.Functional.PhiTaylor
public import CK.Low.Local

/-! Sound analytic bridge from exact rational Taylor-polynomial
certificates to the local entropy deficit on a whole correlation interval. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem localDeficit_eq_phi (ρ a : ℝ) :
    localDeficit ρ a = (a-1)*ρ^2*Real.log 2 +
      (1-a*ρ^2)*phi ρ - (1-ρ^2)*phi (a*ρ) := by
  unfold localDeficit
  simp only [signEntropy_eq_log_two_sub_phi]
  rw [mul_comm ρ a]
  ring

/-- Polynomial data are only a sufficient lower envelope; this theorem
proves the full real analytic comparison, with every denominator valid. -/
theorem localTaylorPolynomial_le_deficit (N M : ℕ) {a R L ρ : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) R) (hL : Real.log 2 ≤ L) :
    ρ^2*localTaylorPolynomial N M a R L (ρ^2) ≤ localDeficit ρ a := by
  have hρ1 : ρ ≤ 1 := by linarith [hρ.2]
  have hρsq : ρ^2 ≤ 1 := by nlinarith [hρ.1]
  have hra0 : 0 ≤ a*R := mul_nonneg ha.1 hR0
  have hra1 : a*R < 1 := by
    have h := mul_le_mul_of_nonneg_right ha.2 hR0
    nlinarith
  have harg : a*ρ ∈ Set.Icc (-(a*R)) (a*R) := by
    constructor
    · nlinarith [mul_nonneg ha.1 hρ.1]
    · exact mul_le_mul_of_nonneg_left hρ.2 ha.1
  have hlo := phiTaylor_le_phi N (show ρ ∈ Set.Icc (-1 : ℝ) 1 from ⟨by linarith [hρ.1],hρ1⟩)
  have hhi := phi_le_phiTaylor_bound M hra0 hra1 harg
  have hfactor : 0 ≤ 1-a*ρ^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) (sq_nonneg ρ)]
  have hlow := mul_le_mul_of_nonneg_left hlo hfactor
  have hupp := mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hρsq)
  have hlog := mul_le_mul_of_nonpos_left hL
    (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ha.2) (sq_nonneg ρ))
  rw [localTaylorPolynomial_identity,localDeficit_eq_phi]
  nlinarith only [hlow,hupp,hlog]

theorem localDeficit_nonneg_of_taylor (N M : ℕ) {a R L ρ : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 1) (hR0 : 0 ≤ R) (hR1 : R < 1)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) R) (hL : Real.log 2 ≤ L)
    (hpoly : 0 ≤ localTaylorPolynomial N M a R L (ρ^2)) :
    0 ≤ localDeficit ρ a :=
  (mul_nonneg (sq_nonneg ρ) hpoly).trans
    (localTaylorPolynomial_le_deficit N M ha hR0 hR1 hρ hL)

end
end CK
