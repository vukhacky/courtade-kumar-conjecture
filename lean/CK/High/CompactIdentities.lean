module

public import CK.High.CompactParameters
public import CK.High.CostMajorants
public import CK.Certificate.CompactScalar

/-! Correspondence between the compact verifier variables and the entropy and profile quantities in the spectral theorem. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section
open Certificate

theorem compact_scalar_z (u : ℝ) : Compact.z u=compactZ u := rfl
theorem compact_scalar_t (u : ℝ) : Compact.t u=compactT u := rfl
theorem compact_scalar_cap (u : ℝ) : Compact.cap u=compactAlpha u := rfl
theorem compact_scalar_top (u : ℝ) : Compact.top u=compactTop u := rfl
theorem compact_scalar_P : Compact.P=Real.pi^2/4 := rfl
theorem compact_scalar_CS : Compact.CS=arcsineSharpConstant := rfl

theorem compact_q_pos (u : ℝ) : 0 < Compact.q u := Real.exp_pos _
theorem compact_R_pos (u : ℝ) : 0 < Compact.R u := by unfold Compact.R; positivity

theorem compact_scalar_rho (u : ℝ) : Compact.rho u=Real.tanh u := by
  exact (tanh_eq_heightExpParameter u).symm

theorem compact_raw_entropy (u : ℝ) :
    Compact.q u*Compact.raw u=Profile.meanEntropy (Real.tanh u) := by
  rw [meanEntropy_tanh_exp_formula]
  unfold Compact.raw Compact.q heightExpParameter
  have hp : 0 < 1+Real.exp (-2*u) := by positivity
  field_simp [hp.ne',Real.exp_ne_zero]
  <;> ring

theorem compact_raw_pos {u : ℝ} (hu : 0 < u) : 0 < Compact.raw u := by
  have ht := tanh_mem_Ioo_positive hu
  have hH := Profile.meanEntropy_pos ⟨by linarith [ht.1],ht.2⟩
  rw [←compact_raw_entropy] at hH
  exact (mul_pos_iff_of_pos_left (compact_q_pos u)).mp hH

theorem compact_scalar_F (u : ℝ) : Compact.F u=heightF u := by
  unfold Compact.F heightF
  rw [compact_raw_entropy,compact_scalar_rho]

theorem compact_scalar_d (u : ℝ) : Compact.d u=1-Real.tanh u^2 := by
  rw [←compact_scalar_rho]
  unfold Compact.d Compact.rho
  have hp : 0 < 1+Compact.q u := by have := compact_q_pos u; positivity
  field_simp [hp.ne']
  <;> ring

theorem compact_scalar_psi (u : ℝ) :
    Compact.q u*Compact.psi u=entropyRemainder (Real.tanh u) := by
  calc
    Compact.q u*Compact.psi u = Compact.q u*Compact.raw u-Compact.d u*Real.log 2 := by
      unfold Compact.psi Compact.d Compact.L
      ring
    _ = Profile.meanEntropy (Real.tanh u)-(1-Real.tanh u^2)*Real.log 2 := by
      rw [compact_raw_entropy,compact_scalar_d]
    _ = entropyRemainder (Real.tanh u) := by
      unfold entropyRemainder phi Profile.meanEntropy
      ring

theorem compact_gamma_factor (u : ℝ) :
    compactGamma u=Real.exp (9*u/20+1/4)*(1+Compact.R u) := by
  have h : Real.exp (9*u/20+1/4)*(Real.exp (53*u/100-9/20)/2)=
      Real.exp (49*u/50-1/5)/2 := by
    rw [←mul_div_assoc,←Real.exp_add]
    congr 2
    ring
  unfold compactGamma Compact.R
  rw [←h]
  ring

theorem compact_scalar_w (u : ℝ) : Compact.w u=1/compactGamma u := by
  have hR : 0 < 1+Compact.R u := by have := compact_R_pos u; positivity
  unfold Compact.w
  rw [compact_gamma_factor,show -9*u/20-1/4=-(9*u/20+1/4) by ring,Real.exp_neg]
  field_simp [hR.ne',Real.exp_ne_zero]

theorem compact_scaled_gamma (u : ℝ) : Compact.G u=Compact.q u*compactGamma u := by
  unfold Compact.G Compact.first Compact.extra Compact.q compactGamma
  simp only [mul_add,←mul_div_assoc,←Real.exp_add]
  ring_nf

theorem compact_scaled_extra (u : ℝ) :
    Compact.extra u=Compact.q u*Real.exp (9*u/20+1/4) := by
  unfold Compact.extra Compact.q
  rw [←Real.exp_add]
  congr 1
  ring

theorem compact_G_factor (u : ℝ) : Compact.G u=Compact.extra u*(1+Compact.R u) := by
  rw [compact_scaled_gamma,compact_gamma_factor,←mul_assoc,←compact_scaled_extra]

theorem compact_invBase_gamma (u : ℝ) :
    Real.exp (-9*u/20-1/4)*compactGamma u=1+Compact.R u := by
  rw [compact_gamma_factor,←mul_assoc,←Real.exp_add]
  rw [show -9*u/20-1/4+(9*u/20+1/4)=0 by ring,Real.exp_zero,one_mul]

theorem compact_scaled_first (u : ℝ) :
    Compact.first u=Compact.q u*(Real.exp (2*compactT u-3)/2) := by
  unfold Compact.first Compact.q compactT
  rw [←mul_div_assoc,←Real.exp_add]
  congr 2
  ring

theorem compact_gamma_minus_first (u : ℝ) :
    compactGamma u-Real.exp (2*compactT u-3)/2=Real.exp (9*u/20+1/4) := by
  have he : 2*compactT u-3=49*u/50-1/5 := by unfold compactT; ring
  rw [he,compactGamma]
  ring

end
end CK
