module

public import CK.High.Compact
public import CK.High.CompactIdentities
public import CK.High.TailLosses

/-! The cleared compact master margin is exactly a positive factor times
the gap between the spectral numerator and the discarded-coordinate cost. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section
open Certificate

def compactInvBase (u : ℝ) : ℝ := Real.exp (-9*u/20-1/4)
def compactMasterD (u : ℝ) : ℝ := 1+Compact.R u+Compact.t u*compactInvBase u
def compactMasterE (u : ℝ) : ℝ := 1+Compact.t u*compactInvBase u
def compactMasterFactor (u : ℝ) : ℝ :=
  compactMasterD u*compactMasterE u*Compact.z u*Compact.F (Compact.z u)

theorem compactInvBase_pos (u : ℝ) : 0 < compactInvBase u := Real.exp_pos _

theorem compactMasterD_eq (u : ℝ) :
    compactMasterD u=compactInvBase u*(compactGamma u+compactT u) := by
  unfold compactMasterD
  rw [←compact_invBase_gamma,compact_scalar_t]
  unfold compactInvBase
  ring

theorem compactInvBase_gap (u : ℝ) :
    compactInvBase u*(compactGamma u-Real.exp (2*compactT u-3)/2)=1 := by
  rw [compact_gamma_minus_first]
  unfold compactInvBase
  rw [←Real.exp_add,show -9*u/20-1/4+(9*u/20+1/4)=0 by ring,Real.exp_zero]

theorem compactMasterE_eq (u : ℝ) :
    compactMasterE u=compactInvBase u*(compactGamma u+compactT u-
      Real.exp (2*compactT u-3)/2) := by
  unfold compactMasterE
  rw [←compactInvBase_gap,compact_scalar_t]
  ring

theorem compactMasterFactor_pos {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    0 < compactMasterFactor u := by
  have ht : 0 < Compact.t u := by rw [compact_scalar_t]; linarith [(compact_parameter_domains hu).1]
  have hz : 0 < Compact.z u := by rw [compact_scalar_z]; exact (compactZ_bounds hu).1
  have hF : 0 < Compact.F (Compact.z u) := by rw [compact_scalar_F]; exact heightF_pos hz
  have ha := compactInvBase_pos u
  have hR := compact_R_pos u
  unfold compactMasterFactor compactMasterD compactMasterE
  positivity

theorem compact_multiplier_masterD {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    shiftedMultiplier (compactGamma u) (compactT u)*compactMasterD u =
      Compact.t u*(1+Compact.R u) := by
  have hg := compactGamma_pos u
  have ht := (compact_parameter_domains hu).1
  have hgt : compactGamma u+compactT u ≠ 0 := by linarith
  rw [compactMasterD_eq,compact_scalar_t,←compact_invBase_gamma]
  unfold shiftedMultiplier compactInvBase
  field_simp [hgt]
  <;> ring

theorem compact_numerator_masterD {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    compactNumerator u*compactMasterD u =
      Compact.P*Compact.t u*Compact.rho u^2*(1+Compact.R u)-
        Compact.extra u*compactMasterD u*(1+Compact.R u)*Compact.CS*Compact.psi u := by
  have hE : Compact.extra u*compactMasterD u*(1+Compact.R u)*Compact.CS*Compact.psi u =
      compactGamma u*arcsineSharpConstant*entropyRemainder (Real.tanh u)*compactMasterD u := by
    calc
      _ = (Compact.extra u*(1+Compact.R u))*Compact.CS*(Compact.psi u*compactMasterD u) := by ring
      _ = (Compact.q u*compactGamma u)*Compact.CS*(Compact.psi u*compactMasterD u) := by
        rw [←compact_G_factor,compact_scaled_gamma]
      _ = _ := by rw [←compact_scalar_psi,←compact_scalar_CS]; ring
  rw [hE,compact_scalar_P,compact_scalar_rho]
  unfold compactNumerator spectralNumerator
  have hm := compact_multiplier_masterD hu
  calc
    _ = (Real.pi^2/4)*Real.tanh u^2*
        (shiftedMultiplier (compactGamma u) (compactT u)*compactMasterD u)-
        compactGamma u*arcsineSharpConstant*entropyRemainder (Real.tanh u)*compactMasterD u := by ring
    _ = _ := by rw [hm]; ring

theorem compact_tau_clearing_algebra {γ t b r q h a z Fz : ℝ}
    (hgt : γ+t ≠ 0) (hgtb : γ+t-b ≠ 0) (hz : z ≠ 0)
    (hFz : Fz ≠ 0) (hr : r ≠ 0) :
    ((γ^2*b/((γ+t)*(γ+t-b)))*r^2*(q*h/r/Fz)/z)*
        ((a*(γ+t))*(a*(γ+t-b))*z*Fz) =
      (q*b)*(a*γ)^2*r*h := by
  field_simp [hgt,hgtb,hz,hFz,hr]
  <;> ring

theorem compact_tau_masterFactor {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    spectralTau (compactGamma u) (compactT u) (Real.tanh u) (compactZ u)*
      compactMasterFactor u =
        Compact.first u*(1+Compact.R u)^2*Compact.rho u*Compact.raw u := by
  have hu0 : 0 < u := by linarith only [hu]
  have hz := (compactZ_bounds hu).1
  have hfz := heightF_pos hz
  have hr := (tanh_mem_Ioo_positive hu0).1
  have hg := compactGamma_pos u
  have ht := (compact_parameter_domains hu).1
  have hgt : compactGamma u+compactT u ≠ 0 := by linarith
  have hgap : 0 < compactGamma u-Real.exp (2*compactT u-3)/2 := by
    rw [compact_gamma_minus_first]; exact Real.exp_pos _
  have hgtb : compactGamma u+compactT u-Real.exp (2*compactT u-3)/2 ≠ 0 := by linarith
  unfold spectralTau spectralDeltaOutside compactMasterFactor
  rw [shiftedMultiplier_drop_identity hgt hgtb,profileCoefficient_tanh_eq hu0 hz,
    compactMasterD_eq,compactMasterE_eq,compact_scalar_z,compact_scalar_F,
    ←compact_scalar_F u]
  unfold Compact.F
  rw [compact_scaled_first,←compact_invBase_gamma,compact_scalar_rho]
  unfold compactInvBase
  exact compact_tau_clearing_algebra hgt hgtb hz.ne' hfz.ne' hr.ne'

theorem compact_master_factorization {u : ℝ} (hu : (9/4 : ℝ) ≤ u) :
    Compact.master u=(compactNumerator u-u*compactDiscardedCost u)*compactMasterFactor u := by
  calc
    Compact.master u = (compactNumerator u*compactMasterD u-
        Compact.rho u*u*compactMasterD u)*compactMasterE u*Compact.z u*Compact.F (Compact.z u)-
        Compact.P*Compact.first u*(1+Compact.R u)^2*Compact.rho u*Compact.raw u*u := by
      rw [compact_numerator_masterD hu]
      rfl
    _ = (compactNumerator u-u*Compact.rho u)*compactMasterFactor u-
        u*Compact.P*(Compact.first u*(1+Compact.R u)^2*Compact.rho u*Compact.raw u) := by
      unfold compactMasterFactor
      ring
    _ = (compactNumerator u-u*Compact.rho u)*compactMasterFactor u-
        u*Compact.P*(spectralTau (compactGamma u) (compactT u) (Real.tanh u) (compactZ u)*
          compactMasterFactor u) := by rw [compact_tau_masterFactor hu]
    _ = _ := by
      unfold compactDiscardedCost
      rw [compact_scalar_rho,compact_scalar_P]
      ring

theorem compact_discarded_of_master {u : ℝ} (hu : (9/4 : ℝ) ≤ u)
    (hmaster : 0 < Compact.master u) : compactDiscardedCost u < compactNumerator u/u := by
  have hu0 : 0 < u := by linarith only [hu]
  rw [compact_master_factorization hu] at hmaster
  have h := (mul_pos_iff_of_pos_right (compactMasterFactor_pos hu)).mp hmaster
  apply (lt_div_iff₀ hu0).mpr
  nlinarith only [h]

end
end CK
