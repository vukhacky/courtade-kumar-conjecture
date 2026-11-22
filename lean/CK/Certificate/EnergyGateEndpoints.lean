module

public import CK.Certificate.EnergyGateLogs
public import CK.Low.EnergyGate

/-! Full scalar tangent gates obtained from exact rational logarithm enclosures.
These facts concern every t in [0,1]; the numerical tests certify the two
endpoints of the supporting tangent line, not samples of the entropy function. -/

@[expose] public section
set_option autoImplicit false
namespace CK.Certificate
noncomputable section

private theorem low_log_right : Real.log ((1+(39/100:ℝ))/2) = -Real.log (200/139:ℝ) := by
  rw [show (1+(39/100:ℝ))/2=(200/139:ℝ)⁻¹ by norm_num,Real.log_inv]

private theorem central_log_right : Real.log ((1+(829/1250:ℝ))/2) = -Real.log (2500/2079:ℝ) := by
  rw [show (1+(829/1250:ℝ))/2=(2500/2079:ℝ)⁻¹ by norm_num,Real.log_inv]

theorem energy_gate_low_endpoints :
    CK.energyChi (1425/1459) (9/25) (39/100) - (39/100)*CK.energyChiSlope (1425/1459) (39/100) ≤ 0 ∧
    CK.energyChi (1425/1459) (9/25) (39/100) + (1-39/100)*CK.energyChiSlope (1425/1459) (39/100) ≤ 0 := by
  have hl := EnergyLogs.log_low_left_bounds
  have hr := EnergyLogs.log_low_right_bounds
  rw [CK.energyChiSlope_eq,low_log_right]
  unfold CK.energyChi CK.signEntropy
  rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [hl.1,hl.2,hr.1,hr.2]

theorem energy_gate_central_endpoints :
    CK.energyChi (57/(76-49*(457/500:ℝ)^2)) ((457/500:ℝ)^2) (829/1250) -
      (829/1250)*CK.energyChiSlope (57/(76-49*(457/500:ℝ)^2)) (829/1250) ≤ 0 ∧
    CK.energyChi (57/(76-49*(457/500:ℝ)^2)) ((457/500:ℝ)^2) (829/1250) +
      (1-829/1250)*CK.energyChiSlope (57/(76-49*(457/500:ℝ)^2)) (829/1250) ≤ 0 := by
  have hl := EnergyLogs.log_central_left_bounds
  have hr := EnergyLogs.log_central_right_bounds
  rw [CK.energyChiSlope_eq,central_log_right]
  unfold CK.energyChi CK.signEntropy
  rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [hl.1,hl.2,hr.1,hr.2]

theorem entropy_gate_low {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (1425/1459:ℝ)*(1-t)*(1+t-9/25) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate (by norm_num : (39/100:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    energy_gate_low_endpoints.1 energy_gate_low_endpoints.2 t ht

theorem entropy_gate_central {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (57/(76-49*(457/500:ℝ)^2))*(1-t)*(1+t-(457/500:ℝ)^2) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate (by norm_num : (829/1250:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    energy_gate_central_endpoints.1 energy_gate_central_endpoints.2 t ht

end
end CK.Certificate
