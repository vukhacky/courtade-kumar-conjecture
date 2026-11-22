module
public import CK.Certificate.CubicEndpointLogs
public import CK.Middle.CubicEnergy
public import CK.Low.EnergyGate

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace CK.Certificate.CubicEndpointGates
noncomputable section

theorem band0_lower_endpoints :
    CK.energyChi (CK.cubicKappa (457/500) (20630961/25000000)) ((457/500:ℝ)^3) (614956673117/1000000000000)-(614956673117/1000000000000)*CK.energyChiSlope (CK.cubicKappa (457/500) (20630961/25000000)) (614956673117/1000000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (457/500) (20630961/25000000)) ((457/500:ℝ)^3) (614956673117/1000000000000)+(1-(614956673117/1000000000000))*CK.energyChiSlope (CK.cubicKappa (457/500) (20630961/25000000)) (614956673117/1000000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log00
  have h1 := CubicEndpointLogs.log01
  have h2 := CubicEndpointLogs.log02
  have h3 := CubicEndpointLogs.log03
  have hlog : Real.log ((1+(614956673117/1000000000000:ℝ))/2) = -Real.log (2000000000000/1614956673117:ℝ) := by
    rw [show (1+(614956673117/1000000000000:ℝ))/2=(2000000000000/1614956673117:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band0_lower {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (457/500) (20630961/25000000))*(1-t)*(1+t-((457/500:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (614956673117/1000000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band0_lower_endpoints.1 band0_lower_endpoints.2 t ht

theorem band0_upper_endpoints :
    CK.energyChi (CK.cubicKappa (19/20) (20630961/25000000)) ((19/20:ℝ)^3) (67305817327/100000000000)-(67305817327/100000000000)*CK.energyChiSlope (CK.cubicKappa (19/20) (20630961/25000000)) (67305817327/100000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (19/20) (20630961/25000000)) ((19/20:ℝ)^3) (67305817327/100000000000)+(1-(67305817327/100000000000))*CK.energyChiSlope (CK.cubicKappa (19/20) (20630961/25000000)) (67305817327/100000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log04
  have h1 := CubicEndpointLogs.log05
  have h2 := CubicEndpointLogs.log06
  have h3 := CubicEndpointLogs.log07
  have hlog : Real.log ((1+(67305817327/100000000000:ℝ))/2) = -Real.log (200000000000/167305817327:ℝ) := by
    rw [show (1+(67305817327/100000000000:ℝ))/2=(200000000000/167305817327:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band0_upper {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (19/20) (20630961/25000000))*(1-t)*(1+t-((19/20:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (67305817327/100000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band0_upper_endpoints.1 band0_upper_endpoints.2 t ht

theorem band1_lower_endpoints :
    CK.energyChi (CK.cubicKappa (19/20) (24615813/31250000)) ((19/20:ℝ)^3) (327962758093/500000000000)-(327962758093/500000000000)*CK.energyChiSlope (CK.cubicKappa (19/20) (24615813/31250000)) (327962758093/500000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (19/20) (24615813/31250000)) ((19/20:ℝ)^3) (327962758093/500000000000)+(1-(327962758093/500000000000))*CK.energyChiSlope (CK.cubicKappa (19/20) (24615813/31250000)) (327962758093/500000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log04
  have h1 := CubicEndpointLogs.log05
  have h2 := CubicEndpointLogs.log08
  have h3 := CubicEndpointLogs.log09
  have hlog : Real.log ((1+(327962758093/500000000000:ℝ))/2) = -Real.log (1000000000000/827962758093:ℝ) := by
    rw [show (1+(327962758093/500000000000:ℝ))/2=(1000000000000/827962758093:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band1_lower {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (19/20) (24615813/31250000))*(1-t)*(1+t-((19/20:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (327962758093/500000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band1_lower_endpoints.1 band1_lower_endpoints.2 t ht

theorem band1_upper_endpoints :
    CK.energyChi (CK.cubicKappa (97/100) (24615813/31250000)) ((97/100:ℝ)^3) (348495149563/500000000000)-(348495149563/500000000000)*CK.energyChiSlope (CK.cubicKappa (97/100) (24615813/31250000)) (348495149563/500000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (97/100) (24615813/31250000)) ((97/100:ℝ)^3) (348495149563/500000000000)+(1-(348495149563/500000000000))*CK.energyChiSlope (CK.cubicKappa (97/100) (24615813/31250000)) (348495149563/500000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log10
  have h1 := CubicEndpointLogs.log11
  have h2 := CubicEndpointLogs.log12
  have h3 := CubicEndpointLogs.log13
  have hlog : Real.log ((1+(348495149563/500000000000:ℝ))/2) = -Real.log (1000000000000/848495149563:ℝ) := by
    rw [show (1+(348495149563/500000000000:ℝ))/2=(1000000000000/848495149563:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band1_upper {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (97/100) (24615813/31250000))*(1-t)*(1+t-((97/100:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (348495149563/500000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band1_upper_endpoints.1 band1_upper_endpoints.2 t ht

theorem band2_lower_endpoints :
    CK.energyChi (CK.cubicKappa (97/100) (77592593/100000000)) ((97/100:ℝ)^3) (691989933291/1000000000000)-(691989933291/1000000000000)*CK.energyChiSlope (CK.cubicKappa (97/100) (77592593/100000000)) (691989933291/1000000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (97/100) (77592593/100000000)) ((97/100:ℝ)^3) (691989933291/1000000000000)+(1-(691989933291/1000000000000))*CK.energyChiSlope (CK.cubicKappa (97/100) (77592593/100000000)) (691989933291/1000000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log10
  have h1 := CubicEndpointLogs.log11
  have h2 := CubicEndpointLogs.log14
  have h3 := CubicEndpointLogs.log15
  have hlog : Real.log ((1+(691989933291/1000000000000:ℝ))/2) = -Real.log (2000000000000/1691989933291:ℝ) := by
    rw [show (1+(691989933291/1000000000000:ℝ))/2=(2000000000000/1691989933291:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band2_lower {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (97/100) (77592593/100000000))*(1-t)*(1+t-((97/100:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (691989933291/1000000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band2_lower_endpoints.1 band2_lower_endpoints.2 t ht

theorem band2_upper_endpoints :
    CK.energyChi (CK.cubicKappa (487/500) (77592593/100000000)) ((487/500:ℝ)^3) (5482545249/7812500000)-(5482545249/7812500000)*CK.energyChiSlope (CK.cubicKappa (487/500) (77592593/100000000)) (5482545249/7812500000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (487/500) (77592593/100000000)) ((487/500:ℝ)^3) (5482545249/7812500000)+(1-(5482545249/7812500000))*CK.energyChiSlope (CK.cubicKappa (487/500) (77592593/100000000)) (5482545249/7812500000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log16
  have h1 := CubicEndpointLogs.log17
  have h2 := CubicEndpointLogs.log18
  have h3 := CubicEndpointLogs.log19
  have hlog : Real.log ((1+(5482545249/7812500000:ℝ))/2) = -Real.log (15625000000/13295045249:ℝ) := by
    rw [show (1+(5482545249/7812500000:ℝ))/2=(15625000000/13295045249:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band2_upper {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (487/500) (77592593/100000000))*(1-t)*(1+t-((487/500:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (5482545249/7812500000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band2_upper_endpoints.1 band2_upper_endpoints.2 t ht

theorem band3_lower_endpoints :
    CK.energyChi (CK.cubicKappa (487/500) (772609873/1000000000)) ((487/500:ℝ)^3) (175096972269/250000000000)-(175096972269/250000000000)*CK.energyChiSlope (CK.cubicKappa (487/500) (772609873/1000000000)) (175096972269/250000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (487/500) (772609873/1000000000)) ((487/500:ℝ)^3) (175096972269/250000000000)+(1-(175096972269/250000000000))*CK.energyChiSlope (CK.cubicKappa (487/500) (772609873/1000000000)) (175096972269/250000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log16
  have h1 := CubicEndpointLogs.log17
  have h2 := CubicEndpointLogs.log20
  have h3 := CubicEndpointLogs.log21
  have hlog : Real.log ((1+(175096972269/250000000000:ℝ))/2) = -Real.log (500000000000/425096972269:ℝ) := by
    rw [show (1+(175096972269/250000000000:ℝ))/2=(500000000000/425096972269:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band3_lower {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (487/500) (772609873/1000000000))*(1-t)*(1+t-((487/500:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (175096972269/250000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band3_lower_endpoints.1 band3_lower_endpoints.2 t ht

theorem band3_upper_endpoints :
    CK.energyChi (CK.cubicKappa (39/40) (772609873/1000000000)) ((39/40:ℝ)^3) (175739726977/250000000000)-(175739726977/250000000000)*CK.energyChiSlope (CK.cubicKappa (39/40) (772609873/1000000000)) (175739726977/250000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (39/40) (772609873/1000000000)) ((39/40:ℝ)^3) (175739726977/250000000000)+(1-(175739726977/250000000000))*CK.energyChiSlope (CK.cubicKappa (39/40) (772609873/1000000000)) (175739726977/250000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log22
  have h1 := CubicEndpointLogs.log23
  have h2 := CubicEndpointLogs.log24
  have h3 := CubicEndpointLogs.log25
  have hlog : Real.log ((1+(175739726977/250000000000:ℝ))/2) = -Real.log (500000000000/425739726977:ℝ) := by
    rw [show (1+(175739726977/250000000000:ℝ))/2=(500000000000/425739726977:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band3_upper {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (39/40) (772609873/1000000000))*(1-t)*(1+t-((39/40:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (175739726977/250000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band3_upper_endpoints.1 band3_upper_endpoints.2 t ht

theorem band4_lower_endpoints :
    CK.energyChi (CK.cubicKappa (39/40) (150614067/200000000)) ((39/40:ℝ)^3) (694865634831/1000000000000)-(694865634831/1000000000000)*CK.energyChiSlope (CK.cubicKappa (39/40) (150614067/200000000)) (694865634831/1000000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (39/40) (150614067/200000000)) ((39/40:ℝ)^3) (694865634831/1000000000000)+(1-(694865634831/1000000000000))*CK.energyChiSlope (CK.cubicKappa (39/40) (150614067/200000000)) (694865634831/1000000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log22
  have h1 := CubicEndpointLogs.log23
  have h2 := CubicEndpointLogs.log26
  have h3 := CubicEndpointLogs.log27
  have hlog : Real.log ((1+(694865634831/1000000000000:ℝ))/2) = -Real.log (2000000000000/1694865634831:ℝ) := by
    rw [show (1+(694865634831/1000000000000:ℝ))/2=(2000000000000/1694865634831:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band4_lower {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (39/40) (150614067/200000000))*(1-t)*(1+t-((39/40:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (694865634831/1000000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band4_lower_endpoints.1 band4_lower_endpoints.2 t ht

theorem band4_upper_endpoints :
    CK.energyChi (CK.cubicKappa (49/50) (150614067/200000000)) ((49/50:ℝ)^3) (708918499749/1000000000000)-(708918499749/1000000000000)*CK.energyChiSlope (CK.cubicKappa (49/50) (150614067/200000000)) (708918499749/1000000000000) ≤ 0 ∧
    CK.energyChi (CK.cubicKappa (49/50) (150614067/200000000)) ((49/50:ℝ)^3) (708918499749/1000000000000)+(1-(708918499749/1000000000000))*CK.energyChiSlope (CK.cubicKappa (49/50) (150614067/200000000)) (708918499749/1000000000000) ≤ 0 := by
  have h0 := CubicEndpointLogs.log28
  have h1 := CubicEndpointLogs.log29
  have h2 := CubicEndpointLogs.log30
  have h3 := CubicEndpointLogs.log31
  have hlog : Real.log ((1+(708918499749/1000000000000:ℝ))/2) = -Real.log (2000000000000/1708918499749:ℝ) := by
    rw [show (1+(708918499749/1000000000000:ℝ))/2=(2000000000000/1708918499749:ℝ)⁻¹ by norm_num,Real.log_inv]
  rw [CK.energyChiSlope_eq,hlog]
  unfold CK.energyChi CK.cubicKappa CK.cubicC CK.signEntropy
  simp_rw [binEntropy_eq_log_inv]
  norm_num
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2]

theorem band4_upper {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (CK.cubicKappa (49/50) (150614067/200000000))*(1-t)*(1+t-((49/50:ℝ)^3)) ≤ CK.signEntropy t :=
  CK.entropy_tangent_gate
    (by norm_num : (708918499749/1000000000000:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    band4_upper_endpoints.1 band4_upper_endpoints.2 t ht

end
end CK.Certificate.CubicEndpointGates
