module

public import CK.Middle.CubicPropagation
public import CK.Middle.CellGate
public import CK.Certificate.CubicEndpointGates

/-! Complete scalar cubic gates on the five middle-correlation bands.
Endpoint logarithm certificates are propagated over every correlation by
the proved analytic convexity theorem. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem cubic_band0_parameters {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (457/500 : ℝ) (19/20)) :
    0 < cubicC ρ (20630961/25000000) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, cubicKappa ρ (20630961/25000000)*(1-t)*(1+t-ρ^3) ≤ signEntropy t) ∧
      cubicKappa ρ (20630961/25000000)*(1-ρ^3) < 1/2 := by
  have hρdom : ρ ∈ Set.Ico (457/500 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hM : (20630961/25000000 : ℝ) ∈ Set.Icc (3/4 : ℝ) (83/100) := by norm_num
  refine ⟨cubicC_pos hM ⟨hρdom.1,hρdom.2.le⟩, ?_, cubicKappa_prior_credit hM hρdom⟩
  exact cubic_entropy_gate_of_endpoints hM (by norm_num) (by norm_num) hρ
    (fun _ ht => Certificate.CubicEndpointGates.band0_lower ht)
    (fun _ ht => Certificate.CubicEndpointGates.band0_upper ht)

theorem mutualInformation_le_phi_cubic_band0 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (457/500 : ℝ) (19/20)) (f : BooleanFunction n)
    (hw : cubicWeight ρ f ≤ 20630961/25000000) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hC,hgate,hcredit⟩ := cubic_band0_parameters hρ
  exact mutualInformation_le_phi_of_cubicWeight ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
    hC hgate hcredit.le f hw

theorem cubic_band1_parameters {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (19/20 : ℝ) (97/100)) :
    0 < cubicC ρ (24615813/31250000) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, cubicKappa ρ (24615813/31250000)*(1-t)*(1+t-ρ^3) ≤ signEntropy t) ∧
      cubicKappa ρ (24615813/31250000)*(1-ρ^3) < 1/2 := by
  have hρdom : ρ ∈ Set.Ico (457/500 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hM : (24615813/31250000 : ℝ) ∈ Set.Icc (3/4 : ℝ) (83/100) := by norm_num
  refine ⟨cubicC_pos hM ⟨hρdom.1,hρdom.2.le⟩, ?_, cubicKappa_prior_credit hM hρdom⟩
  exact cubic_entropy_gate_of_endpoints hM (by norm_num) (by norm_num) hρ
    (fun _ ht => Certificate.CubicEndpointGates.band1_lower ht)
    (fun _ ht => Certificate.CubicEndpointGates.band1_upper ht)

theorem mutualInformation_le_phi_cubic_band1 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (19/20 : ℝ) (97/100)) (f : BooleanFunction n)
    (hw : cubicWeight ρ f ≤ 24615813/31250000) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hC,hgate,hcredit⟩ := cubic_band1_parameters hρ
  exact mutualInformation_le_phi_of_cubicWeight ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
    hC hgate hcredit.le f hw

theorem cubic_band2_parameters {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (97/100 : ℝ) (487/500)) :
    0 < cubicC ρ (77592593/100000000) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, cubicKappa ρ (77592593/100000000)*(1-t)*(1+t-ρ^3) ≤ signEntropy t) ∧
      cubicKappa ρ (77592593/100000000)*(1-ρ^3) < 1/2 := by
  have hρdom : ρ ∈ Set.Ico (457/500 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hM : (77592593/100000000 : ℝ) ∈ Set.Icc (3/4 : ℝ) (83/100) := by norm_num
  refine ⟨cubicC_pos hM ⟨hρdom.1,hρdom.2.le⟩, ?_, cubicKappa_prior_credit hM hρdom⟩
  exact cubic_entropy_gate_of_endpoints hM (by norm_num) (by norm_num) hρ
    (fun _ ht => Certificate.CubicEndpointGates.band2_lower ht)
    (fun _ ht => Certificate.CubicEndpointGates.band2_upper ht)

theorem mutualInformation_le_phi_cubic_band2 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (97/100 : ℝ) (487/500)) (f : BooleanFunction n)
    (hw : cubicWeight ρ f ≤ 77592593/100000000) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hC,hgate,hcredit⟩ := cubic_band2_parameters hρ
  exact mutualInformation_le_phi_of_cubicWeight ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
    hC hgate hcredit.le f hw

theorem cubic_band3_parameters {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (487/500 : ℝ) (39/40)) :
    0 < cubicC ρ (772609873/1000000000) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, cubicKappa ρ (772609873/1000000000)*(1-t)*(1+t-ρ^3) ≤ signEntropy t) ∧
      cubicKappa ρ (772609873/1000000000)*(1-ρ^3) < 1/2 := by
  have hρdom : ρ ∈ Set.Ico (457/500 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hM : (772609873/1000000000 : ℝ) ∈ Set.Icc (3/4 : ℝ) (83/100) := by norm_num
  refine ⟨cubicC_pos hM ⟨hρdom.1,hρdom.2.le⟩, ?_, cubicKappa_prior_credit hM hρdom⟩
  exact cubic_entropy_gate_of_endpoints hM (by norm_num) (by norm_num) hρ
    (fun _ ht => Certificate.CubicEndpointGates.band3_lower ht)
    (fun _ ht => Certificate.CubicEndpointGates.band3_upper ht)

theorem mutualInformation_le_phi_cubic_band3 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (487/500 : ℝ) (39/40)) (f : BooleanFunction n)
    (hw : cubicWeight ρ f ≤ 772609873/1000000000) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hC,hgate,hcredit⟩ := cubic_band3_parameters hρ
  exact mutualInformation_le_phi_of_cubicWeight ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
    hC hgate hcredit.le f hw

theorem cubic_band4_parameters {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50)) :
    0 < cubicC ρ (150614067/200000000) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1, cubicKappa ρ (150614067/200000000)*(1-t)*(1+t-ρ^3) ≤ signEntropy t) ∧
      cubicKappa ρ (150614067/200000000)*(1-ρ^3) < 1/2 := by
  have hρdom : ρ ∈ Set.Ico (457/500 : ℝ) 1 := ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
  have hM : (150614067/200000000 : ℝ) ∈ Set.Icc (3/4 : ℝ) (83/100) := by norm_num
  refine ⟨cubicC_pos hM ⟨hρdom.1,hρdom.2.le⟩, ?_, cubicKappa_prior_credit hM hρdom⟩
  exact cubic_entropy_gate_of_endpoints hM (by norm_num) (by norm_num) hρ
    (fun _ ht => Certificate.CubicEndpointGates.band4_lower ht)
    (fun _ ht => Certificate.CubicEndpointGates.band4_upper ht)

theorem mutualInformation_le_phi_cubic_band4 {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (39/40 : ℝ) (49/50)) (f : BooleanFunction n)
    (hw : cubicWeight ρ f ≤ 150614067/200000000) : mutualInformation ρ f ≤ phi ρ := by
  obtain ⟨hC,hgate,hcredit⟩ := cubic_band4_parameters hρ
  exact mutualInformation_le_phi_of_cubicWeight ⟨by linarith [hρ.1],by linarith [hρ.2]⟩
    hC hgate hcredit.le f hw

end
end CK
