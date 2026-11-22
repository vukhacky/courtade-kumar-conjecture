module

public import CK.Profile.ClockCertificates
public import CK.Certificate.ClockBatch.Domains

/-! Twenty-nine supporting-line clock bounds propagated with fixed coefficients as correlation varies. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Middle.ClockConsequences
noncomputable section

theorem C00_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (457/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C00.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C00.weights CK.Certificate.ClockBatch.C00.parameters
    CK.Certificate.ClockBatch.C00.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C00.parameters_nonneg i,CK.Certificate.ClockBatch.C00.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C00.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C00.endpoint_enclosure
    (show (0 : ℝ) ≤ 3794778718303457/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C00.clock_certified.2.2

theorem C01_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (457/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C01.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C01.weights CK.Certificate.ClockBatch.C01.parameters
    CK.Certificate.ClockBatch.C01.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C01.parameters_nonneg i,CK.Certificate.ClockBatch.C01.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C01.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C01.endpoint_enclosure
    (show (0 : ℝ) ≤ 816203064754057/250000000000000000 by norm_num) CK.Certificate.ClockBatch.C01.clock_certified.2.2

theorem C02_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (457/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C02.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C02.weights CK.Certificate.ClockBatch.C02.parameters
    CK.Certificate.ClockBatch.C02.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C02.parameters_nonneg i,CK.Certificate.ClockBatch.C02.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C02.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C02.endpoint_enclosure
    (show (0 : ℝ) ≤ 16570769505363/125000000000000000 by norm_num) CK.Certificate.ClockBatch.C02.clock_certified.2.2

theorem C03_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (457/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C03.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C03.weights CK.Certificate.ClockBatch.C03.parameters
    CK.Certificate.ClockBatch.C03.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C03.parameters_nonneg i,CK.Certificate.ClockBatch.C03.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C03.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C03.endpoint_enclosure
    (show (0 : ℝ) ≤ 2071918126350501/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C03.clock_certified.2.2

theorem C04_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (457/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C04.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C04.weights CK.Certificate.ClockBatch.C04.parameters
    CK.Certificate.ClockBatch.C04.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C04.parameters_nonneg i,CK.Certificate.ClockBatch.C04.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C04.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C04.endpoint_enclosure
    (show (0 : ℝ) ≤ 1481653076981459/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C04.clock_certified.2.2

theorem C05_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (457/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C05.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C05.weights CK.Certificate.ClockBatch.C05.parameters
    CK.Certificate.ClockBatch.C05.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C05.parameters_nonneg i,CK.Certificate.ClockBatch.C05.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C05.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C05.endpoint_enclosure
    (show (0 : ℝ) ≤ 1473509371462107/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C05.clock_certified.2.2

theorem C06_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (457/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C06.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C06.weights CK.Certificate.ClockBatch.C06.parameters
    CK.Certificate.ClockBatch.C06.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C06.parameters_nonneg i,CK.Certificate.ClockBatch.C06.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C06.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C06.endpoint_enclosure
    (show (0 : ℝ) ≤ 35167136603133/125000000000000000 by norm_num) CK.Certificate.ClockBatch.C06.clock_certified.2.2

theorem C07_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (19/20 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C07.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C07.weights CK.Certificate.ClockBatch.C07.parameters
    CK.Certificate.ClockBatch.C07.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C07.parameters_nonneg i,CK.Certificate.ClockBatch.C07.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C07.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C07.endpoint_enclosure
    (show (0 : ℝ) ≤ 207475497721527/250000000000000000 by norm_num) CK.Certificate.ClockBatch.C07.clock_certified.2.2

theorem C08_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (19/20 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C08.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C08.weights CK.Certificate.ClockBatch.C08.parameters
    CK.Certificate.ClockBatch.C08.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C08.parameters_nonneg i,CK.Certificate.ClockBatch.C08.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C08.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C08.endpoint_enclosure
    (show (0 : ℝ) ≤ 222170212250301/500000000000000000 by norm_num) CK.Certificate.ClockBatch.C08.clock_certified.2.2

theorem C09_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (19/20 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C09.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C09.weights CK.Certificate.ClockBatch.C09.parameters
    CK.Certificate.ClockBatch.C09.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C09.parameters_nonneg i,CK.Certificate.ClockBatch.C09.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C09.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C09.endpoint_enclosure
    (show (0 : ℝ) ≤ 367694971188661/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C09.clock_certified.2.2

theorem C10_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (19/20 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C10.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C10.weights CK.Certificate.ClockBatch.C10.parameters
    CK.Certificate.ClockBatch.C10.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C10.parameters_nonneg i,CK.Certificate.ClockBatch.C10.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C10.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C10.endpoint_enclosure
    (show (0 : ℝ) ≤ 79943327037799/250000000000000000 by norm_num) CK.Certificate.ClockBatch.C10.clock_certified.2.2

theorem C11_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (19/20 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C11.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C11.weights CK.Certificate.ClockBatch.C11.parameters
    CK.Certificate.ClockBatch.C11.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C11.parameters_nonneg i,CK.Certificate.ClockBatch.C11.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C11.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C11.endpoint_enclosure
    (show (0 : ℝ) ≤ 26979357526803/500000000000000000 by norm_num) CK.Certificate.ClockBatch.C11.clock_certified.2.2

theorem C12_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (97/100 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C12.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C12.weights CK.Certificate.ClockBatch.C12.parameters
    CK.Certificate.ClockBatch.C12.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C12.parameters_nonneg i,CK.Certificate.ClockBatch.C12.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C12.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C12.endpoint_enclosure
    (show (0 : ℝ) ≤ 285017456723829/500000000000000000 by norm_num) CK.Certificate.ClockBatch.C12.clock_certified.2.2

theorem C13_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (97/100 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C13.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C13.weights CK.Certificate.ClockBatch.C13.parameters
    CK.Certificate.ClockBatch.C13.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C13.parameters_nonneg i,CK.Certificate.ClockBatch.C13.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C13.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C13.endpoint_enclosure
    (show (0 : ℝ) ≤ 514474958818347/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C13.clock_certified.2.2

theorem C14_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (97/100 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C14.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C14.weights CK.Certificate.ClockBatch.C14.parameters
    CK.Certificate.ClockBatch.C14.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C14.parameters_nonneg i,CK.Certificate.ClockBatch.C14.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C14.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C14.endpoint_enclosure
    (show (0 : ℝ) ≤ 436132279273209/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C14.clock_certified.2.2

theorem C15_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (97/100 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C15.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C15.weights CK.Certificate.ClockBatch.C15.parameters
    CK.Certificate.ClockBatch.C15.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C15.parameters_nonneg i,CK.Certificate.ClockBatch.C15.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C15.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C15.endpoint_enclosure
    (show (0 : ℝ) ≤ 35140061667593/500000000000000000 by norm_num) CK.Certificate.ClockBatch.C15.clock_certified.2.2

theorem C16_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (487/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C16.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C16.weights CK.Certificate.ClockBatch.C16.parameters
    CK.Certificate.ClockBatch.C16.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C16.parameters_nonneg i,CK.Certificate.ClockBatch.C16.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C16.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C16.endpoint_enclosure
    (show (0 : ℝ) ≤ 480310284193691/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C16.clock_certified.2.2

theorem C17_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (487/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C17.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C17.weights CK.Certificate.ClockBatch.C17.parameters
    CK.Certificate.ClockBatch.C17.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C17.parameters_nonneg i,CK.Certificate.ClockBatch.C17.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C17.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C17.endpoint_enclosure
    (show (0 : ℝ) ≤ 10475904507409/250000000000000000 by norm_num) CK.Certificate.ClockBatch.C17.clock_certified.2.2

theorem C18_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (487/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C18.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C18.weights CK.Certificate.ClockBatch.C18.parameters
    CK.Certificate.ClockBatch.C18.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C18.parameters_nonneg i,CK.Certificate.ClockBatch.C18.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C18.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C18.endpoint_enclosure
    (show (0 : ℝ) ≤ 417787108600797/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C18.clock_certified.2.2

theorem C19_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (487/500 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C19.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C19.weights CK.Certificate.ClockBatch.C19.parameters
    CK.Certificate.ClockBatch.C19.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C19.parameters_nonneg i,CK.Certificate.ClockBatch.C19.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C19.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C19.endpoint_enclosure
    (show (0 : ℝ) ≤ 21140652613967/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C19.clock_certified.2.2

theorem C20_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C20.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C20.weights CK.Certificate.ClockBatch.C20.parameters
    CK.Certificate.ClockBatch.C20.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C20.parameters_nonneg i,CK.Certificate.ClockBatch.C20.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C20.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C20.endpoint_enclosure
    (show (0 : ℝ) ≤ 4086069271149/250000000000000000 by norm_num) CK.Certificate.ClockBatch.C20.clock_certified.2.2

theorem C21_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C21.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C21.weights CK.Certificate.ClockBatch.C21.parameters
    CK.Certificate.ClockBatch.C21.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C21.parameters_nonneg i,CK.Certificate.ClockBatch.C21.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C21.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C21.endpoint_enclosure
    (show (0 : ℝ) ≤ 190130083085029/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C21.clock_certified.2.2

theorem C22_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C22.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C22.weights CK.Certificate.ClockBatch.C22.parameters
    CK.Certificate.ClockBatch.C22.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C22.parameters_nonneg i,CK.Certificate.ClockBatch.C22.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C22.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C22.endpoint_enclosure
    (show (0 : ℝ) ≤ 20154795268233/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C22.clock_certified.2.2

theorem C23_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C23.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C23.weights CK.Certificate.ClockBatch.C23.parameters
    CK.Certificate.ClockBatch.C23.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C23.parameters_nonneg i,CK.Certificate.ClockBatch.C23.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C23.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C23.endpoint_enclosure
    (show (0 : ℝ) ≤ 138120155905839/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C23.clock_certified.2.2

theorem C24_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C24.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C24.weights CK.Certificate.ClockBatch.C24.parameters
    CK.Certificate.ClockBatch.C24.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C24.parameters_nonneg i,CK.Certificate.ClockBatch.C24.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C24.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C24.endpoint_enclosure
    (show (0 : ℝ) ≤ 254576595378357/250000000000000000 by norm_num) CK.Certificate.ClockBatch.C24.clock_certified.2.2

theorem C25_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C25.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C25.weights CK.Certificate.ClockBatch.C25.parameters
    CK.Certificate.ClockBatch.C25.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C25.parameters_nonneg i,CK.Certificate.ClockBatch.C25.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C25.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C25.endpoint_enclosure
    (show (0 : ℝ) ≤ 269244275451889/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C25.clock_certified.2.2

theorem C26_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C26.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C26.weights CK.Certificate.ClockBatch.C26.parameters
    CK.Certificate.ClockBatch.C26.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C26.parameters_nonneg i,CK.Certificate.ClockBatch.C26.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C26.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C26.endpoint_enclosure
    (show (0 : ℝ) ≤ 689680846427171/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C26.clock_certified.2.2

theorem C27_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C27.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C27.weights CK.Certificate.ClockBatch.C27.parameters
    CK.Certificate.ClockBatch.C27.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C27.parameters_nonneg i,CK.Certificate.ClockBatch.C27.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C27.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C27.endpoint_enclosure
    (show (0 : ℝ) ≤ 6453340951943/100000000000000000 by norm_num) CK.Certificate.ClockBatch.C27.clock_certified.2.2

theorem C28_propagated {ρ : ℝ} (hρ : ρ ∈ Ico (39/40 : ℝ) 1) :
    CK.Profile.clock CK.Certificate.ClockBatch.C28.profile (CK.Profile.meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  exact CK.Profile.fixed_clock_of_certificate CK.Certificate.ClockBatch.C28.weights CK.Certificate.ClockBatch.C28.parameters
    CK.Certificate.ClockBatch.C28.weights_nonneg (fun i => ⟨CK.Certificate.ClockBatch.C28.parameters_nonneg i,CK.Certificate.ClockBatch.C28.parameters_le_one i⟩)
    CK.Certificate.ClockBatch.C28.positive_term (by norm_num) hρ CK.Certificate.ClockBatch.C28.endpoint_enclosure
    (show (0 : ℝ) ≤ 53072094260211/1000000000000000000 by norm_num) CK.Certificate.ClockBatch.C28.clock_certified.2.2

end
end CK.Middle.ClockConsequences
