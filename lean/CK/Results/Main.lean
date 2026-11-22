module

public import CK.Results.FinalAssembly
public import CK.Certificate.CompactCover

/-! Canonical STOC Courtade--Kumar theorem. The compact input is discharged
by exact rational certificates checked by Lean's kernel. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem compactCertificate : CompactCertificateStatement := by
  intro u hu
  exact Certificate.CompactData.all_margins_positive hu

theorem analytic_compact_derivative {n : ℕ} {u : ℝ}
    (hu : u ∈ Set.Icc (45951/20000 : ℝ) 8)
    (f : BooleanFunction n) (hf : Monotone (lift f))
    (hgap : 0 < informationGap (Real.tanh u) f) :
    0 < deriv (fun r => informationGap r f) (Real.tanh u) := by
  have hu9 : (9/4 : ℝ) ≤ u := by linarith only [hu.1]
  obtain ⟨hB,hLL,hLM,hQM,hQT⟩ := compactCertificate u hu
  exact compact_spectral_derivative_of_margins hu9 hB hLL hLM hQM hQT f hf hgap

theorem positive_gap_terminal_derivative {n : ℕ} (hn : 0 < n)
    (f : BooleanFunction n) (hf : Monotone (lift f))
    {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (49/50 : ℝ) 1) (hgap : 0 < informationGap ρ f) :
    0 < deriv (fun r => informationGap r f) ρ :=
  terminal_derivative_of_compact_certificate compactCertificate hn f hf hρ hgap

theorem main : MainStatement := mainStatement_of_compact_certificate compactCertificate

theorem mutualInformation_le_phi {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ phi ρ := main.1 n hn ρ hρ f

theorem mutualInformation_le_binaryEntropy {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f : BooleanFunction n) :
    mutualInformation ρ f ≤ Real.log 2-Real.binEntropy ((1-ρ)/2) :=
  mutualInformation_le_phi hn hρ f

theorem mutualInformation_le_signedDictator {n : ℕ} (hn : 0 < n) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (f g : BooleanFunction n)
    (hg : IsSignedDictator g) : mutualInformation ρ f ≤ mutualInformation ρ g := by
  rw [main.2 n hn ρ hρ g hg]
  exact mutualInformation_le_phi hn hρ f

theorem functionalMain : FunctionalMainStatement := by
  constructor
  · intro n hn ρ hρ f
    rw [←mutualInformation_eq_information hρ]
    exact main.1 n hn ρ hρ f
  · intro n hn ρ hρ f hf
    rw [←mutualInformation_eq_information hρ]
    exact main.2 n hn ρ hρ f hf

end
end CK
