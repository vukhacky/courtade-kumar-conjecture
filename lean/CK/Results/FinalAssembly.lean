module

public import CK.High.CompactCriterion
public import CK.Results.HighTailRange

/-! The global Shannon inequality from the five compact-range scalar certificates and the analytic tail. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK
noncomputable section

def CompactCertificateStatement : Prop :=
  ∀ u ∈ Icc (45951/20000 : ℝ) 8,
    0 < Certificate.Compact.master u ∧
    0 < Certificate.Compact.lowerLogMargin u ∧
    0 < Certificate.Compact.middleLogMargin u ∧
    0 < Certificate.Compact.middleQuadMargin u ∧
    0 < Certificate.Compact.upperQuadMargin u

theorem terminal_derivative_of_compact_certificate
    (hcompact : CompactCertificateStatement)
    {n : ℕ} (hn : 0 < n) (f : BooleanFunction n) (hf : Monotone (lift f))
    {ρ : ℝ} (hρ : ρ ∈ Ioo (49/50 : ℝ) 1) (hgap : 0 < informationGap ρ f) :
    0 < deriv (fun r => informationGap r f) ρ := by
  have hρio : ρ ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith only [hρ.1],hρ.2⟩
  have hid := Real.tanh_artanh hρio
  have hp : 0 < informationGap (Real.tanh (Real.artanh ρ)) f := by rw [hid]; exact hgap
  by_cases hu : Real.artanh ρ ≤ 8
  · have hdom := compact_height_overlap ⟨hρ.1.le,hρ.2⟩ hu
    have hu9 : (9/4 : ℝ) ≤ Real.artanh ρ := by linarith only [hdom.1]
    obtain ⟨hB,hLL,hLM,hQM,hQT⟩ := hcompact (Real.artanh ρ) hdom
    have hd := compact_spectral_derivative_of_margins hu9 hB hLL hLM hQM hQT f hf hp
    rwa [hid] at hd
  · have hu8 : (8 : ℝ) ≤ Real.artanh ρ := (lt_of_not_ge hu).le
    have hd := analytic_tail_derivative hn hu8 f hf
      (positive_gap_tail_distance hn hu8 f hp).le hp
    rwa [hid] at hd

theorem mainStatement_of_compact_certificate
    (hcompact : CompactCertificateStatement) : MainStatement := by
  apply mainStatement_of_terminal_derivative
  intro n hn f hf ρ hρ hgap
  exact terminal_derivative_of_compact_certificate hcompact hn f hf hρ hgap

end
end CK
