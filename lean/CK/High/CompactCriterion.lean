module

public import CK.High.CompactEndpoints
public import CK.High.CompactMaster

/-! Assemble the five exact scalar margins into the analytic derivative
criterion. Positivity of the margins is supplied by the certificate layer. -/

@[expose] public section
set_option autoImplicit false
namespace CK
noncomputable section

theorem compact_spectral_derivative_of_margins {n : ℕ} {u : ℝ}
    (hu : (9/4 : ℝ) ≤ u)
    (hmaster : 0 < Certificate.Compact.master u)
    (hLL : 0 < Certificate.Compact.lowerLogMargin u)
    (hLM : 0 < Certificate.Compact.middleLogMargin u)
    (hQM : 0 < Certificate.Compact.middleQuadMargin u)
    (hQT : 0 < Certificate.Compact.upperQuadMargin u)
    (f : BooleanFunction n) (hm : Monotone (lift f))
    (hgap : 0 < informationGap (Real.tanh u) f) :
    0 < deriv (fun ρ => informationGap ρ f) (Real.tanh u) := by
  apply compact_spectral_derivative_of_endpoints hu
    (compact_discarded_of_master hu hmaster)
    (compact_logLow_of_margin hu hLL)
    (compact_logMiddle_of_margin hu hLM)
    (compact_quadMiddle_of_margin hu hQM)
    (compact_quadTop_of_margin hu hQT) f hm
  · by_contra hf
    push Not at hf
    have hc : f=(fun _ : Cube n => f (fun _ => false)) := funext (fun x => hf x _)
    rw [informationGap,hc,information_const] at hgap
    have hp := phi_nonneg (Real.tanh u)
    linarith only [hgap,hp]
  · exact hgap

end
end CK
