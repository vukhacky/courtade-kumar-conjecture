module

public import CK.Profile.Tangent
public import CK.Certificate.ClockIntegral

/-! The P03 supporting-line bound and its integral over the full entropy interval. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory
namespace CK.Profile
noncomputable section

theorem p03_supportHeight :
    Certificate.P03.supportHeight = Real.artanh Certificate.P03.support := by
  have ht : Certificate.P03.support ∈ Set.Icc (-1 : ℝ) 1 := by
    norm_num [Certificate.P03.support]
  rw [Real.artanh_eq_half_log ht]
  unfold Certificate.P03.supportHeight
  ring

/-- The P03 entropy-profile bound on its entire integration domain, with a strict rational margin. -/
theorem p03_profileClock_certified :
    IntervalIntegrable
      (fun e => 1 / (e + Certificate.P03.weight * profile e Certificate.P03.profileQ))
      volume 0 Certificate.P03.endpointY ∧
    (∫ e in (0 : ℝ)..Certificate.P03.endpointY,
      1 / (e + Certificate.P03.weight * profile e Certificate.P03.profileQ)) +
        (7 / 1000 : ℝ) < Real.log (1 / Certificate.P03.rho) := by
  apply Certificate.P03.profileClock_of_tangent
  · exact (continuousOn_profile (by norm_num [Certificate.P03.profileQ])).mono
      (fun _ he => he.1)
  · intro e he
    have h := profile_tangent he.1
      (show 0 < Certificate.P03.profileQ by norm_num [Certificate.P03.profileQ])
      (show Certificate.P03.support ∈ Set.Ioo (0 : ℝ) 1 by
        norm_num [Certificate.P03.support])
    rw [p03_supportHeight]
    exact h

/-- The exact source entropy ratio lies below the certified endpoint. -/
theorem p03_endpoint_enclosure :
    meanEntropy Certificate.P03.rho / Certificate.P03.rho < Certificate.P03.endpointY := by
  have h := Certificate.P03.endpointY_entropy_margin
  change meanEntropy Certificate.P03.rho / Certificate.P03.rho +
    (9 / 1000000000000 : ℝ) < Certificate.P03.endpointY at h
  linarith

/-- Agreement with the right-hand improper-integral interpretation in
the manuscript, rather than the default value of a divergent integral. -/
theorem p03_profileClock_improper_limit :
    Filter.Tendsto
      (fun ε => ∫ e in ε..Certificate.P03.endpointY,
        1 / (e + Certificate.P03.weight * profile e Certificate.P03.profileQ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ e in (0 : ℝ)..Certificate.P03.endpointY,
        1 / (e + Certificate.P03.weight * profile e Certificate.P03.profileQ))) := by
  exact Certificate.tendsto_integral_from_right
    (by norm_num [Certificate.P03.endpointY]) p03_profileClock_certified.1

end
end CK.Profile
