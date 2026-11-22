module

public import CK.Profile.Weighted
public import CK.Certificate.ClockIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The profile clock for any positive, decreasing, continuous profile.
Integrability is proved before the clock is used analytically. Its value
at zero is independent of the chosen totalized profile value there. -/

@[expose] public section
set_option autoImplicit false
open MeasureTheory Set
namespace CK.Profile
noncomputable section

def clock (P : ℝ → ℝ) (y : ℝ) : ℝ := ∫ e in (0 : ℝ)..y, 1/(e+P e)

@[simp] theorem clock_zero (P : ℝ → ℝ) : clock P 0 = 0 := by simp [clock]

variable {P : ℝ → ℝ}
variable (hcont : ContinuousOn P (Ioi (0 : ℝ)))
variable (hanti : AntitoneOn P (Ioi (0 : ℝ)))
variable (hpos : ∀ y, 0 < y → 0 < P y)
include hcont hanti hpos

theorem clock_integrable {Y : ℝ} (hY : 0 < Y) :
    IntervalIntegrable (fun e => 1/(e+P e)) volume 0 Y := by
  have hbound : ∀ e ∈ Ioc (0 : ℝ) Y, P Y+0*e ≤ e+P e := by
    intro e he
    have hp := hanti he.1 hY he.2
    linarith [he.1]
  exact (Certificate.reciprocal_integral_le_affine hY (hpos Y hY)
    (by simpa using hpos Y hY) (fun e => e+P e)
    (continuousOn_id.add (hcont.mono (fun _ he => he.1))) hbound).1

theorem continuousOn_clock_interval {Y : ℝ} (hY : 0 < Y) :
    ContinuousOn (clock P) (Icc (0 : ℝ) Y) := by
  change ContinuousOn (fun b => ∫ e in (0 : ℝ)..b, 1/(e+P e)) (Icc (0 : ℝ) Y)
  have h := intervalIntegral.continuousOn_primitive_interval'
    (clock_integrable hcont hanti hpos hY) (a := (0 : ℝ)) (by simp)
  simpa only [clock, uIcc_of_le hY.le] using h

theorem hasDerivAt_clock {y : ℝ} (hy : 0 < y) :
    HasDerivAt (clock P) (1/(y+P y)) y := by
  have hcOn : ContinuousOn (fun e => 1/(e+P e)) (Ioi (0 : ℝ)) :=
    continuousOn_const.div (continuousOn_id.add hcont)
      (fun e he => ne_of_gt (add_pos he (hpos e he)))
  have hc : ContinuousAt (fun e => 1/(e+P e)) y :=
    continuousAt_const.div (continuousAt_id.add
      ((hcont y hy).continuousAt (Ioi_mem_nhds hy))) (ne_of_gt (add_pos hy (hpos y hy)))
  exact intervalIntegral.integral_hasDerivAt_right (clock_integrable hcont hanti hpos hy)
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hcOn y hy) hc

theorem continuousOn_clock : ContinuousOn (clock P) (Ici (0 : ℝ)) := by
  intro y hy
  rcases eq_or_lt_of_le hy with hy | hy
  · subst y
    have h := (continuousOn_clock_interval hcont hanti hpos (show (0 : ℝ) < 1 by norm_num))
      0 (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    simpa only [ContinuousWithinAt, nhdsWithin_Icc_eq_nhdsGE (show (0 : ℝ) < 1 by norm_num)] using h
  · exact (hasDerivAt_clock hcont hanti hpos hy).continuousAt.continuousWithinAt

theorem strictMonoOn_clock : StrictMonoOn (clock P) (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 0) (continuousOn_clock hcont hanti hpos)
  · intro y hy
    exact (hasDerivAt_clock hcont hanti hpos (by simpa only [interior_Ici, mem_Ioi] using hy)).hasDerivWithinAt
  · intro y hy
    have hy' : 0 < y := by simpa only [interior_Ici, mem_Ioi] using hy
    exact one_div_pos.mpr (add_pos hy' (hpos y hy'))

theorem clock_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ clock P y := by
  have h := (strictMonoOn_clock hcont hanti hpos).monotoneOn
    (show (0 : ℝ) ∈ Ici (0 : ℝ) from le_rfl) hy hy
  simpa using h

/-- A generic differential comparison. Its regularity and differential
premises are explicit; actual noisy-Boolean trajectories discharge them
in `ClockDynamics.lean`. -/
theorem time_le_clock_of_differential {T : ℝ} (hT : 0 < T) (y v : ℝ → ℝ)
    (hycont : ContinuousOn y (Icc (0 : ℝ) T)) (hy0 : y 0 = 0)
    (hypos : ∀ t ∈ Ioc (0 : ℝ) T, 0 < y t)
    (hyderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt y (v t) t)
    (hprod : ∀ t ∈ Ioo (0 : ℝ) T, y t+P (y t) ≤ v t) :
    T ≤ clock P (y T) := by
  have hrange : Set.MapsTo y (Icc (0 : ℝ) T) (Ici (0 : ℝ)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · simp [← ht0, hy0]
    · exact (hypos t ⟨ht0, ht.2⟩).le
  let G : ℝ → ℝ := fun t => clock P (y t)-t
  have hGc : ContinuousOn G (Icc (0 : ℝ) T) :=
    ((continuousOn_clock hcont hanti hpos).comp hycont hrange).sub continuousOn_id
  have hGd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
      HasDerivAt G (v t/(y t+P (y t))-1) t := by
    have h := ((hasDerivAt_clock hcont hanti hpos (hypos t ⟨ht.1, ht.2.le⟩)).comp t
      (hyderiv t ht)).sub (hasDerivAt_id t)
    apply h.congr_deriv
    ring
  have hm : MonotoneOn G (Icc (0 : ℝ) T) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hGc
    · intro t ht
      exact (hGd t (by simpa only [interior_Icc] using ht)).hasDerivWithinAt
    · intro t ht
      have ht' : t ∈ Ioo (0 : ℝ) T := by simpa only [interior_Icc] using ht
      have hy := hypos t ⟨ht'.1, ht'.2.le⟩
      have hd : 0 < y t+P (y t) := add_pos hy (hpos _ hy)
      exact sub_nonneg.mpr ((le_div_iff₀ hd).2 (by simpa using hprod t ht'))
  have h := hm ⟨le_rfl, hT.le⟩ ⟨hT.le, le_rfl⟩ hT.le
  simpa [G, hy0] using h

end
end CK.Profile
