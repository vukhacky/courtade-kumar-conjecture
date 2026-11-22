module

public import CK.Analysis.BinaryEntropy
public import CK.Functional.SignEntropy

/-! Quartic entropy bounds for fourth-moment compensation, via interior derivatives and continuity at the endpoints. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Certificate
noncomputable section

theorem cubic_lower_phiSlope {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    t + t^3/3 ≤ phiSlope t := by
  rw [phiSlope_eq_artanh ⟨by linarith, ht1⟩]
  have h := Real.sum_range_le_artanh ht0 ht1 2
  norm_num [Finset.sum_range_succ] at h
  exact h

theorem quartic_lower_phi_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t^2/2 + t^4/12 ≤ phi t := by
  let F : ℝ → ℝ := fun x => phi x - x^2/2 - x^4/12
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt F (phiSlope x - x - x^3/3) x := by
    have h := ((hasDerivAt_phi ⟨by linarith [hx.1], hx.2⟩).sub
      ((hasDerivAt_pow 2 x).div_const 2)).sub ((hasDerivAt_pow 4 x).div_const 12)
    apply h.congr_deriv
    norm_num
    ring
  have hm : MonotoneOn F (Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hc.continuousOn
    · intro x hx
      exact (hd x (by simpa using hx)).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo (0 : ℝ) 1 := by simpa using hx
      linarith [cubic_lower_phiSlope hx'.1.le hx'.2]
  have hh := hm (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht ht.1
  dsimp [F] at hh
  norm_num at hh
  linarith

theorem quartic_lower_phi {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    t^2/2 + t^4/12 ≤ phi t := by
  by_cases ht0 : 0 ≤ t
  · exact quartic_lower_phi_nonneg ⟨ht0, ht.2⟩
  · have hneg : -t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1]
    simpa only [neg_sq, show (-t)^4 = t^4 by ring, phi_neg]
      using quartic_lower_phi_nonneg hneg

def quarticNumerator (t : ℝ) : ℝ := t * phiSlope t - 4 * phi t + t^2
def quarticNumeratorSlope (t : ℝ) : ℝ := t / (1-t^2) - 3 * phiSlope t + 2*t
def quarticRatio (t : ℝ) : ℝ := (phi t - t^2/2) / t^4

theorem hasDerivAt_quarticNumerator {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt quarticNumerator (quarticNumeratorSlope t) t := by
  have h := (((hasDerivAt_id t).mul (hasDerivAt_phiSlope ht)).sub
    ((hasDerivAt_phi ht).const_mul 4)).add (hasDerivAt_pow 2 t)
  apply h.congr_deriv
  dsimp [quarticNumeratorSlope]
  norm_num
  ring

theorem hasDerivAt_quarticNumeratorSlope {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt quarticNumeratorSlope (2*t^4/(1-t^2)^2) t := by
  have hn : 1-t^2 ≠ 0 := by nlinarith [ht.1, ht.2]
  have h := (((hasDerivAt_id t).div ((hasDerivAt_pow 2 t).const_sub 1) hn).sub
    ((hasDerivAt_phiSlope ht).const_mul 3)).add ((hasDerivAt_id t).const_mul 2)
  apply h.congr_deriv
  norm_num
  field_simp
  ring

theorem quarticNumeratorSlope_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ quarticNumeratorSlope t := by
  have hdom : Icc 0 t ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 ht1⟩
  have hm : MonotoneOn quarticNumeratorSlope (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
    · intro x hx
      exact (hasDerivAt_quarticNumeratorSlope (hdom hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_quarticNumeratorSlope (hdom (interior_subset hx))).hasDerivWithinAt
    · intro x hx
      positivity
  have h := hm ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  simpa [quarticNumeratorSlope] using h

theorem quarticNumerator_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 ≤ quarticNumerator t := by
  have hdom : Icc 0 t ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], lt_of_le_of_lt hx.2 ht1⟩
  have hm : MonotoneOn quarticNumerator (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
    · intro x hx
      exact (hasDerivAt_quarticNumerator (hdom hx)).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_quarticNumerator (hdom (interior_subset hx))).hasDerivWithinAt
    · intro x hx
      have hx' := interior_subset hx
      exact quarticNumeratorSlope_nonneg hx'.1 (lt_of_le_of_lt hx'.2 ht1)
  have h := hm ⟨le_rfl, ht0⟩ ⟨ht0, le_rfl⟩ ht0
  simpa [quarticNumerator] using h

theorem hasDerivAt_quarticRatio {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    HasDerivAt quarticRatio (quarticNumerator t / t^5) t := by
  have h := ((hasDerivAt_phi ⟨by linarith, ht1⟩).sub
    ((hasDerivAt_pow 2 t).div_const 2)).div (hasDerivAt_pow 4 t) (pow_ne_zero 4 ht0.ne')
  apply h.congr_deriv
  dsimp [quarticNumerator]
  norm_num
  field_simp
  ring

theorem quartic_upper_phi_nonneg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    phi t ≤ t^2/2 + (Real.log 2 - 1/2)*t^4 := by
  by_cases hz : t = 0
  · subst t
    simp
  have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hz)
  have hc : ContinuousOn quarticRatio (Icc t 1) := by
    unfold quarticRatio
    apply (continuous_phi.continuousOn.sub ((continuous_pow 2).continuousOn.div_const 2)).div
      (continuous_pow 4).continuousOn
    intro x hx
    exact pow_ne_zero 4 (ne_of_gt (ht0.trans_le hx.1))
  have hm : MonotoneOn quarticRatio (Icc t 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t 1) hc
    · intro x hx
      have hx' : x ∈ Ioo t 1 := by simpa using hx
      exact (hasDerivAt_quarticRatio (ht0.trans hx'.1) hx'.2).hasDerivWithinAt
    · intro x hx
      have hx' : x ∈ Ioo t 1 := by simpa using hx
      exact div_nonneg (quarticNumerator_nonneg (ht0.trans hx'.1).le hx'.2)
        (pow_pos (ht0.trans hx'.1) 5).le
  have h := hm ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2
  have hratio : (phi t - t^2/2) / t^4 ≤ Real.log 2 - 1/2 := by
    simpa [quarticRatio] using h
  have hh := (div_le_iff₀ (pow_pos ht0 4)).mp hratio
  linarith

theorem quartic_upper_phi {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    phi t ≤ t^2/2 + (Real.log 2 - 1/2)*t^4 := by
  by_cases ht0 : 0 ≤ t
  · exact quartic_upper_phi_nonneg ⟨ht0, ht.2⟩
  · have hneg : -t ∈ Icc (0 : ℝ) 1 := by constructor <;> linarith [ht.1]
    simpa only [neg_sq, show (-t)^4 = t^4 by ring, phi_neg]
      using quartic_upper_phi_nonneg hneg

theorem signEntropy_quartic_lower {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    Real.log 2 - t^2/2 - (Real.log 2 - 1/2)*t^4 ≤ signEntropy t := by
  rw [signEntropy_eq_log_two_sub_phi]
  linarith [quartic_upper_phi ht]

end
end CK.Certificate
