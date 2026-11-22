module

public import CK.Profile.Clock
public import CK.Profile.Ratio

/-! Exact normalization of the dictator clock, including the continuous
zero-entropy endpoint. This fixes the time scale in clock propagation. -/

@[expose] public section
set_option autoImplicit false
open Set
namespace CK.Profile
noncomputable section

theorem profile_at_entropy_ratio {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    profile (meanEntropy t/t) 1 = phiSlope t := by
  have hH := meanEntropy_pos ⟨by linarith [ht.1], ht.2⟩
  have he := div_pos hH ht.1
  have hroot : t=profilePoint (meanEntropy t/t) 1 :=
    profilePoint_unique he (by norm_num) ht (by
      rw [div_mul_cancel₀ _ (ne_of_gt ht.1), one_mul])
  unfold profile
  rw [← hroot, one_mul, phiSlope_eq_artanh ⟨by linarith [ht.1], ht.2⟩]

theorem dictator_clock {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    clock (fun e => profile e 1) (meanEntropy ρ/ρ) = -Real.log ρ := by
  let P := fun e => profile e 1
  let y := fun r : ℝ => meanEntropy r/r
  let G := fun r : ℝ => clock P (y r)+Real.log r
  have hcP : ContinuousOn P (Ioi (0 : ℝ)) := continuousOn_profile (by norm_num)
  have haP : AntitoneOn P (Ioi (0 : ℝ)) := profile_antitone (by norm_num)
  have hpP : ∀ e, 0 < e → 0 < P e := fun _ he => profile_pos he (by norm_num)
  have hyc : ContinuousOn y (Icc ρ 1) := continuous_meanEntropy.continuousOn.div
    continuousOn_id (fun r hr => ne_of_gt (hρ.1.trans_le hr.1))
  have hyrange : MapsTo y (Icc ρ 1) (Ici (0 : ℝ)) := by
    intro r hr
    exact div_nonneg (meanEntropy_nonneg ⟨by linarith [hρ.1, hr.1], hr.2⟩)
      (hρ.1.le.trans hr.1)
  have hGc : ContinuousOn G (Icc ρ 1) :=
    ((continuousOn_clock hcP haP hpP).comp hyc hyrange).add
      (Real.continuousOn_log.mono (fun r hr => ne_of_gt (hρ.1.trans_le hr.1)))
  have hGd (r : ℝ) (hr : r ∈ Ioo ρ 1) : HasDerivAt G 0 r := by
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hρ.1.trans hr.1, hr.2⟩
    have hdom : r ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hr01.1], hr01.2⟩
    have hypos : 0 < y r := div_pos (meanEntropy_pos hdom) hr01.1
    have h := ((hasDerivAt_clock hcP haP hpP hypos).comp r
      (hasDerivAt_entropy_ratio hr01)).add (Real.hasDerivAt_log (ne_of_gt hr01.1))
    apply h.congr_deriv
    change (1/(y r+profile (y r) 1))*(-profileAux r/r^2)+r⁻¹=0
    dsimp only [y]
    rw [profile_at_entropy_ratio hr01]
    have hden : meanEntropy r/r+phiSlope r=profileAux r/r := by
      rw [show profileAux r=meanEntropy r+r*phiSlope r from (meanEntropy_add_slope hdom).symm]
      field_simp [ne_of_gt hr01.1]
    rw [hden]
    field_simp [ne_of_gt hr01.1, ne_of_gt (profileAux_pos hdom)]
    ring
  have hm : MonotoneOn G (Icc ρ 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc ρ 1) hGc
      (f' := fun _ => (0 : ℝ))
    · intro r hr
      exact (hGd r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt
    · intro r hr
      exact le_rfl
  have ha : AntitoneOn G (Icc ρ 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc ρ 1) hGc
      (f' := fun _ => (0 : ℝ))
    · intro r hr
      exact (hGd r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt
    · intro r hr
      exact le_rfl
  have heq := le_antisymm
    (hm ⟨le_rfl, hρ.2.le⟩ ⟨hρ.2.le, le_rfl⟩ hρ.2.le)
    (ha ⟨le_rfl, hρ.2.le⟩ ⟨hρ.2.le, le_rfl⟩ hρ.2.le)
  have hy1 : y 1=0 := by simp [y]
  change clock P (y ρ)+Real.log ρ=clock P (y 1)+Real.log 1 at heq
  rw [hy1, clock_zero, Real.log_one] at heq
  change clock P (y ρ) = -Real.log ρ
  linarith

end
end CK.Profile
