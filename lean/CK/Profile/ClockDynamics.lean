module

public import CK.Profile.Clock
public import CK.Profile.Production

/-! The actual noisy-Boolean profile clock. We differentiate with respect
to correlation on a fixed compact subinterval of `(0,1]`, keeping the
Boolean function fixed throughout. The noiseless endpoint is treated by
continuity, not by differentiating a singular expression there. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK.Profile
noncomputable section

def singletonProfile {n : ℕ} (f : BooleanFunction n) (e : ℝ) : ℝ :=
  ∑ i : Fin n, profile e |fourier (lift f) {i}|

theorem exists_nonzero_singleton_of_weight_pos {n : ℕ} (f : BooleanFunction n)
    (hW : 0 < fourierWeight (lift f) 1) : ∃ i : Fin n, 0 < |fourier (lift f) {i}| := by
  classical
  unfold fourierWeight at hW
  obtain ⟨S, _, hS⟩ : ∃ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      0 < if S.card = 1 then fourier (lift f) S ^ 2 else 0 := by
    by_contra h
    push Not at h
    have hz := Finset.sum_nonpos h
    linarith
  split_ifs at hS with hcard
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
    exact ⟨i, abs_pos.mpr (by intro h; simp [h] at hS)⟩
  · linarith

theorem nonconstant_of_weight_pos {n : ℕ} (f : BooleanFunction n)
    (hW : 0 < fourierWeight (lift f) 1) : ∃ u v, f u ≠ f v := by
  obtain ⟨i, hi⟩ := exists_nonzero_singleton_of_weight_pos f hW
  by_contra h
  push_neg at h
  have hconst : lift f = fun _ : Cube n => sign (f (fun _ => false)) := by
    funext x
    exact congrArg sign (h x (fun _ => false))
  rw [hconst, fourier_const] at hi
  simp at hi

theorem continuousOn_singletonProfile {n : ℕ} (f : BooleanFunction n) :
    ContinuousOn (singletonProfile f) (Ioi (0 : ℝ)) := by
  exact continuousOn_finsetSum Finset.univ
    (fun i _ => continuousOn_profile_of_nonneg (abs_nonneg (fourier (lift f) {i})))

theorem singletonProfile_antitone {n : ℕ} (f : BooleanFunction n) :
    AntitoneOn (singletonProfile f) (Ioi (0 : ℝ)) := by
  intro e he d hd hed
  apply Finset.sum_le_sum
  intro i _
  rcases eq_or_lt_of_le (abs_nonneg (fourier (lift f) {i})) with hq | hq
  · rw [← hq, profile_zero_right, profile_zero_right]
  · exact profile_antitone hq he hd hed

theorem singletonProfile_pos {n : ℕ} (f : BooleanFunction n)
    (hW : 0 < fourierWeight (lift f) 1) (e : ℝ) (he : 0 < e) :
    0 < singletonProfile f e := by
  obtain ⟨i, hi⟩ := exists_nonzero_singleton_of_weight_pos f hW
  have hle : profile e |fourier (lift f) {i}| ≤ singletonProfile f e := by
    unfold singletonProfile
    exact Finset.single_le_sum (fun j _ =>
      profile_nonneg he (abs_nonneg (fourier (lift f) {j}))) (Finset.mem_univ i)
  exact (profile_pos he hi).trans_le hle

theorem continuous_conditionalEntropy {n : ℕ} (f : BooleanFunction n) :
    Continuous (fun ρ => conditionalEntropy ρ f) := by
  have heq : (fun ρ => conditionalEntropy ρ f) =
      fun ρ => Real.binEntropy ((1-mean f)/2)-information ρ f := by
    funext ρ
    rw [information_eq_initial_sub_conditional]
    ring
  rw [heq]
  exact continuous_const.sub (continuous_information f)

theorem conditionalEntropy_one {n : ℕ} (f : BooleanFunction n) : conditionalEntropy 1 f = 0 := by
  unfold conditionalEntropy
  simp only [noise_one, lift]
  have h (x : Cube n) : Real.binEntropy ((1-sign (f x))/2) = 0 := by
    cases hf : f x <;> norm_num [sign]
  simp only [h, avg_const]

theorem conditionalEntropy_nonneg {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1)
    (f : BooleanFunction n) : 0 ≤ conditionalEntropy ρ f := by
  have hdom := noise_mem_Icc (show ρ ∈ Icc (-1 : ℝ) 1 from ⟨by linarith [hρ.1], hρ.2⟩)
    (lift f) (fun x => sign_mem_Icc (f x))
  have h := avg_mono (fun x => (meanEntropy_nonneg (hdom x)))
  change 0 ≤ avg (fun x => meanEntropy (noise ρ (lift f) x))
  simpa only [avg_const] using h

theorem conditionalEntropy_pos {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) : 0 < conditionalEntropy ρ f := by
  have hpos (x : Cube n) : 0 < meanEntropy (noise ρ (lift f) x) :=
    meanEntropy_pos (noise_lift_mem_Ioo ⟨by linarith [hρ.1], hρ.2⟩ f hf x)
  change 0 < (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ x, meanEntropy (noise ρ (lift f) x)
  apply mul_pos (inv_pos.mpr (card_cube_pos n))
  exact Finset.sum_pos' (fun x _ => (hpos x).le) ⟨(fun _ => false), Finset.mem_univ _, hpos _⟩

theorem production_ge_scaled_singletonProfile {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n) (hf : ∃ u v, f u ≠ f v) :
    ρ*singletonProfile f (conditionalEntropy ρ f/ρ) ≤ entropyProduction (noise ρ (lift f)) := by
  have he := conditionalEntropy_pos hρ f hf
  have h := entropyProduction_noise_ge_profile hρ f hf
  simp_rw [profile_scaling he hρ.1 (abs_nonneg _)] at h
  simpa only [singletonProfile, Finset.mul_sum] using h

/-- STOC `thm:profile-clock`, with its actual finite Boolean trajectory
and all regularity/positivity premises proved internally. -/
theorem profile_clock_lower_bound {n : ℕ} {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (f : BooleanFunction n) (hW : 0 < fourierWeight (lift f) 1) :
    -Real.log ρ ≤ clock (singletonProfile f) (conditionalEntropy ρ f/ρ) := by
  have hf := nonconstant_of_weight_pos f hW
  let P := singletonProfile f
  let y := fun r : ℝ => conditionalEntropy r f/r
  let G := fun r : ℝ => clock P (y r)+Real.log r
  have hcP := continuousOn_singletonProfile f
  have haP := singletonProfile_antitone f
  have hpP := singletonProfile_pos f hW
  have hycont : ContinuousOn y (Icc ρ 1) :=
    (continuous_conditionalEntropy f).continuousOn.div continuousOn_id
      (fun r hr => ne_of_gt (lt_of_lt_of_le hρ.1 hr.1))
  have hyrange : MapsTo y (Icc ρ 1) (Ici (0 : ℝ)) := by
    intro r hr
    exact div_nonneg (conditionalEntropy_nonneg ⟨hρ.1.le.trans hr.1, hr.2⟩ f)
      (hρ.1.le.trans hr.1)
  have hGc : ContinuousOn G (Icc ρ 1) :=
    ((continuousOn_clock hcP haP hpP).comp hycont hyrange).add
      (Real.continuousOn_log.mono (fun r hr => ne_of_gt (lt_of_lt_of_le hρ.1 hr.1)))
  have hGd (r : ℝ) (hr : r ∈ Ioo ρ 1) :
      HasDerivAt G
        (((-entropyProduction (noise r (lift f))-conditionalEntropy r f)/r^2)/
          (y r+P (y r))+1/r) r := by
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hρ.1.trans hr.1, hr.2⟩
    have hr0 := ne_of_gt hr01.1
    have hyr : 0 < y r := div_pos (conditionalEntropy_pos hr01 f hf) hr01.1
    have hyderiv : HasDerivAt y
        ((-entropyProduction (noise r (lift f))-conditionalEntropy r f)/r^2) r := by
      have h := (hasDerivAt_conditionalEntropy hr01 f hf).div (hasDerivAt_id r) hr0
      apply h.congr_deriv
      dsimp only [id_eq]
      field_simp
    have h := ((hasDerivAt_clock hcP haP hpP hyr).comp r hyderiv).add (Real.hasDerivAt_log hr0)
    apply h.congr_deriv
    simp only [one_div]
    ring
  have hm : AntitoneOn G (Icc ρ 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc ρ 1) hGc
    · intro r hr
      exact (hGd r (by simpa only [interior_Icc] using hr)).hasDerivWithinAt
    · intro r hr
      have hr' : r ∈ Ioo ρ 1 := by simpa only [interior_Icc] using hr
      have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hρ.1.trans hr'.1, hr'.2⟩
      have hyr : 0 < y r := div_pos (conditionalEntropy_pos hr01 f hf) hr01.1
      have hden : 0 < y r+P (y r) := add_pos hyr (hpP _ hyr)
      have hp := production_ge_scaled_singletonProfile hr01 f hf
      have hle : ((-entropyProduction (noise r (lift f))-conditionalEntropy r f)/r^2)/
          (y r+P (y r)) ≤ -(1/r) := by
        apply (div_le_iff₀ hden).2
        apply (div_le_iff₀ (sq_pos_of_pos hr01.1)).2
        have heq : (-(1/r))*(y r+P (y r))*r^2 =
            -conditionalEntropy r f-r*P (y r) := by
          dsimp only [y]
          field_simp [ne_of_gt hr01.1]
          ring
        rw [heq]
        linarith only [hp]
      linarith only [hle]
  have h := hm ⟨le_rfl, hρ.2.le⟩ ⟨hρ.2.le, le_rfl⟩ hρ.2.le
  have hy1 : y 1 = 0 := by simp [y, conditionalEntropy_one]
  change clock P (y 1)+Real.log 1 ≤ clock P (y ρ)+Real.log ρ at h
  rw [hy1, clock_zero, Real.log_one] at h
  change -Real.log ρ ≤ clock P (y ρ)
  linarith only [h]

end
end CK.Profile
