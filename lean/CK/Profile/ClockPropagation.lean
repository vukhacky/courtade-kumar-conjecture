module

public import CK.Profile.DictatorClock
public import CK.Profile.Fixed
public import CK.Profile.ClockComparison

/-! Fixed-clock propagation to higher correlation, with an envelope independent of correlation. -/

@[expose] public section
set_option autoImplicit false
open Set MeasureTheory
namespace CK.Profile
noncomputable section

theorem clock_le_clock_of_envelope {P Q : ℝ → ℝ}
    (hcP : ContinuousOn P (Ioi (0 : ℝ))) (haP : AntitoneOn P (Ioi (0 : ℝ)))
    (hpP : ∀ e, 0 < e → 0 < P e)
    (hcQ : ContinuousOn Q (Ioi (0 : ℝ))) (haQ : AntitoneOn Q (Ioi (0 : ℝ)))
    (hpQ : ∀ e, 0 < e → 0 < Q e)
    (hQP : ∀ e, 0 < e → Q e ≤ P e) {y : ℝ} (hy : 0 ≤ y) :
    clock P y ≤ clock Q y := by
  obtain rfl | hy := hy.eq_or_lt
  · simp
  apply intervalIntegral.integral_mono_on_of_le_Ioo hy.le
    (clock_integrable hcP haP hpP hy) (clock_integrable hcQ haQ hpQ hy)
  intro e he
  exact one_div_le_one_div_of_le (add_pos he.1 (hpQ e he.1))
    (by linarith only [hQP e he.1])

/-- A single-crossing argument for clocks. The ratio hypothesis is proved
for fixed profile sums in `Fixed.lean`. -/
theorem clock_comparison_propagates {P Q : ℝ → ℝ}
    (hcP : ContinuousOn P (Ioi (0 : ℝ))) (haP : AntitoneOn P (Ioi (0 : ℝ)))
    (hpP : ∀ e, 0 < e → 0 < P e)
    (hcQ : ContinuousOn Q (Ioi (0 : ℝ))) (haQ : AntitoneOn Q (Ioi (0 : ℝ)))
    (hpQ : ∀ e, 0 < e → 0 < Q e)
    (hRatio : AntitoneOn (fun e => Q e/P e) (Ioi (0 : ℝ)))
    {Y y : ℝ} (hY : 0 < Y) (hy : 0 ≤ y) (hyY : y ≤ Y)
    (hYcmp : clock Q Y ≤ clock P Y) : clock Q y ≤ clock P y := by
  obtain rfl | hy := hy.eq_or_lt
  · simp
  let D := fun e => clock Q e-clock P e
  have hc : ContinuousOn D (Icc (0 : ℝ) Y) :=
    (continuousOn_clock_interval hcQ haQ hpQ hY).sub
      (continuousOn_clock_interval hcP haP hpP hY)
  have hd (e : ℝ) (he : 0 < e) :
      HasDerivAt D (1/(e+Q e)-1/(e+P e)) e :=
    (hasDerivAt_clock hcQ haQ hpQ he).sub (hasDerivAt_clock hcP haP hpP he)
  by_cases hside : P y ≤ Q y
  · have horder (e : ℝ) (he : e ∈ Ioo (0 : ℝ) y) : P e ≤ Q e := by
      have hr := hRatio he.1 hy he.2.le
      have hyR : 1 ≤ Q y/P y := (le_div_iff₀ (hpP y hy)).2 (by simpa using hside)
      have heR : 1 ≤ Q e/P e := hyR.trans hr
      simpa using (le_div_iff₀ (hpP e he.1)).mp heR
    have ha : AntitoneOn D (Icc (0 : ℝ) y) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 y)
        (hc.mono (Icc_subset_Icc_right hyY))
      · intro e he
        have he' : e ∈ Ioo (0 : ℝ) y := by simpa only [interior_Icc] using he
        exact (hd e he'.1).hasDerivWithinAt
      · intro e he
        have he' : e ∈ Ioo (0 : ℝ) y := by simpa only [interior_Icc] using he
        exact sub_nonpos.mpr (one_div_le_one_div_of_le (add_pos he'.1 (hpP e he'.1))
          (by linarith only [horder e he']))
    have h := ha ⟨le_rfl, hy.le⟩ ⟨hy.le, le_rfl⟩ hy.le
    simpa only [D, clock_zero, sub_self, sub_nonpos] using h
  · have hside' : Q y ≤ P y := (lt_of_not_ge hside).le
    have horder (e : ℝ) (he : e ∈ Ioo y Y) : Q e ≤ P e := by
      have he0 := hy.trans he.1
      have hr := hRatio hy he0 he.1.le
      have hyR : Q y/P y ≤ 1 := (div_le_one (hpP y hy)).2 hside'
      have heR : Q e/P e ≤ 1 := hr.trans hyR
      exact (div_le_one (hpP e he0)).mp heR
    have hm : MonotoneOn D (Icc y Y) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc y Y)
        (hc.mono (Icc_subset_Icc_left hy.le))
      · intro e he
        have he' : e ∈ Ioo y Y := by simpa only [interior_Icc] using he
        exact (hd e (hy.trans he'.1)).hasDerivWithinAt
      · intro e he
        have he' : e ∈ Ioo y Y := by simpa only [interior_Icc] using he
        have he0 := hy.trans he'.1
        exact sub_nonneg.mpr (one_div_le_one_div_of_le (add_pos he0 (hpQ e he0))
          (by linarith only [horder e he']))
    have h := hm ⟨le_rfl, hyY⟩ ⟨hyY, le_rfl⟩ hyY
    dsimp only [D] at h
    linarith only [h, hYcmp]

theorem fixed_profile_clock_propagates {ι : Type*} [Fintype ι] (w q : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1)
    (hpos : ∃ i, 0 < w i ∧ 0 < q i)
    {ρ₀ ρ : ℝ} (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) (hρ : ρ ∈ Ico ρ₀ 1)
    (hbase : clock (sumProfile w q) (meanEntropy ρ₀/ρ₀) ≤ -Real.log ρ₀) :
    clock (sumProfile w q) (meanEntropy ρ/ρ) ≤ -Real.log ρ := by
  have hρ01 : ρ ∈ Ioo (0 : ℝ) 1 := ⟨hρ₀.1.trans_le hρ.1, hρ.2⟩
  have hy0 := div_pos (meanEntropy_pos ⟨by linarith [hρ₀.1], hρ₀.2⟩) hρ₀.1
  have hy := div_pos (meanEntropy_pos ⟨by linarith [hρ01.1], hρ01.2⟩) hρ01.1
  have hyy := entropy_ratio_strictAnti.antitoneOn hρ₀ hρ01 hρ.1
  have h := clock_comparison_propagates
    (P := fun e => profile e 1) (Q := sumProfile w q)
    (continuousOn_profile (by norm_num)) (profile_antitone (by norm_num))
    (fun _ he => profile_pos he (by norm_num))
    (continuousOn_sumProfile w q (fun i => (hq i).1))
    (sumProfile_antitone w q hw (fun i => (hq i).1))
    (fun _ he => sumProfile_pos w q hw (fun i => (hq i).1) hpos he)
    (sumProfile_ratio_antitone w q hw hq) hy0 hy.le hyy
    (by simpa only [dictator_clock hρ₀] using hbase)
  simpa only [dictator_clock hρ01] using h

/-- Shannon mutual information bound from a fixed-envelope clock at the current correlation. -/
theorem mutualInformation_le_phi_of_profile_clock {n : ℕ} {ρ : ℝ}
    (hρ : ρ ∈ Ioo (0 : ℝ) 1) (f : BooleanFunction n)
    (hW : 0 < fourierWeight (lift f) 1) (Q : ℝ → ℝ)
    (hcQ : ContinuousOn Q (Ioi (0 : ℝ))) (haQ : AntitoneOn Q (Ioi (0 : ℝ)))
    (hpQ : ∀ e, 0 < e → 0 < Q e)
    (hQP : ∀ e, 0 < e → Q e ≤ singletonProfile f e)
    (hclock : clock Q (meanEntropy ρ/ρ) ≤ -Real.log ρ) :
    mutualInformation ρ f ≤ phi ρ := by
  have he := conditionalEntropy_pos hρ f (nonconstant_of_weight_pos f hW)
  have hactual := profile_clock_lower_bound hρ f hW
  have hcmp := clock_le_clock_of_envelope (continuousOn_singletonProfile f)
    (singletonProfile_antitone f) (singletonProfile_pos f hW)
    hcQ haQ hpQ hQP (div_pos he hρ.1).le
  have hE : meanEntropy ρ ≤ conditionalEntropy ρ f := by
    by_contra h
    have hlt : conditionalEntropy ρ f/ρ < meanEntropy ρ/ρ :=
      div_lt_div_of_pos_right (lt_of_not_ge h) hρ.1
    have hH := meanEntropy_pos ⟨by linarith [hρ.1], hρ.2⟩
    have hs := strictMonoOn_clock hcQ haQ hpQ (div_pos he hρ.1).le
      (div_pos hH hρ.1).le hlt
    linarith only [hactual, hcmp, hclock, hs]
  rw [mutualInformation_eq_information ⟨hρ.1.le, hρ.2.le⟩,
    information_eq_initial_sub_conditional]
  change Real.binEntropy ((1-mean f)/2)-conditionalEntropy ρ f ≤ Real.log 2-meanEntropy ρ
  linarith only [hE, Real.binEntropy_le_log_two (p := (1-mean f)/2)]

end
end CK.Profile
