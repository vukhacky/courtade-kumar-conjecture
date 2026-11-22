module

public import CK.Profile.Weighted
public import CK.Profile.Ratio

/-! Fixed finite envelopes, with zero weights and zero arguments included. -/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators
open Set
namespace CK.Profile
noncomputable section

def sumProfile {ι : Type*} [Fintype ι] (w q : ι → ℝ) (e : ℝ) : ℝ :=
  ∑ i, w i*profile e (q i)

theorem continuousOn_sumProfile {ι : Type*} [Fintype ι] (w q : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) : ContinuousOn (sumProfile w q) (Ioi (0 : ℝ)) := by
  exact continuousOn_finsetSum Finset.univ (fun i _ =>
    continuousOn_const.mul (continuousOn_profile_of_nonneg (hq i)))

theorem sumProfile_nonneg {ι : Type*} [Fintype ι] (w q : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 ≤ q i) {e : ℝ} (he : 0 < e) :
    0 ≤ sumProfile w q e := by
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (profile_nonneg he (hq i)))

theorem sumProfile_pos {ι : Type*} [Fintype ι] (w q : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 ≤ q i)
    (hpos : ∃ i, 0 < w i ∧ 0 < q i) {e : ℝ} (he : 0 < e) :
    0 < sumProfile w q e := by
  obtain ⟨i, hi, hqi⟩ := hpos
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j) (profile_nonneg he (hq j)))
    ⟨i, Finset.mem_univ i, mul_pos hi (profile_pos he hqi)⟩

theorem sumProfile_antitone {ι : Type*} [Fintype ι] (w q : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, 0 ≤ q i) :
    AntitoneOn (sumProfile w q) (Ioi (0 : ℝ)) := by
  intro e he d hd hed
  apply Finset.sum_le_sum
  intro i _
  obtain hi | hi := (hq i).eq_or_lt
  · simp [← hi]
  · exact mul_le_mul_of_nonneg_left (profile_antitone hi he hd hed) (hw i)

theorem sumProfile_ratio_antitone {ι : Type*} [Fintype ι] (w q : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) :
    AntitoneOn (fun e => sumProfile w q e/profile e 1) (Ioi (0 : ℝ)) := by
  intro e he d hd hed
  dsimp only [sumProfile]
  rw [Finset.sum_div, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  obtain hi | hi := (hq i).1.eq_or_lt
  · simp [← hi]
  · simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left
      (profile_ratio_antitone hi (hq i).2 he hd hed) (hw i)

end
end CK.Profile
